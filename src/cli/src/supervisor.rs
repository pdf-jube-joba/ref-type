//! Keep the terminal and cancellation alive while bounded workers check a snapshot.
use crate::{Args, progress, report};
use anyhow::{Context, bail};
use sema::{ModuleProgress, ProgressEvent, ProgressPlan, SourceSnapshot};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    fs::{self, File},
    io::{BufRead, BufReader, Read, Seek, SeekFrom, Write},
    os::{
        fd::{AsRawFd, FromRawFd, OwnedFd},
        unix::process::{CommandExt, ExitStatusExt},
    },
    path::{Path, PathBuf},
    process::{Child, Command, ExitStatus, Stdio},
    sync::atomic::{AtomicI32, AtomicU64, Ordering},
    thread,
    time::{Duration, Instant},
};

static SIGNAL: AtomicI32 = AtomicI32::new(0);
fn worker_executable() -> std::io::Result<PathBuf> {
    // Keep using this supervisor's executable when a rebuild replaces its
    // directory entry. current_exe() can then name an unlinked file on Linux.
    #[cfg(target_os = "linux")]
    {
        Ok(PathBuf::from("/proc/self/exe"))
    }
    #[cfg(not(target_os = "linux"))]
    {
        std::env::current_exe()
    }
}
extern "C" fn cancel(signal: libc::c_int) {
    SIGNAL.store(signal, Ordering::Relaxed);
}
pub fn interrupted() -> bool {
    SIGNAL.load(Ordering::Relaxed) != 0
}

struct Signals(Vec<(libc::c_int, libc::sigaction)>);
impl Signals {
    fn install() -> std::io::Result<Self> {
        SIGNAL.store(0, Ordering::Relaxed);
        let mut saved = Self(Vec::new());
        for signal in [libc::SIGINT, libc::SIGTERM, libc::SIGHUP] {
            // SAFETY: sigaction structs are initialized and the handler only stores an atomic.
            unsafe {
                let mut action: libc::sigaction = std::mem::zeroed();
                let mut old: libc::sigaction = std::mem::zeroed();
                action.sa_sigaction = cancel as *const () as usize;
                libc::sigemptyset(&mut action.sa_mask);
                if libc::sigaction(signal, &action, &mut old) != 0 {
                    return Err(std::io::Error::last_os_error());
                }
                saved.0.push((signal, old));
            }
        }
        Ok(saved)
    }
}
impl Drop for Signals {
    fn drop(&mut self) {
        for (signal, action) in &self.0 {
            // SAFETY: restore the dispositions saved by install.
            unsafe {
                libc::sigaction(*signal, action, std::ptr::null_mut());
            }
        }
    }
}

#[derive(Serialize, Deserialize)]
enum Message {
    Event(ProgressEvent, Duration),
    Timing(ModuleProgress),
    Output(sema::QueryOutput),
}
thread_local! {
    static EVENTS: RefCell<Option<File>> = const { RefCell::new(None) };
}
fn send(message: Message) {
    EVENTS.with_borrow_mut(|file| {
        if let Some(file) = file {
            // A broken supervisor channel must not turn a check into apparent success.
            // Publish each complete record in one write. Streaming JSON directly
            // to File issues a syscall for every token in a dependency plan.
            let mut record = serde_json::to_vec(&message).expect("serialize worker event");
            record.push(b'\n');
            file.write_all(&record).expect("write worker event");
        }
    });
}
pub fn send_event(event: &ProgressEvent) {
    let elapsed = match event {
        ProgressEvent::ModuleFinished { path, .. } => sema::timing::elapsed(path),
        _ => Duration::ZERO,
    };
    send(Message::Event(event.clone(), elapsed));
}
pub fn send_timing(timing: ModuleProgress) {
    send(Message::Timing(timing));
}
pub fn send_output(output: sema::QueryOutput) {
    send(Message::Output(output));
}

extern "C" fn collect(_: libc::c_int) {
    sema::request_collection();
}

pub fn worker_arguments(args: Args) -> anyhow::Result<Args> {
    let Some(request) = &args.worker else {
        return Ok(args);
    };
    let args: Args = serde_json::from_slice(&fs::read(request)?)?;
    let directory = args.worker.as_ref().context("missing worker directory")?;
    EVENTS.with_borrow_mut(|events| -> std::io::Result<()> {
        *events = Some(File::create(directory.join("events.jsonl"))?);
        Ok(())
    })?;
    // Abort diagnostics are retained, but dumping gigabytes of core is unnecessary.
    let limit = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    // SAFETY: limit points to a live rlimit; nice changes only this worker's priority.
    unsafe {
        libc::setrlimit(libc::RLIMIT_CORE, &limit);
        libc::nice(5);
        let mut action: libc::sigaction = std::mem::zeroed();
        action.sa_sigaction = collect as *const () as usize;
        libc::sigemptyset(&mut action.sa_mask);
        if libc::sigaction(libc::SIGUSR1, &action, std::ptr::null_mut()) != 0 {
            return Err(std::io::Error::last_os_error().into());
        }
    }
    Ok(args)
}
pub fn read_snapshot(directory: &Path) -> anyhow::Result<SourceSnapshot> {
    // Slice decoding can scan source strings directly instead of pulling each
    // escaped byte through serde_json's generic reader interface.
    Ok(serde_json::from_slice(&fs::read(
        directory.join("snapshot.json"),
    )?)?)
}

struct Workspace {
    directory: PathBuf,
}
impl Workspace {
    fn new(cache: &Path) -> anyhow::Result<Self> {
        fs::create_dir_all(cache)?;
        static NEXT: AtomicU64 = AtomicU64::new(0);
        loop {
            let directory = cache.join(format!(
                ".check-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            match fs::create_dir(&directory) {
                Ok(()) => return Ok(Self { directory }),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(e.into()),
            }
        }
    }
    fn path(&self, name: &str) -> PathBuf {
        self.directory.join(name)
    }
    fn publish(
        &self,
        destination: &Path,
        budget: u64,
    ) -> anyhow::Result<sema::artifact_store::CacheStoreStats> {
        let directory = self.path("cache");
        if !directory.exists() {
            return Ok(Default::default());
        }
        let store = sema::artifact_store::ArtifactStore::new(destination);
        store.set_budget(budget);
        store.publish_from(directory)?;
        Ok(store.stats())
    }
}
impl Drop for Workspace {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}

/// Own the child until it is reaped, including errors and Ctrl+C.
struct Worker {
    child: Child,
    reaped: bool,
}
impl Worker {
    fn signal_kill(&mut self) {
        if self.reaped {
            return;
        }
        // SAFETY: the child owns its process group; ESRCH means it already exited.
        unsafe {
            libc::kill(-(self.child.id() as i32), libc::SIGKILL);
        }
        let _ = self.child.kill();
    }
    fn kill(&mut self) {
        if self.reaped {
            return;
        }
        self.signal_kill();
        let _ = self.child.wait();
        self.reaped = true;
    }
}
impl Drop for Worker {
    fn drop(&mut self) {
        self.kill();
    }
}

struct Events {
    reader: BufReader<File>,
    pending: Vec<u8>,
    timings: Vec<ModuleProgress>,
    outputs: Vec<sema::QueryOutput>,
    checkpoint: Option<usize>,
    completed: BTreeSet<usize>,
    repeated: u64,
    storage: sema::artifact_store::CacheStoreStats,
    session: sema::SessionStatistics,
    last_module: Option<Vec<String>>,
}
impl Events {
    fn new(path: &Path) -> anyhow::Result<Self> {
        File::create(path)?;
        Ok(Self {
            reader: BufReader::new(File::open(path)?),
            pending: Vec::new(),
            timings: Vec::new(),
            outputs: Vec::new(),
            checkpoint: None,
            completed: BTreeSet::new(),
            repeated: 0,
            storage: Default::default(),
            session: Default::default(),
            last_module: None,
        })
    }
    fn poll(&mut self, plan: &mut ProgressPlan) -> anyhow::Result<()> {
        loop {
            let size = self.reader.read_until(b'\n', &mut self.pending)?;
            if size == 0 {
                break;
            }
            if self.pending.last() != Some(&b'\n') {
                break;
            }
            let message: Message = serde_json::from_slice(&self.pending)?;
            self.pending.clear();
            match message {
                Message::Event(ProgressEvent::Planned(next), _) => {
                    let mut packages: BTreeSet<_> = plan.packages.iter().cloned().collect();
                    plan.packages.extend(
                        next.packages
                            .into_iter()
                            .filter(|p| packages.insert(p.clone())),
                    );
                    let mut known: BTreeSet<_> =
                        plan.modules.iter().map(|m| m.path.clone()).collect();
                    plan.modules.extend(
                        next.modules
                            .into_iter()
                            .filter(|m| known.insert(m.path.clone())),
                    );
                    progress::receive(&ProgressEvent::Planned(plan.clone()));
                }
                Message::Event(ProgressEvent::Finished { .. }, _) => {}
                Message::Event(ProgressEvent::DeclarationFinished { position, success }, _) => {
                    if success && !self.completed.insert(position) {
                        self.repeated += 1;
                    }
                }
                Message::Event(event @ ProgressEvent::CheckpointSaved { steps }, elapsed) => {
                    self.checkpoint = Some(steps);
                    progress::receive_timed(&event, elapsed);
                }
                Message::Event(ProgressEvent::StorageStats(stats), _) => self.storage = *stats,
                Message::Event(ProgressEvent::SessionStatistics(stats), _) => self.session = *stats,
                Message::Event(event @ ProgressEvent::ModuleStarted(_), elapsed) => {
                    let ProgressEvent::ModuleStarted(path) = &event else {
                        unreachable!()
                    };
                    self.last_module = Some(path.clone());
                    progress::receive_timed(&event, elapsed);
                }
                Message::Event(event, elapsed) => progress::receive_timed(&event, elapsed),
                Message::Timing(timing) => self.timings.push(timing),
                Message::Output(output) => self.outputs.push(output),
            }
        }
        Ok(())
    }
}

struct Outcome {
    status: ExitStatus,
    limited: bool,
    memory_limited: bool,
    timeout_hit: bool,
    cancelled: bool,
    events: Events,
    resources: report::Execution,
}
fn execute(
    mut command: Command,
    workspace: &Workspace,
    timeout: Option<Duration>,
    plan: &mut ProgressPlan,
    display: &progress::Display,
    quiet: bool,
    memory_mib: u64,
) -> anyhow::Result<Outcome> {
    let mut events = Events::new(&workspace.path("events.jsonl"))?;
    // The allocator's 1 GiB default reservation is substantial under RLIMIT_AS.
    // Smaller arenas leave virtual address space for live graphs and I/O buffers.
    if memory_mib != 0 && std::env::var_os("MIMALLOC_ARENA_RESERVE").is_none() {
        command.env("MIMALLOC_ARENA_RESERVE", "128M");
    }
    if std::env::var_os("REF_TYPE_GRAPH_SPILL_DIR").is_none() {
        command.env("REF_TYPE_GRAPH_SPILL_DIR", &workspace.directory);
    }
    command
        .stdout(Stdio::from(File::create(workspace.path("stdout"))?))
        .stderr(Stdio::from(File::create(workspace.path("stderr"))?))
        .stdin(Stdio::null())
        .process_group(0);
    let parent = std::process::id();
    // SAFETY: only async-signal-safe Linux syscalls run between fork and exec.
    unsafe {
        command.pre_exec(move || {
            let limit = libc::rlimit {
                rlim_cur: 0,
                rlim_max: 0,
            };
            if libc::setrlimit(libc::RLIMIT_CORE, &limit) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            if libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            if libc::getppid() != parent as i32 {
                libc::_exit(130);
            }
            Ok(())
        });
    }
    let mut worker = Worker {
        child: command.spawn()?,
        reaped: false,
    };
    // A pidfd wakes poll as soon as the child exits, while the timeout retains
    // periodic progress/cancellation checks. Older kernels keep timed polling.
    // SAFETY: pidfd_open takes a live child PID and returns a new owned fd.
    let exit_fd = unsafe { libc::syscall(libc::SYS_pidfd_open, worker.child.id(), 0) };
    let exit_fd = (exit_fd >= 0).then(|| {
        // SAFETY: the successful syscall returned a fresh, uniquely owned fd.
        unsafe { OwnedFd::from_raw_fd(exit_fd as i32) }
    });
    let started = Instant::now();
    let mut heartbeat = Instant::now();
    let mut last_pressure = started
        .checked_sub(Duration::from_secs(5))
        .unwrap_or(started);
    let mut resources = report::Execution::default();
    let mut cancelled = false;
    let mut timeout_hit = false;
    let status = loop {
        events.poll(plan)?;
        if interrupted() && !cancelled {
            cancelled = true;
            worker.signal_kill();
        }
        // wait4 also returns the final peak RSS and CPU usage of this worker.
        let mut status = 0;
        let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
        // SAFETY: status and usage are live writable records; this worker owns PID.
        let reaped = unsafe {
            libc::wait4(
                worker.child.id() as i32,
                &mut status,
                libc::WNOHANG,
                &mut usage,
            )
        };
        if reaped > 0 {
            worker.reaped = true;
            resources.peak_rss_kib = resources.peak_rss_kib.max(usage.ru_maxrss as u64);
            resources.cpu_micros = (usage.ru_utime.tv_sec + usage.ru_stime.tv_sec) as u64
                * 1_000_000
                + (usage.ru_utime.tv_usec + usage.ru_stime.tv_usec) as u64;
            break ExitStatus::from_raw(status);
        }
        if reaped < 0 {
            return Err(std::io::Error::last_os_error().into());
        }
        if let Ok(status) = fs::read_to_string(format!("/proc/{}/status", worker.child.id())) {
            let kib = |label: &str| {
                status
                    .lines()
                    .find_map(|line| line.strip_prefix(label))
                    .and_then(|value| value.split_whitespace().next()?.parse::<u64>().ok())
                    .unwrap_or(0)
            };
            let virtual_kib = kib("VmSize:");
            resources.peak_virtual_kib = resources.peak_virtual_kib.max(kib("VmPeak:"));
            resources.peak_rss_kib = resources.peak_rss_kib.max(kib("VmHWM:"));
            if memory_mib != 0
                && virtual_kib > memory_mib.saturating_mul(1024) * 4 / 5
                && last_pressure.elapsed() >= Duration::from_secs(5)
            {
                // SAFETY: signal only the live child; its handler sets an atomic.
                unsafe {
                    libc::kill(worker.child.id() as i32, libc::SIGUSR1);
                }
                last_pressure = Instant::now();
                resources.collection_requests += 1;
            }
        }
        if !timeout_hit && timeout.is_some_and(|limit| started.elapsed() >= limit) {
            timeout_hit = true;
            worker.signal_kill();
        }
        if !quiet && !display.enabled() && heartbeat.elapsed() >= Duration::from_secs(30) {
            display.message(&format!(
                "checking ({:.0}s)",
                started.elapsed().as_secs_f64()
            ));
            heartbeat = Instant::now();
        }
        if let Some(exit_fd) = &exit_fd {
            let mut descriptor = libc::pollfd {
                fd: exit_fd.as_raw_fd(),
                events: libc::POLLIN,
                revents: 0,
            };
            // SAFETY: descriptor is valid for one entry; OwnedFd keeps it open.
            unsafe { libc::poll(&mut descriptor, 1, 50) };
        } else {
            thread::sleep(Duration::from_millis(50));
        }
    };
    events.poll(plan)?;
    resources.last_module = events.last_module.clone();
    resources.last_checkpoint = events.checkpoint.unwrap_or(0);
    let mut stderr = File::open(workspace.path("stderr"))?;
    let size = stderr.metadata()?.len();
    stderr.seek(SeekFrom::Start(size.saturating_sub(8192)))?;
    let mut tail = Vec::new();
    stderr.read_to_end(&mut tail)?;
    // The bounded suffix can start inside a UTF-8 diagnostic character.
    let tail = String::from_utf8_lossy(&tail);
    let memory_limited = !timeout_hit
        && !cancelled
        && (status.signal() == Some(libc::SIGKILL)
            || (status.signal() == Some(libc::SIGABRT) && tail.contains("memory allocation of")));
    let limited = timeout_hit || memory_limited;
    Ok(Outcome {
        status,
        limited,
        memory_limited,
        timeout_hit,
        cancelled,
        events,
        resources,
    })
}

fn snapshot_key(snapshot: &SourceSnapshot) -> Vec<u8> {
    let mut digest = Sha256::new();
    // Include alias identities: retargeting two symlinks can preserve the exact
    // file set while changing which nominal package each import resolves to.
    for (path, identity) in snapshot.source_identities() {
        digest.update([0]);
        for path in [path, identity] {
            let bytes = path.as_os_str().as_encoded_bytes();
            digest.update((bytes.len() as u64).to_le_bytes());
            digest.update(bytes);
        }
    }
    for (path, source) in snapshot.files() {
        digest.update([1]);
        let bytes = path.as_os_str().as_encoded_bytes();
        digest.update((bytes.len() as u64).to_le_bytes());
        digest.update(bytes);
        digest.update((source.text.len() as u64).to_le_bytes());
        digest.update(source.text.as_bytes());
    }
    digest.finalize().to_vec()
}

pub fn run(args: &Args, display: &mut progress::Display) -> anyhow::Result<report::Report> {
    let _signals = Signals::install()?;
    let cache = crate::cache_directory(args)?;
    if args.clear_cache {
        crate::clear_cache_directory(&cache)?;
    }
    let mut database = sema::Database::new();
    let snapshot = match crate::input_snapshot(args, &mut database) {
        Ok(snapshot) => snapshot,
        Err(error) => {
            eprintln!("Module Load Error: {error}");
            return Ok(report::Report::checked(false, false));
        }
    };
    crate::save_input_snapshot(args, &snapshot)?;
    let workspace = Workspace::new(&cache)?;
    let paths = if args.module.is_some() {
        match database.module_paths(&snapshot) {
            Ok(paths) => paths,
            Err(diagnostics) => {
                display.finish(false);
                for diagnostic in diagnostics {
                    eprintln!("{}", diagnostic.render(&snapshot));
                }
                return Ok(report::Report::checked(false, false));
            }
        }
    } else {
        Vec::new()
    };
    let module = args
        .module
        .as_ref()
        .map(|name| name.split('.').map(str::to_owned).collect::<Vec<_>>());
    if module.as_ref().is_some_and(|p| !paths.contains(p)) {
        eprintln!(
            "Module Selection Error: module '{}' was not found",
            args.module.as_ref().unwrap()
        );
        return Ok(report::Report::checked(false, false));
    }
    let mut plan = ProgressPlan {
        packages: paths
            .iter()
            .filter(|p| p.len() == 1)
            .map(|p| p[0].clone())
            .collect(),
        modules: paths
            .iter()
            .filter(|p| {
                module
                    .as_ref()
                    .is_none_or(|m| *p == m || (!args.module_only && p.starts_with(m)))
            })
            .map(|p| sema::ProgressModule {
                path: p.clone(),
                dependencies: vec![],
            })
            .collect(),
    };
    progress::receive(&ProgressEvent::Planned(plan.clone()));
    let initial_key = snapshot_key(&snapshot);
    serde_json::to_writer(
        std::io::BufWriter::new(File::create(workspace.path("snapshot.json"))?),
        &snapshot,
    )?;
    // The snapshot on disk also supports lazy scope enumeration after a limit.
    drop(snapshot);
    drop(database);
    let fresh = args.full_check || args.no_cache || args.trace;
    let worker_cache = if fresh {
        workspace.path("cache")
    } else {
        cache.clone()
    };
    let session_store = sema::artifact_store::ArtifactStore::new(&worker_cache);
    if let Some(budget) = args.cache_budget_mib {
        session_store.set_budget(budget.saturating_mul(1024 * 1024));
    }
    let session_token = session_store.session_token()?;
    let label = module
        .as_ref()
        .map_or_else(|| "project".to_owned(), |path| path.join("."));
    let started = Instant::now();
    let mut last_checkpoint = 0;
    let mut workers = 0u64;
    let mut resources = report::Execution::default();
    let mut timings: BTreeMap<Vec<String>, ModuleProgress> = BTreeMap::new();
    let mut outputs = BTreeSet::new();
    let mut success = true;
    let mut internal_error = false;
    let mut incomplete = None;
    let mut verification_reused = false;
    let mut checking = sema::QueryStats::default();
    let mut storage = sema::artifact_store::CacheStoreStats::default();
    let mut completed = BTreeSet::new();
    loop {
        if interrupted() {
            bail!("検査を中断しました");
        }
        workers += 1;
        let mut request = args.clone();
        request.worker = Some(workspace.directory.clone());
        request.worker_progress = display.enabled();
        request.full_check = false;
        request.no_cache = args.no_cache;
        request.clear_cache = false;
        request.progress_tty = false;
        request.cache_dir = Some(worker_cache.clone());
        request.report_json = Some(workspace.path("report.json"));
        if workspace.path("report.json").exists() {
            fs::remove_file(workspace.path("report.json"))?;
        }
        fs::write(
            workspace.path("request.json"),
            serde_json::to_vec(&request)?,
        )?;
        let mut command = Command::new(worker_executable()?);
        command
            .arg(&args.path)
            .arg("--worker")
            .arg(workspace.path("request.json"))
            .env_remove("REF_TYPE_PROFILE_PROGRESS")
            .env("REF_TYPE_CACHE_SESSION", &session_token);
        if !args.no_progress {
            display.message(&format!("checking {label}"));
        }
        let outcome = execute(
            command,
            &workspace,
            args.time_limit_seconds
                .map(|limit| Duration::from_secs(limit).saturating_sub(started.elapsed())),
            &mut plan,
            display,
            args.no_progress,
            args.memory_mib.unwrap_or(3072),
        );
        let outcome = match outcome {
            Ok(outcome) => outcome,
            Err(error) => {
                if fresh
                    && !args.no_cache
                    && let Err(save) = workspace.publish(
                        &cache,
                        args.cache_budget_mib
                            .map_or(u64::MAX, |budget| budget.saturating_mul(1024 * 1024)),
                    )
                {
                    eprintln!("中断前の checkpoint の公開に失敗しました: {save:#}");
                }
                return Err(error);
            }
        };
        resources.merge(&outcome.resources);
        resources.duplicate_source_steps += outcome.events.repeated;
        resources.replayed_source_steps +=
            outcome.events.completed.intersection(&completed).count() as u64;
        completed.extend(&outcome.events.completed);
        resources.source_steps = completed.len() as u64;
        if outcome.events.session.completed_steps > 0 {
            checking.session = outcome.events.session.clone();
        }
        if !outcome.status.success()
            && !outcome.cancelled
            && !outcome.timeout_hit
            && !args
                .time_limit_seconds
                .is_some_and(|limit| started.elapsed() >= Duration::from_secs(limit))
            && (outcome.memory_limited || outcome.status.signal().is_some())
            && let Some(checkpoint) = outcome.events.checkpoint
            && checkpoint > last_checkpoint
        {
            resources.lost_steps += outcome.events.completed.range(checkpoint..).count() as u64;
            storage.merge(&outcome.events.storage);
            last_checkpoint = checkpoint;
            display.message(&format!("検査を checkpoint {checkpoint} から再開します。"));
            continue;
        }
        if !outcome.status.success() {
            success = false;
            if outcome.cancelled {
                incomplete = Some(report::Outcome::Interrupted);
                display.message("検査を中断しました。");
            } else if outcome.timeout_hit {
                incomplete = Some(report::Outcome::TimeLimit);
                display.message("指定された総時間制限に達しました。検査は未完了です。");
            } else if outcome.limited {
                incomplete = Some(report::Outcome::MemoryLimit);
                display.message("この module と参照先がメモリ上限を超えました。検査は未完了です。");
            } else {
                display.message(&format!("検査失敗: {} ({})", label, outcome.status));
            }
        }
        std::io::copy(
            &mut File::open(workspace.path("stderr"))?,
            &mut std::io::stderr(),
        )?;
        std::io::copy(
            &mut File::open(workspace.path("stdout"))?,
            &mut std::io::stdout(),
        )?;
        let summary = match fs::read(workspace.path("report.json")) {
            Ok(bytes) => serde_json::from_slice::<report::Report>(&bytes)?,
            Err(_) if !outcome.status.success() => {
                // An aborted worker cannot write its final report. Still publish
                // the verified prefixes below so a retry can use completed work.
                internal_error = incomplete.is_none();
                resources.lost_steps += outcome
                    .events
                    .completed
                    .range(outcome.events.checkpoint.unwrap_or(0)..)
                    .count() as u64;
                storage.merge(&outcome.events.storage);
                break;
            }
            Err(error) => return Err(error).context("worker did not finish its report"),
        };
        if summary.outcome == report::Outcome::InternalError {
            bail!("verification worker failed internally");
        }
        if outcome.status.success() != (summary.outcome == report::Outcome::Accepted) {
            bail!("verification worker status disagrees with its report");
        }
        verification_reused |= !fresh && summary.cache.verification_reused;
        checking = summary.checking;
        storage.merge(&summary.storage);
        for output in outcome.events.outputs {
            if outputs.insert((
                output.location.file,
                output.location.range.start,
                output.location.range.end,
                output.text.clone(),
            )) {
                println!("{}", output.text);
            }
        }
        for timing in outcome.events.timings {
            let entry = timings
                .entry(timing.path.clone())
                .or_insert_with(|| ModuleProgress {
                    elapsed: Duration::ZERO,
                    ..timing.clone()
                });
            entry.elapsed += timing.elapsed;
            if timing.action == sema::ProgressAction::Check {
                entry.action = timing.action;
            }
        }
        break;
    }
    if !interrupted()
        && snapshot_key(&crate::input_snapshot(args, &mut sema::Database::new())?) != initial_key
    {
        if args.source_snapshot.is_some() {
            bail!(
                "検査中に入力 snapshot が変更されました。再実行して現在の snapshot を検査してください。"
            );
        }
        bail!("検査中にソースが変更されました。再実行して現在のソースを検査してください。");
    }
    if fresh && !args.no_cache {
        match workspace.publish(
            &cache,
            args.cache_budget_mib
                .map_or(u64::MAX, |budget| budget.saturating_mul(1024 * 1024)),
        ) {
            Ok(published) => storage.merge(&published),
            Err(error) => {
                storage.save_failures += 1;
                storage.last_save_error = Some(error.to_string());
                eprintln!("キャッシュの公開を省略しました: {error:#}");
            }
        }
    }
    progress::receive(&ProgressEvent::Finished { success });
    crate::PROGRESS.with_borrow_mut(|events| events.extend(timings.into_values()));
    if !args.no_progress {
        display.message(if success {
            "全検査範囲の型検査が完了しました。"
        } else {
            "検査が完了していない範囲があります。"
        });
    }
    let mut report = if internal_error {
        report::Report::internal_error()
    } else {
        report::Report::checked(success, verification_reused)
    };
    if let Some(outcome) = incomplete {
        report.outcome = outcome;
    }
    report.checking = checking;
    report.storage = storage;
    report.execution = resources;
    report.execution.elapsed_micros = started.elapsed().as_micros() as u64;
    report.execution.workers = workers;
    report.execution.recoveries = workers.saturating_sub(1);
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    #[cfg(target_os = "linux")]
    fn worker_binary_survives_unlink() {
        const CHILD: &str = "REF_TYPE_TEST_UNLINKED_WORKER_BINARY";
        if let Some(linked) = std::env::var_os(CHILD) {
            assert_eq!(std::env::current_exe().unwrap(), PathBuf::from(&linked));
            fs::remove_file(&linked).unwrap();
            let output = Command::new(worker_executable().unwrap())
                .arg("--list")
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            return;
        }
        let workspace = Workspace::new(&std::env::temp_dir()).unwrap();
        let linked = workspace.path("worker-executable");
        let executable = std::env::current_exe().unwrap();
        if fs::hard_link(&executable, &linked).is_err() {
            fs::copy(&executable, &linked).unwrap();
        }
        let module = module_path!().split_once("::").unwrap().1;
        let name = format!("{module}::worker_binary_survives_unlink");
        let output = Command::new(&linked)
            .args(["--exact", &name, "--nocapture"])
            .env(CHILD, &linked)
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success(),
            "{stdout}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            stdout.contains("1 passed"),
            "child test did not run: {stdout}"
        );
    }

    #[test]
    fn snapshot_identity_changes_when_import_aliases_are_retargeted() {
        let snapshot = SourceSnapshot::new("/project")
            .with_file("/packages/one/src/root.ref", "\\module Value {}")
            .with_file("/packages/two/src/root.ref", "\\module Value {}");
        let mut value = serde_json::to_value(snapshot).unwrap();
        value["aliases"] = serde_json::json!({
            "/project/left": "/packages/one",
            "/project/right": "/packages/two",
        });
        let before: SourceSnapshot = serde_json::from_value(value.clone()).unwrap();
        value["aliases"] = serde_json::json!({
            "/project/left": "/packages/two",
            "/project/right": "/packages/one",
        });
        let after: SourceSnapshot = serde_json::from_value(value).unwrap();
        assert_eq!(
            before.files().map(|(path, _)| path).collect::<Vec<_>>(),
            after.files().map(|(path, _)| path).collect::<Vec<_>>()
        );
        assert_ne!(snapshot_key(&before), snapshot_key(&after));
        let mut value = serde_json::to_value(&after).unwrap();
        value["aliases"]["/project/cache/objects"] = serde_json::json!("/project/cache/objects");
        let with_cache_directory: SourceSnapshot = serde_json::from_value(value).unwrap();
        assert_eq!(snapshot_key(&after), snapshot_key(&with_cache_directory));
    }

    #[test]
    fn worker_limits_are_distinct_from_type_errors_and_timeouts_reap_children() {
        let workspace = Workspace::new(&std::env::temp_dir()).unwrap();
        let display = progress::Display::new(false, Box::new(std::io::sink()));
        for (script, timeout, limited, signal) in [
            ("echo 'type error' >&2; exit 1", None, false, None),
            (
                "echo 'memory allocation of 1024 bytes failed' >&2; kill -ABRT $$",
                None,
                true,
                Some(libc::SIGABRT),
            ),
            (
                "exec sleep 20",
                Some(Duration::from_millis(150)),
                true,
                Some(libc::SIGKILL),
            ),
        ] {
            let mut command = Command::new("sh");
            command.args(["-c", script]);
            let started = Instant::now();
            let outcome = execute(
                command,
                &workspace,
                timeout,
                &mut ProgressPlan {
                    packages: vec![],
                    modules: vec![],
                },
                &display,
                true,
                0,
            )
            .unwrap();
            assert!(!outcome.status.success());
            assert_eq!(outcome.limited, limited);
            assert_eq!(outcome.status.signal(), signal);
            assert!(started.elapsed() < Duration::from_secs(2));
        }
    }
}
