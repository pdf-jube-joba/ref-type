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
    fn publish(&self, destination: &Path, budget: u64) -> anyhow::Result<()> {
        let directory = self.path("cache");
        if !directory.exists() {
            return Ok(());
        }
        let store = sema::artifact_store::ArtifactStore::new(destination);
        store.set_budget(budget);
        store.publish_from(directory)?;
        Ok(())
    }
}
impl Drop for Workspace {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Batch {
    module: Option<Vec<String>>,
    exact: bool,
}

#[derive(Serialize, Deserialize)]
struct Layout {
    memory_mib: u64,
    batch_seconds: u64,
    splits: BTreeSet<String>,
}
impl Batch {
    fn label(&self) -> String {
        format!(
            "{}{}",
            self.module
                .as_ref()
                .map_or_else(|| "project".into(), |p| p.join(".")),
            if self.exact { " (declarations)" } else { "" }
        )
    }
    fn children(&self, paths: &[Vec<String>]) -> Vec<Self> {
        if self.exact {
            return Vec::new();
        }
        paths
            .iter()
            .filter(|p| match &self.module {
                Some(parent) => p.len() == parent.len() + 1 && p.starts_with(parent),
                None => p.len() == 1,
            })
            .map(|p| Self {
                module: Some(p.clone()),
                exact: false,
            })
            .collect()
    }
    fn split(&self, paths: &[Vec<String>]) -> Vec<Self> {
        let mut children = self.children(paths);
        if !children.is_empty() && self.module.is_some() {
            children.insert(
                0,
                Self {
                    exact: true,
                    ..self.clone()
                },
            );
        }
        children
    }
    fn key(&self) -> String {
        self.module
            .as_ref()
            .map_or_else(String::new, |p| p.join("."))
    }
}

/// Own the child until it is reaped, including errors and Ctrl+C.
struct Worker {
    child: Child,
    reaped: bool,
}
impl Worker {
    fn kill(&mut self) {
        if self.reaped {
            return;
        }
        // SAFETY: the child owns its process group; ESRCH means it already exited.
        unsafe {
            libc::kill(-(self.child.id() as i32), libc::SIGKILL);
        }
        let _ = self.child.kill();
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
}
impl Events {
    fn new(path: &Path) -> anyhow::Result<Self> {
        File::create(path)?;
        Ok(Self {
            reader: BufReader::new(File::open(path)?),
            pending: Vec::new(),
            timings: Vec::new(),
            outputs: Vec::new(),
        })
    }
    fn poll(&mut self, plan: &mut ProgressPlan) -> anyhow::Result<()> {
        loop {
            if interrupted() {
                bail!("検査を中断しました");
            }
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
    events: Events,
}
fn execute(
    mut command: Command,
    workspace: &Workspace,
    timeout: Option<Duration>,
    plan: &mut ProgressPlan,
    display: &progress::Display,
    quiet: bool,
) -> anyhow::Result<Outcome> {
    let mut events = Events::new(&workspace.path("events.jsonl"))?;
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
    let (status, timeout_hit) = loop {
        events.poll(plan)?;
        if interrupted() {
            bail!("検査を中断しました");
        }
        if let Some(status) = worker.child.try_wait()? {
            worker.reaped = true;
            break (status, false);
        }
        if timeout.is_some_and(|limit| started.elapsed() >= limit) {
            worker.kill();
            break (worker.child.wait()?, true);
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
    let mut stderr = File::open(workspace.path("stderr"))?;
    let size = stderr.metadata()?.len();
    stderr.seek(SeekFrom::Start(size.saturating_sub(8192)))?;
    let mut tail = String::new();
    stderr.read_to_string(&mut tail)?;
    let limited = timeout_hit
        || status.signal() == Some(libc::SIGKILL)
        || (status.signal() == Some(libc::SIGABRT) && tail.contains("memory allocation of"));
    Ok(Outcome {
        status,
        limited,
        events,
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
    let cache = match &args.cache_dir {
        Some(path) => path.clone(),
        None => sema::default_cache_directory(&args.path)?,
    };
    if args.clear_cache {
        crate::clear_cache_directory(&cache)?;
    }
    let mut database = sema::Database::new();
    let snapshot = match database.read_snapshot(&args.path, args.full_check_local) {
        Ok(snapshot) => snapshot,
        Err(error) => {
            eprintln!("Module Load Error: {error}");
            return Ok(report::Report::checked(false, false));
        }
    };
    let workspace = Workspace::new(&cache)?;
    let layout_key: String =
        Sha256::digest(args.path.canonicalize()?.as_os_str().as_encoded_bytes())
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
    let layout = if args.no_cache {
        workspace.path("batches.json")
    } else {
        cache.join(format!("{layout_key}.batches.json"))
    };
    let memory_mib = args.memory_mib.unwrap_or(3072);
    let mut splits = fs::read(&layout)
        .ok()
        .and_then(|s| serde_json::from_slice::<Layout>(&s).ok())
        .filter(|saved| saved.memory_mib == memory_mib && saved.batch_seconds == args.batch_seconds)
        .map(|saved| saved.splits)
        .unwrap_or_default();
    // The worker already parses the full snapshot. Only enumerate scopes here
    // when selection or a saved resource-limit split needs them in advance.
    let mut paths = if args.module.is_some() || !splits.is_empty() {
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
    session_store.set_budget(args.cache_budget_mib.saturating_mul(1024 * 1024));
    let session_token = session_store.session_token()?;
    let mut pending = vec![Batch {
        module,
        exact: args.module_only,
    }];
    let mut timings: BTreeMap<Vec<String>, ModuleProgress> = BTreeMap::new();
    let mut outputs = BTreeSet::new();
    let mut success = true;
    let mut verification_reused = false;
    // A successful uncached batch needs no portable artifacts. If it exceeds
    // a resource limit, enable the session's temporary cache for the smaller
    // retries so they can share checked dependency prefixes.
    let mut cache_batches = !args.no_cache;
    while let Some(batch) = pending.pop() {
        if interrupted() {
            bail!("検査を中断しました");
        }
        let mut smaller = batch.split(&paths);
        if !smaller.is_empty() && splits.contains(&batch.key()) {
            pending.extend(smaller.into_iter().rev());
            continue;
        }
        let mut request = args.clone();
        request.worker = Some(workspace.directory.clone());
        request.module = batch.module.as_ref().map(|m| m.join("."));
        request.module_only = batch.exact;
        request.full_check = false;
        request.no_cache = !cache_batches;
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
        let mut command = Command::new(std::env::current_exe()?);
        command
            .arg(&args.path)
            .arg("--worker")
            .arg(workspace.path("request.json"))
            .env_remove("REF_TYPE_PROFILE_PROGRESS")
            .env("REF_TYPE_CACHE_SESSION", &session_token);
        if !args.no_progress {
            display.message(&format!("checking {}", batch.label()));
        }
        let outcome = execute(
            command,
            &workspace,
            (batch.module.is_none() || !smaller.is_empty())
                .then(|| Duration::from_secs(args.batch_seconds)),
            &mut plan,
            display,
            args.no_progress,
        )?;
        if outcome.limited && paths.is_empty() {
            let snapshot = read_snapshot(&workspace.directory)?;
            paths = match sema::Database::new().module_paths(&snapshot) {
                Ok(paths) => paths,
                Err(diagnostics) => {
                    display.finish(false);
                    for diagnostic in diagnostics {
                        eprintln!("{}", diagnostic.render(&snapshot));
                    }
                    return Ok(report::Report::checked(false, false));
                }
            };
            smaller = batch.split(&paths);
        }
        if outcome.limited && !smaller.is_empty() {
            cache_batches = true;
            splits.insert(batch.key());
            // Avoid repeating almost the same oversized work through unary wrappers.
            let mut descendants = batch.children(&paths);
            while descendants.len() == 1 {
                let child = descendants.remove(0);
                descendants = child.children(&paths);
                if !descendants.is_empty() {
                    splits.insert(child.key());
                }
            }
            fs::write(
                workspace.path("layout.json"),
                serde_json::to_vec(&Layout {
                    memory_mib,
                    batch_seconds: args.batch_seconds,
                    splits: splits.clone(),
                })?,
            )?;
            fs::rename(workspace.path("layout.json"), &layout)?;
            if !args.no_progress {
                display.message(&format!(
                    "splitting {} into {} batches",
                    batch.label(),
                    smaller.len()
                ));
            }
            pending.extend(smaller.into_iter().rev());
            continue;
        }
        if !outcome.status.success() {
            success = false;
            display.message(&format!("検査失敗: {} ({})", batch.label(), outcome.status));
            if outcome.limited {
                display.message("この module と参照先がメモリ上限を超えました。検査は未完了です。");
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
        let summary: report::Report = serde_json::from_slice(
            &fs::read(workspace.path("report.json")).context("worker did not finish its report")?,
        )?;
        if summary.outcome == report::Outcome::InternalError {
            bail!("verification worker failed internally");
        }
        if outcome.status.success() != (summary.outcome == report::Outcome::Accepted) {
            bail!("verification worker status disagrees with its report");
        }
        verification_reused |= !fresh && summary.cache.verification_reused;
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
    }
    let current = SourceSnapshot::read(&args.path)?;
    if snapshot_key(&current) != initial_key {
        bail!("検査中にソースが変更されました。再実行して現在のソースを検査してください。");
    }
    if fresh
        && !args.no_cache
        && let Err(error) =
            workspace.publish(&cache, args.cache_budget_mib.saturating_mul(1024 * 1024))
    {
        eprintln!("キャッシュの公開を省略しました: {error:#}");
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
    Ok(report::Report::checked(success, verification_reused))
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn splitting_covers_parent_declarations_and_each_descendant_once() {
        let paths: Vec<Vec<String>> = ["a", "a.B", "a.B.C", "a.D", "b"]
            .into_iter()
            .map(|s| s.split('.').map(str::to_owned).collect())
            .collect();
        let mut pending = vec![Batch {
            module: None,
            exact: false,
        }];
        let mut covered = Vec::new();
        while let Some(batch) = pending.pop() {
            let smaller = batch.split(&paths);
            if smaller.is_empty() {
                covered.push(batch.module.unwrap());
            } else {
                pending.extend(smaller);
            }
        }
        covered.sort();
        assert_eq!(covered, paths);
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
            )
            .unwrap();
            assert!(!outcome.status.success());
            assert_eq!(outcome.limited, limited);
            assert_eq!(outcome.status.signal(), signal);
            assert!(started.elapsed() < Duration::from_secs(2));
        }
    }
}
