//! Keep the terminal and cancellation alive while bounded workers check a snapshot.
use crate::{Args, progress};
use anyhow::{Context, bail};
use sema::{ModuleProgress, ProgressEvent, ProgressPlan, SourceSnapshot};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    fs::{self, File},
    io::{BufRead, BufReader, Read, Seek, SeekFrom, Write},
    os::unix::process::{CommandExt, ExitStatusExt},
    path::{Path, PathBuf},
    process::{Child, Command, ExitCode, ExitStatus, Stdio},
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
            serde_json::to_writer(&mut *file, &message).expect("write worker event");
            file.write_all(b"\n").expect("finish worker event");
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
    let args: Args = serde_json::from_reader(File::open(request)?)?;
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
    Ok(serde_json::from_reader(BufReader::new(File::open(
        directory.join("snapshot.json"),
    )?))?)
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
    fn publish(&self, destination: &Path) -> anyhow::Result<()> {
        let directory = self.path("cache");
        if !directory.exists() {
            return Ok(());
        }
        for entry in fs::read_dir(directory)? {
            let entry = entry?;
            if !entry.file_type()?.is_file() || entry.file_name().to_string_lossy().starts_with('.')
            {
                continue;
            }
            let temporary = self.path("publish.tmp");
            if fs::hard_link(entry.path(), &temporary).is_err() {
                fs::copy(entry.path(), &temporary)?;
            }
            fs::rename(temporary, destination.join(entry.file_name()))?;
        }
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
        thread::sleep(Duration::from_millis(50));
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
    for (path, source) in snapshot.files() {
        digest.update(path.as_os_str().as_encoded_bytes());
        digest.update([0]);
        digest.update(source.text.len().to_le_bytes());
        digest.update(source.text.as_bytes());
    }
    digest.finalize().to_vec()
}

pub fn run(args: &Args, display: &mut progress::Display) -> anyhow::Result<ExitCode> {
    let _signals = Signals::install()?;
    let cache = args
        .cache_dir
        .clone()
        .unwrap_or_else(|| SourceSnapshot::new(&args.path).default_cache_directory());
    if args.clear_cache {
        crate::clear_cache_directory(&cache)?;
    }
    let mut database = sema::Database::with_cache(&cache);
    let snapshot = database.read_snapshot(&args.path, args.full_check_local)?;
    let paths = match database.module_paths(&snapshot) {
        Ok(paths) => paths,
        Err(diagnostics) => {
            display.finish(false);
            for diagnostic in diagnostics {
                eprintln!("{}", diagnostic.render(&snapshot));
            }
            return Ok(ExitCode::FAILURE);
        }
    };
    let module = args
        .module
        .as_ref()
        .map(|name| name.split('.').map(str::to_owned).collect::<Vec<_>>());
    if module.as_ref().is_some_and(|p| !paths.contains(p)) {
        bail!(
            "Module Selection Error: module '{}' was not found",
            args.module.as_ref().unwrap()
        );
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
    let workspace = Workspace::new(&cache)?;
    serde_json::to_writer(
        std::io::BufWriter::new(File::create(workspace.path("snapshot.json"))?),
        &snapshot,
    )?;
    // Drop all parsed syntax before starting a worker. The supervisor retains only paths and hashes.
    drop(snapshot);
    drop(database);
    let layout_key: String =
        Sha256::digest(args.path.canonicalize()?.as_os_str().as_encoded_bytes())
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
    let layout = cache.join(format!("{layout_key}.batches.json"));
    let memory_mib = args.memory_mib.unwrap_or(3072);
    let mut splits = fs::read(&layout)
        .ok()
        .and_then(|s| serde_json::from_slice::<Layout>(&s).ok())
        .filter(|saved| saved.memory_mib == memory_mib && saved.batch_seconds == args.batch_seconds)
        .map(|saved| saved.splits)
        .unwrap_or_default();
    let fresh = args.full_check || args.no_cache || args.trace;
    let worker_cache = if fresh {
        workspace.path("cache")
    } else {
        cache.clone()
    };
    let mut pending = vec![Batch {
        module,
        exact: args.module_only,
    }];
    let mut timings: BTreeMap<Vec<String>, ModuleProgress> = BTreeMap::new();
    let mut outputs = BTreeSet::new();
    let mut success = true;
    while let Some(batch) = pending.pop() {
        if interrupted() {
            bail!("検査を中断しました");
        }
        let smaller = batch.split(&paths);
        if !smaller.is_empty() && splits.contains(&batch.key()) {
            pending.extend(smaller.into_iter().rev());
            continue;
        }
        let mut request = args.clone();
        request.worker = Some(workspace.directory.clone());
        request.module = batch.module.as_ref().map(|m| m.join("."));
        request.module_only = batch.exact;
        request.full_check = false;
        request.no_cache = false;
        request.clear_cache = false;
        request.progress_tty = false;
        request.cache_dir = Some(worker_cache.clone());
        serde_json::to_writer(File::create(workspace.path("request.json"))?, &request)?;
        let mut command = Command::new(std::env::current_exe()?);
        command
            .arg(&args.path)
            .arg("--worker")
            .arg(workspace.path("request.json"))
            .env_remove("REF_TYPE_PROFILE_PROGRESS");
        if !args.no_progress {
            display.message(&format!("checking {}", batch.label()));
        }
        let outcome = execute(
            command,
            &workspace,
            (!smaller.is_empty()).then(|| Duration::from_secs(args.batch_seconds)),
            &mut plan,
            display,
            args.no_progress,
        )?;
        if outcome.limited && !smaller.is_empty() {
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
            serde_json::to_writer(
                File::create(workspace.path("layout.json"))?,
                &Layout {
                    memory_mib,
                    batch_seconds: args.batch_seconds,
                    splits: splits.clone(),
                },
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
    let current =
        sema::Database::with_cache(&cache).read_snapshot(&args.path, args.full_check_local)?;
    if snapshot_key(&current) != initial_key {
        success = false;
        display
            .message("検査中にソースが変更されました。再実行して現在のソースを検査してください。");
    }
    if fresh && !args.no_cache {
        workspace.publish(&cache)?;
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
    Ok(if success {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    })
}

#[cfg(test)]
mod tests {
    use super::*;

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

    #[test]
    fn terminal_elapsed_time_keeps_updating_when_the_worker_sends_no_events() {
        #[derive(Clone)]
        struct Output(std::sync::Arc<std::sync::Mutex<Vec<u8>>>);
        impl Write for Output {
            fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
                self.0.lock().unwrap().extend_from_slice(bytes);
                Ok(bytes.len())
            }
            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }
        let output = Output(Default::default());
        let mut display = progress::Display::new(true, Box::new(output.clone()));
        let workspace = Workspace::new(&std::env::temp_dir()).unwrap();
        let mut command = Command::new("sleep");
        command.arg("0.5");
        let outcome = execute(
            command,
            &workspace,
            None,
            &mut ProgressPlan {
                packages: vec![],
                modules: vec![],
            },
            &display,
            true,
        )
        .unwrap();
        assert!(outcome.status.success());
        display.finish(true);
        let bytes = output.0.lock().unwrap();
        let text = String::from_utf8_lossy(&bytes);
        let elapsed: BTreeSet<_> = text
            .split("Loading (")
            .skip(1)
            .filter_map(|line| line.split_once("s)").map(|(time, _)| time))
            .collect();
        assert!(elapsed.len() >= 2, "elapsed time stopped: {text}");
    }
}
