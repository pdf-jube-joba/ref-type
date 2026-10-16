//! Tests of supervisor batching, snapshots and child process cleanup.
use std::{
    fs,
    io::Read,
    path::{Path, PathBuf},
    process::{Command, Output},
    thread,
    time::{Duration, Instant},
};

const PROCESS_TIMEOUT: Duration = Duration::from_secs(20);

fn run_ref_file(workspace: &Path, path: &Path) -> Result<Output, String> {
    run_ref_file_with_args(workspace, path, &[])
}

fn run_ref_file_with_args(workspace: &Path, path: &Path, args: &[&str]) -> Result<Output, String> {
    let mut child = Command::new(env!("CARGO_BIN_EXE_cli"))
        .arg(path)
        .args(args)
        .env_remove("RUST_LOG")
        .env_remove("REF_TYPE_COMPACT_DIAGNOSTICS")
        .current_dir(workspace)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .map_err(|error| format!("failed to run {}: {error}", path.display()))?;
    // Drain both pipes while the child runs: waiting first can deadlock on a full pipe.
    let mut stdout = child.stdout.take().expect("stdout is piped");
    let mut stderr = child.stderr.take().expect("stderr is piped");
    let stdout_reader = thread::spawn(move || {
        let mut bytes = Vec::new();
        stdout.read_to_end(&mut bytes).map(|_| bytes)
    });
    let stderr_reader = thread::spawn(move || {
        let mut bytes = Vec::new();
        stderr.read_to_end(&mut bytes).map(|_| bytes)
    });
    let started = Instant::now();
    loop {
        if let Some(status) = child
            .try_wait()
            .map_err(|error| format!("failed to wait for {}: {error}", path.display()))?
        {
            let stdout = stdout_reader
                .join()
                .map_err(|_| "stdout reader panicked")?
                .map_err(|error| error.to_string())?;
            let stderr = stderr_reader
                .join()
                .map_err(|_| "stderr reader panicked")?
                .map_err(|error| error.to_string())?;
            return Ok(Output {
                status,
                stdout,
                stderr,
            });
        }
        if started.elapsed() >= PROCESS_TIMEOUT {
            let _ = child.kill();
            let _ = child.wait();
            let _ = stdout_reader.join();
            let _ = stderr_reader.join();
            return Err(format!(
                "{} did not finish within {} seconds",
                path.display(),
                PROCESS_TIMEOUT.as_secs()
            ));
        }
        thread::sleep(Duration::from_millis(10));
    }
}

fn output_details(output: &Output) -> String {
    format!(
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    )
}

struct FixtureDirectory(PathBuf);

impl FixtureDirectory {
    fn new() -> Self {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        loop {
            let path = std::env::temp_dir().join(format!(
                "ref-type-test-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("cannot create fixture directory: {error}"),
            }
        }
    }

    fn write(&self, name: &str, source: &str) -> PathBuf {
        let path = self.0.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(&path, source).unwrap();
        path
    }
}

impl Drop for FixtureDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[cfg(target_os = "linux")]
fn child_process(parent: u32) -> Option<u32> {
    // The per-task `children` file requires an optional kernel configuration.
    fs::read_dir("/proc")
        .unwrap()
        .filter_map(Result::ok)
        .find_map(|entry| {
            let pid = entry.file_name().to_str()?.parse().ok()?;
            let status = fs::read_to_string(entry.path().join("status")).ok()?;
            let ppid = status
                .lines()
                .find_map(|line| line.strip_prefix("PPid:"))?
                .trim()
                .parse::<u32>()
                .ok()?;
            (ppid == parent).then_some(pid)
        })
}

#[cfg(unix)]
#[test]
fn uncached_check_preserves_non_utf8_source_identities() {
    use std::{ffi::OsStr, os::unix::ffi::OsStrExt};
    let fixture = FixtureDirectory::new();
    let path = fixture.0.join(OsStr::from_bytes(b"source_\xff.ref"));
    fs::write(
        &path,
        r"\module M { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }",
    )
    .unwrap();
    let output =
        run_ref_file_with_args(&fixture.0, &path, &["--no-cache", "--no-progress"]).unwrap();
    assert!(output.status.success(), "{}", output_details(&output));
}

#[cfg(target_os = "linux")]
#[test]
fn native_batches_recheck_with_a_fresh_cache_and_preserve_parent_errors() {
    use sha2::{Digest, Sha256};
    let fixture = FixtureDirectory::new();
    fixture.write("ref.toml", "[package]\nname = \"batch\"\n");
    let source = "\\module Root { \\definition root: \\Prop := \\forall (P: \\Prop) -> P -> P;\n\\module A { \\definition a: \\Prop := \\forall (P: \\Prop) -> P -> P; }\n\\module B { \\definition b: \\Prop := \\forall (P: \\Prop) -> P -> P; } }\n";
    let root = fixture.write("src/root.ref", source);
    let cache = fixture.0.join("refcache");
    fs::create_dir_all(&cache).unwrap();
    let key: String = Sha256::digest(
        fixture
            .0
            .canonicalize()
            .unwrap()
            .as_os_str()
            .as_encoded_bytes(),
    )
    .iter()
    .map(|byte| format!("{byte:02x}"))
    .collect();
    fs::write(
        cache.join(format!("{key}.batches.json")),
        r#"{"memory_mib":3072,"batch_seconds":180,"splits":["","batch","batch.Root"]}"#,
    )
    .unwrap();
    for args in [vec![], vec![], vec!["--full-check"]] {
        let output = run_ref_file_with_args(&fixture.0, &fixture.0, &args).unwrap();
        assert!(output.status.success(), "{}", output_details(&output));
        assert!(fs::read_dir(&cache).unwrap().all(|entry| {
            !entry
                .unwrap()
                .file_name()
                .to_string_lossy()
                .starts_with(".check-")
        }));
    }
    let retuned =
        run_ref_file_with_args(&fixture.0, &fixture.0, &["--batch-seconds", "1"]).unwrap();
    assert!(retuned.status.success(), "{}", output_details(&retuned));
    fs::write(
        root,
        source.replace(
            "root: \\Prop := \\forall (P: \\Prop) -> P -> P",
            "root: \\Prop := \\Set",
        ),
    )
    .unwrap();
    let output = run_ref_file(&fixture.0, &fixture.0).unwrap();
    assert_eq!(output.status.code(), Some(1), "{}", output_details(&output));
}

#[cfg(target_os = "linux")]
#[test]
fn native_check_detects_source_changes_after_starting_its_snapshot() {
    let fixture = FixtureDirectory::new();
    fixture.write("ref.toml", "[package]\nname = \"editing\"\n");
    let declarations: String = (0..2000)
        .map(|n| format!("\\definition value{n}: \\Prop := \\forall (P: \\Prop) -> P -> P;\n"))
        .collect();
    let root = fixture.write(
        "src/root.ref",
        &format!("\\module Work {{\n{declarations}}}\n"),
    );
    let mut parent = Command::new(env!("CARGO_BIN_EXE_cli"))
        .arg(&fixture.0)
        .args(["--full-check", "--no-progress"])
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let started = Instant::now();
    loop {
        if child_process(parent.id()).is_some() {
            break;
        }
        if started.elapsed() > Duration::from_secs(10) || parent.try_wait().unwrap().is_some() {
            let _ = parent.kill();
            let _ = parent.wait();
            panic!("native checker did not capture the snapshot");
        }
        thread::sleep(Duration::from_millis(5));
    }
    fs::write(root, "\\module Changed {}\n").unwrap();
    let output = parent.wait_with_output().unwrap();
    assert!(!output.status.success(), "{}", output_details(&output));
}

#[cfg(target_os = "linux")]
#[test]
fn cancelling_native_check_reaps_the_worker_and_removes_its_workspace() {
    let fixture = FixtureDirectory::new();
    fixture.write("ref.toml", "[package]\nname = \"cancel\"\n");
    let declarations: String = (0..2_000)
        .map(|n| format!("\\definition value{n}: \\Prop := \\forall (P: \\Prop) -> P -> P;\n"))
        .collect();
    fixture.write(
        "src/root.ref",
        &format!("\\module Slow {{\n{declarations}}}\n"),
    );
    let mut parent = Command::new(env!("CARGO_BIN_EXE_cli"))
        .arg(&fixture.0)
        .args(["--full-check", "--no-progress"])
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()
        .unwrap();
    let started = Instant::now();
    let worker = loop {
        if let Some(pid) = child_process(parent.id()) {
            break pid;
        }
        if started.elapsed() > Duration::from_secs(10) || parent.try_wait().unwrap().is_some() {
            let _ = parent.kill();
            let _ = parent.wait();
            panic!("native check did not start its worker");
        }
        thread::sleep(Duration::from_millis(5));
    };
    // SAFETY: send SIGINT to the subprocess owned by this test.
    assert_eq!(unsafe { libc::kill(parent.id() as i32, libc::SIGINT) }, 0);
    let interrupted = Instant::now();
    loop {
        if let Some(status) = parent.try_wait().unwrap() {
            assert_eq!(status.code(), Some(130));
            break;
        }
        if interrupted.elapsed() > Duration::from_secs(2) {
            let _ = parent.kill();
            let _ = parent.wait();
            panic!("Ctrl+C did not stop the checker within two seconds");
        }
        thread::sleep(Duration::from_millis(5));
    }
    assert!(
        !Path::new(&format!("/proc/{worker}")).exists(),
        "worker was not reaped"
    );
    assert!(
        fs::read_dir(fixture.0.join("refcache"))
            .unwrap()
            .all(|entry| !entry
                .unwrap()
                .file_name()
                .to_string_lossy()
                .starts_with(".check-"))
    );
}
