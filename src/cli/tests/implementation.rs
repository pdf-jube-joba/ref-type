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

fn progress_lines(output: &Output) -> Vec<String> {
    String::from_utf8_lossy(&output.stderr)
        .lines()
        .filter(|line| line.starts_with("check ") || line.starts_with("skip "))
        .map(str::to_owned)
        .collect()
}

#[test]
fn source_inspection_leaves_existing_semantic_cache_untouched() {
    let fixture = FixtureDirectory::new();
    fixture.write("ref.toml", "[package]\nname = \"inspection\"\n");
    fixture.write(
        "src/root.ref",
        "\\module Values { \\definition value: \\Prop := \\forall (P: \\Prop) -> P -> P; }\n",
    );
    let cache = fixture.0.join("refcache");
    fs::create_dir(&cache).unwrap();
    for mode in ["--parse-only", "--list-modules"] {
        let output = run_ref_file_with_args(&fixture.0, &fixture.0, &[mode]).unwrap();
        assert!(output.status.success(), "{}", output_details(&output));
        assert!(
            fs::read_dir(&cache).unwrap().next().is_none(),
            "source inspection created semantic cache files"
        );
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

#[cfg(target_os = "linux")]
#[test]
fn uncached_native_batch_skips_portable_artifact_generation() {
    let fixture = FixtureDirectory::new();
    fixture.write("ref.toml", "[package]\nname = 'uncached'\n");
    fixture.write(
        "src/root.ref",
        r"\module M { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }",
    );
    let output = run_ref_file_with_args(
        &fixture.0,
        &fixture.0,
        &["--no-cache", "--cache-stats", "--no-progress"],
    )
    .unwrap();
    assert!(output.status.success(), "{}", output_details(&output));
    let log = String::from_utf8_lossy(&output.stderr);
    assert!(log.contains("package_writes: 0"), "{log}");
    assert!(log.contains("compressed_environment_bytes: 0"), "{log}");
    assert!(log.contains("environment_write_bytes: 0"), "{log}");
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
    for (args, action) in [
        (vec![], "check"),
        (vec![], "skip"),
        (vec!["--full-check"], "check"),
    ] {
        let output = run_ref_file_with_args(&fixture.0, &fixture.0, &args).unwrap();
        assert!(output.status.success(), "{}", output_details(&output));
        let lines = progress_lines(&output);
        for module in ["batch.Root.A", "batch.Root.B"] {
            assert!(
                lines
                    .iter()
                    .any(|line| line.starts_with(&format!("{action} {module} ("))),
                "{lines:?}"
            );
        }
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
    assert!(String::from_utf8_lossy(&retuned.stderr).contains("checking project\n"));
    fs::write(
        root,
        source.replace(
            "root: \\Prop := \\forall (P: \\Prop) -> P -> P",
            "root: \\Prop := \\Set",
        ),
    )
    .unwrap();
    let output = run_ref_file(&fixture.0, &fixture.0).unwrap();
    assert!(!output.status.success(), "{}", output_details(&output));
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("root.ref:1:"),
        "{}",
        output_details(&output)
    );
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
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("検査中にソースが変更されました"),
        "{}",
        output_details(&output)
    );
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

#[test]
fn captured_sources_keep_cache_identity_and_check_their_own_text() {
    let fixture = FixtureDirectory::new();
    fixture.write("ref.toml", "[package]\nname = 'captured'\n");
    let root = fixture.write(
        "src/root.ref",
        r"\module M { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }",
    );
    let first = fixture.0.join("first.json");
    let second = fixture.0.join("second.json");
    let export = run_ref_file_with_args(
        &fixture.0,
        &fixture.0,
        &[
            "--parse-only",
            "--save-source-snapshot",
            first.to_str().unwrap(),
        ],
    )
    .unwrap();
    assert!(export.status.success(), "{}", output_details(&export));
    assert!(
        !fixture.0.join("refcache").exists(),
        "capture created semantic cache"
    );
    let snapshot: serde_json::Value = serde_json::from_slice(&fs::read(&first).unwrap()).unwrap();
    assert_eq!(snapshot["entry"].as_str(), fixture.0.to_str());
    assert!(snapshot["files"].get(root.to_str().unwrap()).is_some());
    fs::copy(&first, &second).unwrap();
    fs::write(&root, r"\module M { \definition P: \Prop := \Set; }").unwrap();
    for (path, action) in [
        (&first, "check captured.M ("),
        (&second, "skip captured.M ("),
    ] {
        let output = run_ref_file_with_args(
            &fixture.0,
            &fixture.0,
            &["--source-snapshot", path.to_str().unwrap()],
        )
        .unwrap();
        assert!(output.status.success(), "{}", output_details(&output));
        assert!(
            progress_lines(&output)
                .iter()
                .any(|line| line.starts_with(action)),
            "{}",
            output_details(&output)
        );
    }
    let changed = fixture.0.join("changed.json");
    let export = run_ref_file_with_args(
        &fixture.0,
        &fixture.0,
        &[
            "--parse-only",
            "--save-source-snapshot",
            changed.to_str().unwrap(),
        ],
    )
    .unwrap();
    assert!(export.status.success(), "{}", output_details(&export));
    let output = run_ref_file_with_args(
        &fixture.0,
        &fixture.0,
        &["--source-snapshot", changed.to_str().unwrap()],
    )
    .unwrap();
    assert!(!output.status.success(), "{}", output_details(&output));
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("root.ref:1:"),
        "{}",
        output_details(&output)
    );
}

#[test]
fn captured_sources_reject_entry_mismatch_and_unreadable_input() {
    let fixture = FixtureDirectory::new();
    fixture.write("ref.toml", "[package]\nname = 'entry'\n");
    fixture.write("src/root.ref", r"\module M {}");
    let snapshot = fixture.0.join("source.json");
    let output = run_ref_file_with_args(
        &fixture.0,
        &fixture.0,
        &[
            "--parse-only",
            "--save-source-snapshot",
            snapshot.to_str().unwrap(),
        ],
    )
    .unwrap();
    assert!(output.status.success(), "{}", output_details(&output));
    let other = FixtureDirectory::new();
    other.write("ref.toml", "[package]\nname = 'other'\n");
    other.write("src/root.ref", r"\module Other {}");
    let output = run_ref_file_with_args(
        &other.0,
        &other.0,
        &["--source-snapshot", snapshot.to_str().unwrap()],
    )
    .unwrap();
    assert!(!output.status.success(), "{}", output_details(&output));
    assert!(String::from_utf8_lossy(&output.stderr).contains("does not match requested path"));
    fs::write(&snapshot, "invalid JSON").unwrap();
    let output = run_ref_file_with_args(
        &fixture.0,
        &fixture.0,
        &[
            "--parse-only",
            "--source-snapshot",
            snapshot.to_str().unwrap(),
        ],
    )
    .unwrap();
    assert!(!output.status.success(), "{}", output_details(&output));
    assert!(String::from_utf8_lossy(&output.stderr).contains("decode source snapshot"));
}

#[cfg(target_os = "linux")]
#[test]
fn native_check_detects_captured_input_changes_after_starting() {
    let fixture = FixtureDirectory::new();
    fixture.write("ref.toml", "[package]\nname = 'captured_edit'\n");
    let declarations: String = (0..2000)
        .map(|n| format!("\\definition value{n}: \\Prop := \\forall (P: \\Prop) -> P -> P;\n"))
        .collect();
    fixture.write(
        "src/root.ref",
        &format!("\\module Work {{\n{declarations}}}\n"),
    );
    let snapshot = fixture.0.join("source.json");
    let output = run_ref_file_with_args(
        &fixture.0,
        &fixture.0,
        &[
            "--parse-only",
            "--save-source-snapshot",
            snapshot.to_str().unwrap(),
        ],
    )
    .unwrap();
    assert!(output.status.success(), "{}", output_details(&output));
    let mut parent = Command::new(env!("CARGO_BIN_EXE_cli"))
        .arg(&fixture.0)
        .arg("--source-snapshot")
        .arg(&snapshot)
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
            panic!("native checker did not capture the input");
        }
        thread::sleep(Duration::from_millis(5));
    }
    let mut changed: serde_json::Value =
        serde_json::from_slice(&fs::read(&snapshot).unwrap()).unwrap();
    for source in changed["files"].as_object_mut().unwrap().values_mut() {
        if source.as_str().is_some_and(|s| s.contains("value0")) {
            *source = serde_json::Value::String("\\module Changed {}\n".into());
        }
    }
    fs::write(snapshot, serde_json::to_vec(&changed).unwrap()).unwrap();
    let output = parent.wait_with_output().unwrap();
    assert!(!output.status.success(), "{}", output_details(&output));
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("検査中に入力 snapshot が変更されました"),
        "{}",
        output_details(&output)
    );
}
