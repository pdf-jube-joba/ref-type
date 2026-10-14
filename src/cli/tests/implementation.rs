//! Tests of the current Rust instrumentation and supervisor implementation.
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
    run_ref_file_with_timeout(workspace, path, args, PROCESS_TIMEOUT)
}

fn run_ref_file_with_timeout(
    workspace: &Path,
    path: &Path,
    args: &[&str],
    timeout: Duration,
) -> Result<Output, String> {
    run_ref_file_with_environment(workspace, path, args, timeout, &[])
}

fn run_ref_file_with_environment(
    workspace: &Path,
    path: &Path,
    args: &[&str],
    timeout: Duration,
    environment: &[(&str, &str)],
) -> Result<Output, String> {
    let mut child = Command::new(env!("CARGO_BIN_EXE_cli"))
        .arg(path)
        .args(args)
        .env_remove("RUST_LOG")
        .env_remove("REF_TYPE_COMPACT_DIAGNOSTICS")
        .envs(environment.iter().copied())
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
        if started.elapsed() >= timeout {
            let _ = child.kill();
            let _ = child.wait();
            let _ = stdout_reader.join();
            let _ = stderr_reader.join();
            return Err(format!(
                "{} did not finish within {} seconds",
                path.display(),
                timeout.as_secs()
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

fn dependency_chain(fixture: &FixtureDirectory) -> PathBuf {
    fixture.write("a/ref.toml", "[package]\nname = \"a\"\n");
    fixture.write("a/src/root.ref", r"\module Base;");
    fixture.write(
        "a/src/Base.ref",
        r"\definition P: \Prop := \forall (P: \Prop) -> P -> P;",
    );
    fixture.write(
        "b/ref.toml",
        "[package]\nname = \"b\"\n[dependencies]\na = { path = \"../a\" }\n",
    );
    fixture.write(
        "b/src/root.ref",
        r"\module Bridge { \import a.Base[] \as A; \definition P: \Prop := A.P; }",
    );
    fixture.write(
        "c/ref.toml",
        "[package]\nname = \"c\"\n[dependencies]\nb = { path = \"../b\" }\n",
    );
    fixture.write("c/src/root.ref", r"\module Client { \import b.Bridge[] \as B; \infer B.P; } \module Independent { \module Child { \infer \Set; } }");
    fixture.0.join("c")
}

fn progress_lines(output: &Output) -> Vec<String> {
    String::from_utf8_lossy(&output.stderr)
        .lines()
        .filter(|line| line.starts_with("check ") || line.starts_with("skip "))
        .map(str::to_owned)
        .collect()
}

#[cfg(target_os = "linux")]
#[test]
fn no_cache_with_zero_budget_leaves_persistent_artifacts_unchanged() {
    fn contents(directory: &Path) -> std::collections::BTreeMap<PathBuf, Vec<u8>> {
        let mut result = std::collections::BTreeMap::new();
        for entry in fs::read_dir(directory).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                result.extend(contents(&path));
            } else {
                result.insert(path.clone(), fs::read(path).unwrap());
            }
        }
        result
    }

    let fixture = FixtureDirectory::new();
    fixture.write("ref.toml", "[package]\nname = \"example\"\n");
    fixture.write(
        "src/root.ref",
        r"\module M { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }",
    );
    let cached = run_ref_file(&fixture.0, &fixture.0).unwrap();
    assert!(cached.status.success(), "{}", output_details(&cached));
    let cache = fixture.0.join("refcache");
    let before = contents(&cache);
    assert!(!before.is_empty());
    let uncached = run_ref_file_with_args(
        &fixture.0,
        &fixture.0,
        &["--no-cache", "--cache-budget-mib", "0", "--no-progress"],
    )
    .unwrap();
    assert!(uncached.status.success(), "{}", output_details(&uncached));
    assert_eq!(contents(&cache), before);
}

#[test]
fn progress_profiles_report_modules_in_piped_output_and_cached_runs() {
    let fixture = FixtureDirectory::new();
    let root = dependency_chain(&fixture);
    for cached in [false, true] {
        let output = run_ref_file_with_environment(
            &fixture.0,
            &root,
            &[],
            PROCESS_TIMEOUT,
            &[("REF_TYPE_PROFILE_PROGRESS", "1")],
        )
        .unwrap();
        assert!(output.status.success(), "{}", output_details(&output));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("event=planned"), "{stderr}");
        assert!(stderr.contains("event=finished success=true"), "{stderr}");
        let action = if cached { "Skip" } else { "Check" };
        for module in ["a.Base", "b.Bridge", "c.Client", "c.Independent.Child"] {
            assert!(
                stderr.contains(&format!(
                    "event=complete action={action} module={module} module_seconds="
                )),
                "{stderr}"
            );
            if !cached {
                let start = stderr
                    .find(&format!("event=start module={module} package_completed="))
                    .unwrap();
                let end = stderr
                    .find(&format!("event=complete action=Check module={module} "))
                    .unwrap();
                assert!(start < end, "{stderr}");
            }
        }
        let finished = stderr.find("event=finished").unwrap();
        let summary = stderr
            .find(if cached {
                "skip a.Base ("
            } else {
                "check a.Base ("
            })
            .unwrap();
        assert!(finished < summary, "{stderr}");
        assert!(!stderr.contains('\r'), "{stderr}");
    }
}

#[test]
fn module_progress_reports_checks_skips_children_and_seconds_in_every_mode() {
    let fixture = FixtureDirectory::new();
    let root = dependency_chain(&fixture);
    for (args, expected) in [
        (
            vec![],
            vec![
                "check a.Base",
                "check b.Bridge",
                "check c.Client",
                "check c.Independent",
                "check c.Independent.Child",
            ],
        ),
        (
            vec![],
            vec![
                "skip a.Base",
                "skip b.Bridge",
                "skip c.Client",
                "skip c.Independent",
                "skip c.Independent.Child",
            ],
        ),
        (
            vec!["--full-check"],
            vec![
                "check a.Base",
                "check b.Bridge",
                "check c.Client",
                "check c.Independent",
                "check c.Independent.Child",
            ],
        ),
        (
            vec!["--full-check-local"],
            vec![
                "skip a.Base",
                "skip b.Bridge",
                "check c.Client",
                "check c.Independent",
                "check c.Independent.Child",
            ],
        ),
        (
            vec!["--no-cache"],
            vec![
                "check a.Base",
                "check b.Bridge",
                "check c.Client",
                "check c.Independent",
                "check c.Independent.Child",
            ],
        ),
    ] {
        let output = run_ref_file_with_args(&fixture.0, &root, &args).unwrap();
        assert!(output.status.success(), "{}", output_details(&output));
        let lines = progress_lines(&output);
        assert_eq!(lines.len(), expected.len(), "{lines:?}");
        for prefix in expected {
            assert!(
                lines
                    .iter()
                    .any(|line| line.starts_with(&format!("{prefix} ("))),
                "missing {prefix}: {lines:?}"
            );
        }
        for line in &lines {
            let seconds = line.split_once(" (").unwrap().1.strip_suffix("s)").unwrap();
            assert!(seconds.parse::<f64>().unwrap() >= 0.0, "{line}");
        }
        let stderr = String::from_utf8_lossy(&output.stderr);
        let seconds = |line: &str| {
            line.split_once(" (")
                .unwrap()
                .1
                .strip_suffix("s)")
                .unwrap()
                .parse::<f64>()
                .unwrap()
        };
        let shared = seconds(
            stderr
                .lines()
                .find(|line| line.starts_with("shared ("))
                .unwrap(),
        );
        let total = seconds(
            stderr
                .lines()
                .find(|line| line.starts_with("total ("))
                .unwrap(),
        );
        let sum = lines.iter().map(|line| seconds(line)).sum::<f64>() + shared;
        assert!(total > 0.0);
        assert!(
            (sum - total).abs() <= total * 0.01,
            "sum={sum}, total={total}: {stderr}"
        );
        let mut quiet_args = args.clone();
        quiet_args.push("--no-progress");
        let quiet = run_ref_file_with_args(&fixture.0, &root, &quiet_args).unwrap();
        assert!(quiet.status.success(), "{}", output_details(&quiet));
        assert_eq!(quiet.stdout, output.stdout);
        assert!(quiet.stderr.is_empty(), "{}", output_details(&quiet));
    }
}

#[test]
fn transitive_sources_are_checked_after_artifact_corruption() {
    let fixture = FixtureDirectory::new();
    let root = dependency_chain(&fixture);
    fixture.write("c/unloaded/ref.toml", "[package]\nname = \"unloaded\"\n");
    fixture.write("c/unloaded/src/root.ref", "invalid syntax");
    let first = run_ref_file(&fixture.0, &root).unwrap();
    assert!(first.status.success(), "{}", output_details(&first));
    let mut pending = vec![root.join("refcache/v2/objects")];
    let mut damaged = 0;
    while let Some(directory) = pending.pop() {
        for entry in fs::read_dir(directory).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                pending.push(path);
            } else {
                fs::write(path, "truncated").unwrap();
                damaged += 1;
            }
        }
    }
    assert!(damaged > 0);
    fixture.write("a/src/Base.ref", r"\definition P: \Prop := \Set;");
    let output = run_ref_file_with_args(&fixture.0, &root, &["--full-check-local"]).unwrap();
    assert_eq!(output.status.code(), Some(1), "{}", output_details(&output));
    assert!(String::from_utf8_lossy(&output.stderr).contains("Base.ref:1:"));
}

#[test]
fn parent_and_external_references_share_checked_child_declarations() {
    let fixture = FixtureDirectory::new();
    let path = fixture.write(
        "root.ref",
        r"
\module Parent {
  \module Child { \definition marker: \Prop := \forall (P: \Prop) -> P -> P; }
  \import \root.Parent[].Child[] \as Local;
  \infer Local.marker;
}
\module Other {
  \import \root.Parent[].Child[] \as External;
  \infer External.marker;
}",
    );
    let result = run_ref_file_with_environment(
        &fixture.0,
        &path,
        &["--no-cache"],
        PROCESS_TIMEOUT,
        &[
            ("REF_TYPE_PROFILE_MODULES", "1"),
            ("REF_TYPE_PROFILE_DECLARATIONS", "1"),
        ],
    )
    .unwrap();
    assert!(result.status.success(), "{}", output_details(&result));
    let log = String::from_utf8_lossy(&result.stderr);
    assert_eq!(
        log.matches("definition marker (excluding diagnostics)")
            .count(),
        1,
        "{log}"
    );
    assert!(
        log.contains("phase=specialization-cache") && log.contains("misses=0"),
        "{log}"
    );
    assert!(
        log.contains("phase=load") && log.contains("environment="),
        "{log}"
    );
    let output = String::from_utf8_lossy(&result.stdout);
    let lines: Vec<_> = output.lines().collect();
    assert_eq!(lines.len(), 2, "{output}");
}

#[test]
fn cost_profiles_finish_on_success_and_type_errors_without_progress_logs() {
    let fixture = FixtureDirectory::new();
    for (source, success) in [
        (
            r"\module Root { \definition identity(P: \Prop)(p: P): P := p; }",
            true,
        ),
        (
            r"\module Root { \definition invalid: \Prop := \Set; }",
            false,
        ),
    ] {
        let path = fixture.write("root.ref", source);
        let output = run_ref_file_with_environment(
            &fixture.0,
            &path,
            &["--no-cache", "--no-progress", "--diagnostics", "compact"],
            PROCESS_TIMEOUT,
            &[("REF_TYPE_PROFILE_COSTS", "resolve.total,kernel.")],
        )
        .unwrap();
        assert_eq!(
            output.status.success(),
            success,
            "{}",
            output_details(&output)
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("cost=resolve.total calls=1"), "{stderr}");
        assert!(
            stderr.contains("cost_group=kernel exclusive_us="),
            "{stderr}"
        );
        assert_eq!(
            stderr.matches("cost_total elapsed_us=").count(),
            1,
            "{stderr}"
        );
        assert!(!stderr.contains("cost=resolve.front-binding"), "{stderr}");
        assert!(!String::from_utf8_lossy(&output.stdout).contains("cost="));
    }
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
    let children = format!("/proc/{0}/task/{0}/children", parent.id());
    let started = Instant::now();
    loop {
        if fs::read_to_string(&children).is_ok_and(|text| !text.trim().is_empty()) {
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
    let declarations: String = (0..20_000)
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
    let children = format!("/proc/{0}/task/{0}/children", parent.id());
    let worker = loop {
        if let Ok(text) = fs::read_to_string(&children)
            && let Some(pid) = text.split_whitespace().next()
        {
            break pid.to_owned();
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
