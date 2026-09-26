use std::{
    fs,
    io::Read,
    path::{Path, PathBuf},
    process::{Command, Output},
    thread,
    time::{Duration, Instant},
};

const PROCESS_TIMEOUT: Duration = Duration::from_secs(20);
// This project elaborates and checks the entire library. Allow enough time for
// the debug-build process when it runs concurrently with the other test cases.
const LIBRARY_TIMEOUT: Duration = Duration::from_secs(180);

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("cli crate must be two levels below the workspace root")
        .to_path_buf()
}

fn collect_ref_files(directory: &Path, files: &mut Vec<PathBuf>) {
    let entries = fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", directory.display()));

    for entry in entries {
        let entry = entry.unwrap_or_else(|error| {
            panic!(
                "failed to read an entry in {}: {error}",
                directory.display()
            )
        });
        let path = entry.path();
        if path.is_dir() {
            collect_ref_files(&path, files);
        } else if path.extension().is_some_and(|extension| extension == "ref") {
            files.push(path);
        }
    }
}

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
    let mut child = Command::new(env!("CARGO_BIN_EXE_cli"))
        .arg(path)
        .args(args)
        .env_remove("RUST_LOG")
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

fn run_cases(relative_directory: &str, should_succeed: bool) {
    let workspace = workspace_root();
    let directory = workspace.join(relative_directory);
    let mut files = Vec::new();
    collect_ref_files(&directory, &mut files);
    files.sort();

    assert!(
        !files.is_empty(),
        "no .ref files found in {}",
        directory.display()
    );

    let mut failures = Vec::new();
    for path in files {
        let output = match run_ref_file(&workspace, &path) {
            Ok(output) => output,
            Err(error) => {
                failures.push(error);
                continue;
            }
        };
        let stderr = String::from_utf8_lossy(&output.stderr);
        let expected = fs::read_to_string(&path).expect("read fixture");
        let expected_errors: Vec<_> = expected
            .lines()
            .filter_map(|line| {
                line.strip_prefix("/* expect-error: ")
                    .and_then(|line| line.strip_suffix(" */"))
            })
            .collect();
        let valid = if should_succeed {
            output.status.success()
        } else {
            output.status.code() == Some(1)
                && !expected_errors.is_empty()
                && expected_errors
                    .iter()
                    .all(|message| stderr.contains(message))
                && !stderr.contains("panicked at")
        };
        if !valid {
            let expectation = if should_succeed {
                "was expected to succeed"
            } else {
                "was expected to fail"
            };
            failures.push(format!(
                "{} {expectation}\n{}",
                path.display(),
                output_details(&output)
            ));
        }
    }

    assert!(
        failures.is_empty(),
        "{} case(s) had an unexpected result:\n\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}

#[test]
fn ok_ref_files_succeed() {
    run_cases("tests/ok", true);
}

#[test]
fn ng_ref_files_fail() {
    run_cases("tests/ng", false);
}

#[test]
fn library_examples_succeed() {
    let workspace = workspace_root();
    let path = workspace.join("tests/projects/library");
    let output = run_ref_file_with_timeout(&workspace, &path, &[], LIBRARY_TIMEOUT)
        .unwrap_or_else(|error| panic!("{error}"));
    assert!(output.status.success(), "{}", output_details(&output));
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        !stdout.contains("check failed:") && !stdout.contains("infer failed:"),
        "{}",
        output_details(&output)
    );
}

#[test]
fn packages_resolve_dependencies_and_local_children() {
    let fixture = FixtureDirectory::new();
    fixture.write("shared/ref.toml", "[package]\nname = \"shared\"\n");
    fixture.write(
        "shared/src/root.ref",
        r"\module Truth { \definition proposition: \Prop := \forall (P: \Prop) -> P -> P; }",
    );
    fixture.write(
        "left/ref.toml",
        "[package]\nname = \"left\"\n[dependencies]\nshared = { path = \"../shared\" }\n",
    );
    fixture.write("left/src/root.ref", r"\module Source { \import shared.Truth[] \as T; \definition proposition: \Prop := T.proposition; }");
    fixture.write(
        "right/ref.toml",
        "[package]\nname = \"right\"\n[dependencies]\nshared = { path = \"../shared\" }\n",
    );
    fixture.write("right/src/root.ref", r"\module Source { \import shared.Truth[] \as T; \definition proposition: \Prop := T.proposition; }");
    fixture.write("app/ref.toml", "[package]\nname = \"app\"\n[dependencies]\nleft = { path = \"../left\" }\nright = { path = \"../right\" }\n");
    fixture.write(
        "app/src/root.ref",
        r"
\module Client {
  \module Child { \definition proposition: \Prop := \forall (P: \Prop) -> P -> P; }
  \import .Child[] \as Local;
  \import left.Source[] \as L;
  \import right.Source[] \as R;
  \definition fromLeft: \Prop := L.proposition;
  \definition fromRight: \Prop := R.proposition;
  \definition fromChild: \Prop := Local.proposition;
}
",
    );
    let output = run_ref_file(&fixture.0, &fixture.0.join("app")).unwrap();
    assert!(output.status.success(), "{}", output_details(&output));
}

#[test]
fn package_cycles_report_the_dependency_path() {
    let fixture = FixtureDirectory::new();
    fixture.write(
        "a/ref.toml",
        "[package]\nname = \"a\"\n[dependencies]\nb = { path = \"../b\" }\n",
    );
    fixture.write(
        "b/ref.toml",
        "[package]\nname = \"b\"\n[dependencies]\na = { path = \"../a\" }\n",
    );
    let output = run_ref_file(&fixture.0, &fixture.0.join("a")).unwrap();
    assert_eq!(output.status.code(), Some(1), "{}", output_details(&output));
    assert!(String::from_utf8_lossy(&output.stderr).contains("cyclic package dependency"));
}

#[test]
fn file_errors_are_only_written_to_stderr() {
    let workspace = workspace_root();
    let path = workspace.join("tests/ng/param_free.ref");
    let output = run_ref_file(&workspace, &path).unwrap_or_else(|error| panic!("{error}"));
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(!output.status.success(), "{}", output_details(&output));
    assert!(!stdout.contains("Elaboration Error:"));
    assert_eq!(stderr.matches("Resolution Error:").count(), 1);
}

#[test]
fn parse_only_skips_elaboration_but_reports_parse_errors() {
    let fixture = FixtureDirectory::new();
    let root = fixture.write(
        "root.ref",
        "\\module Root { \\definition invalid: \\Prop := \\Set; }\n",
    );
    let output = run_ref_file_with_args(&fixture.0, &root, &["--parse-only"]).unwrap();
    assert!(output.status.success(), "{}", output_details(&output));
    assert!(output.stdout.is_empty(), "{}", output_details(&output));
    assert!(output.stderr.is_empty(), "{}", output_details(&output));

    let root = fixture.write(
        "root.ref",
        "\\module Root { \\definition invalid: \\Prop := ; }\n",
    );
    let output = run_ref_file_with_args(&fixture.0, &root, &["--parse-only"]).unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{}", output_details(&output));
    assert!(output.stdout.is_empty(), "{}", output_details(&output));
    assert!(stderr.contains("Module Load Error:"), "{stderr}");
    assert!(stderr.contains("parse error:"), "{stderr}");
}

#[test]
fn parse_only_follows_external_modules() {
    let fixture = FixtureDirectory::new();
    let root = fixture.write("root.ref", "\\module Child;\n");
    fixture.write("Child.ref", "\\definition invalid: \\Prop := \\Set;\n");

    let output = run_ref_file_with_args(&fixture.0, &root, &["--parse-only"]).unwrap();
    assert!(output.status.success(), "{}", output_details(&output));

    fixture.write("Child.ref", "\\definition invalid: \\Prop := ;\n");
    let output = run_ref_file_with_args(&fixture.0, &root, &["--parse-only"]).unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{}", output_details(&output));
    assert!(stderr.contains("Child.ref"), "{stderr}");
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

#[test]
fn goals_show_context_constraints_and_source() {
    let workspace = workspace_root();
    let path = workspace.join("tests/ng/metavariables/contextual_unsolved_goal.ref");
    let output = run_ref_file(&workspace, &path).unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1));
    for expected in [
        "context:",
        "goal:",
        "constraints:",
        "contextual_unsolved_goal.ref:",
        "^",
    ] {
        assert!(stderr.contains(expected), "missing {expected}: {stderr}");
    }
    assert!(!stderr.contains('\x1b'));
}

#[test]
fn external_module_diagnostics_use_the_original_file() {
    let fixture = FixtureDirectory::new();
    let root = fixture.write("root.ref", "\\module Child;\n");
    fixture.write(
        "Child.ref",
        "/* 日本語 */\n\\definition bad: \\Prop := \\Set;\n",
    );
    let output = run_ref_file(&fixture.0, &root).unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr.contains("Child.ref:2:1"), "{stderr}");
    assert!(stderr.contains("\\definition bad:"), "{stderr}");

    fixture.write("Child.ref", "\\definition bad: \\Prop := ;\n");
    let output = run_ref_file(&fixture.0, &root).unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("Module Load Error:"), "{stderr}");
    assert!(stderr.contains("Child.ref:1:"), "{stderr}");
    assert!(stderr.contains('^'), "{stderr}");
}

#[test]
fn external_module_parameter_error_uses_the_header_file() {
    let fixture = FixtureDirectory::new();
    let root = fixture.write("root.ref", "\n\\module Child(A: _);\n");
    fixture.write("Child.ref", "");
    let output = run_ref_file(&fixture.0, &root).unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("root.ref:2:1"), "{stderr}");
    assert!(stderr.contains("implicit metavariable"), "{stderr}");
}

#[test]
fn external_program_module_parameters_are_instantiated_in_nested_modules() {
    let fixture = FixtureDirectory::new();
    let root = fixture.write(
        "root.ref",
        r#"
\module Source(X: \VType, x: X);
\module Consumer {
  \inductive Unit: \VType := | unit: Unit;
  \import \root.Source[X := Unit, x := Unit::unit] \as S;
  \import \root.Source[X := Unit, x := Unit::unit].Child[] \as C;
  \vcheck S.value: Unit;
  \ccheck S.result: \F(Unit);
  \vcheck C.value: Unit;
  \definition package: \Box[\F(Unit)] := \box[\F(Unit)](\return(C.value));
  \normalize \squash[\F(Unit)](package);
}
"#,
    );
    fixture.write(
        "Source.ref",
        r#"
\definition value: X := x;
\definition result: \F(X) := \return x;
\module Child;
"#,
    );
    fixture.write("Source/Child.ref", "\\definition value: X := x;\n");

    let output = run_ref_file(&fixture.0, &root).unwrap();
    assert!(output.status.success(), "{}", output_details(&output));
}

#[test]
fn external_child_module_inherits_parent_import_aliases() {
    let fixture = FixtureDirectory::new();
    let root = fixture.write(
        "root.ref",
        r#"
\module Source {
  \definition value: \Prop := \forall (P: \Prop) -> P -> P;
}
\module Parent;
"#,
    );
    fixture.write(
        "Parent.ref",
        r#"
\import \root.Source[] \as Shared;
\module Child;
"#,
    );
    fixture.write(
        "Parent/Child.ref",
        r#"
\definition inherited: \Prop := Shared.value;
"#,
    );

    let output = run_ref_file(&fixture.0, &root).unwrap();
    assert!(output.status.success(), "{}", output_details(&output));
}

#[test]
fn trace_is_on_stderr_and_preserves_command_output() {
    let workspace = workspace_root();
    let path = workspace.join("tests/ok/general-recursion/finish.ref");
    let normal = run_ref_file(&workspace, &path).unwrap();
    let traced = run_ref_file_with_args(&workspace, &path, &["--trace"]).unwrap();
    assert!(normal.status.success(), "{}", output_details(&normal));
    assert!(traced.status.success(), "{}", output_details(&traced));
    assert_eq!(normal.stdout, traced.stdout);
    assert!(normal.stderr.is_empty());
    let stderr = String::from_utf8_lossy(&traced.stderr);
    assert!(stderr.contains("check_value_type"), "{stderr}");
    assert!(stderr.contains("evaluation finished"), "{stderr}");
    assert!(!stderr.contains('\x1b'));
}

#[test]
fn captures_output_larger_than_a_pipe_buffer() {
    let fixture = FixtureDirectory::new();
    let source = format!(
        "\\module Large {{\n{}}}\n",
        "\\infer \\Set;\n".repeat(10_000)
    );
    let root = fixture.write("root.ref", &source);
    let output = run_ref_file(&fixture.0, &root).unwrap();
    assert!(output.status.success(), "{}", output_details(&output));
    assert!(output.stdout.len() > 65_536);
    assert_eq!(
        String::from_utf8_lossy(&output.stdout).lines().count(),
        10_000
    );
}

#[test]
fn default_cache_is_local_to_the_input_and_reused_from_another_directory() {
    let fixture = FixtureDirectory::new();
    fixture.write("package/ref.toml", "[package]\nname = \"example\"\n");
    let source = r"\module M { \definition P: \Prop := \forall (P: \Prop) -> P -> P; \infer P; }";
    fixture.write("package/src/root.ref", source);
    fixture.write("standalone/root.ref", source);
    for input in ["package", "standalone/root.ref"] {
        let path = fixture.0.join(input);
        let directory = if path.is_dir() {
            &path
        } else {
            path.parent().unwrap()
        };
        let cache = directory.join("refcache");
        let first = run_ref_file_with_args(&fixture.0, &path, &["--cache-stats"]).unwrap();
        assert!(first.status.success(), "{}", output_details(&first));
        assert!(fs::read_dir(&cache).unwrap().any(|entry| {
            entry
                .unwrap()
                .path()
                .extension()
                .is_some_and(|ext| ext == "json")
        }));
        fs::write(cache.join("ignored.ref"), "invalid source").unwrap();
        let warm = run_ref_file_with_args(directory, &path, &["--cache-stats"]).unwrap();
        assert!(warm.status.success(), "{}", output_details(&warm));
        assert_eq!(first.stdout, warm.stdout);
        let statistics = String::from_utf8_lossy(&warm.stderr);
        assert!(!statistics.contains("disk_hits: 0"), "{statistics}");
        assert!(statistics.contains("checked_modules: 0"), "{statistics}");
    }
}

#[test]
fn separate_processes_reuse_checked_results_and_detect_source_changes() {
    let fixture = FixtureDirectory::new();
    let root = fixture.write(
        "root.ref",
        r"\module M { \definition P: \Prop := \forall (P: \Prop) -> P -> P; \infer P; }",
    );
    let cache = fixture.0.join("cache");
    let args = ["--cache-dir", cache.to_str().unwrap(), "--cache-stats"];
    let first = run_ref_file_with_args(&fixture.0, &root, &args).unwrap();
    assert!(first.status.success(), "{}", output_details(&first));
    let warm = run_ref_file_with_args(&fixture.0, &root, &args).unwrap();
    assert!(warm.status.success(), "{}", output_details(&warm));
    assert_eq!(first.stdout, warm.stdout);
    let statistics = String::from_utf8_lossy(&warm.stderr);
    assert!(statistics.contains("disk_hits: 1"), "{statistics}");
    assert!(statistics.contains("checked_modules: 0"), "{statistics}");
    let full = run_ref_file_with_args(
        &fixture.0,
        &root,
        &[
            "--cache-dir",
            cache.to_str().unwrap(),
            "--cache-stats",
            "--full-check",
        ],
    )
    .unwrap();
    assert!(full.status.success(), "{}", output_details(&full));
    assert_eq!(first.stdout, full.stdout);
    let statistics = String::from_utf8_lossy(&full.stderr);
    assert!(statistics.contains("disk_hits: 0"), "{statistics}");
    assert!(statistics.contains("checked_modules: 1"), "{statistics}");
    assert!(statistics.contains("disk_writes: 1"), "{statistics}");
    fixture.write("root.ref", r"\module M { \definition P: \Prop := \Set; }");
    let changed = run_ref_file_with_args(&fixture.0, &root, &args).unwrap();
    assert_eq!(
        changed.status.code(),
        Some(1),
        "{}",
        output_details(&changed)
    );
    let clean = run_ref_file_with_args(&fixture.0, &root, &["--no-cache"]).unwrap();
    assert_eq!(changed.status, clean.status);
    assert_eq!(changed.stdout, clean.stdout);
}
