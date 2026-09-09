use std::{
    fs,
    io::Read,
    path::{Path, PathBuf},
    process::{Command, Output},
    thread,
    time::{Duration, Instant},
};

const PROCESS_TIMEOUT: Duration = Duration::from_secs(20);
// These projects elaborate and independently check the entire library. Allow
// for both debug-build processes running concurrently in the test harness.
const LIBRARY_TIMEOUT: Duration = Duration::from_secs(60);

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
fn library_root_succeeds() {
    let workspace = workspace_root();
    let path = workspace.join("lib/root.ref");
    let output = run_ref_file_with_timeout(&workspace, &path, &[], LIBRARY_TIMEOUT)
        .unwrap_or_else(|error| panic!("{error}"));

    assert!(
        output.status.success(),
        "{} was expected to succeed\n{}",
        path.display(),
        output_details(&output),
    );
}

#[test]
fn library_arithmetic_examples_succeed() {
    let workspace = workspace_root();
    let path = workspace.join("lib/tests.ref");
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
fn file_errors_are_only_written_to_stderr() {
    let workspace = workspace_root();
    let path = workspace.join("tests/ng/param_free.ref");
    let output = run_ref_file(&workspace, &path).unwrap_or_else(|error| panic!("{error}"));
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(!output.status.success(), "{}", output_details(&output));
    assert!(!stdout.contains("Elaboration Error:"));
    assert_eq!(stderr.matches("Elaboration Error:").count(), 1);
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
  \inductive Unit: \VType := | unit: Unit; ;
  \import \root.Source(X := Unit, x := Unit::unit) \as S;
  \import \root.Source(X := Unit, x := Unit::unit).Child() \as C;
  \vcheck S.value: Unit;
  \ccheck S.result: \F(Unit);
  \vcheck C.value: Unit;
  \definition package: \Box(Unit) := \box(Unit, C.value);
  \normalize \Force(Unit, package);
}
"#,
    );
    fixture.write(
        "Source.ref",
        r#"
\vdefinition value: X := x;
\cdefinition result: \F(X) := \return x;
\module Child;
"#,
    );
    fixture.write("Source/Child.ref", "\\vdefinition value: X := x;\n");

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
