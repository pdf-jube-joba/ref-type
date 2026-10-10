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
// The topology project also checks finite-dimensional algebra and quotient
// homotopies; a cold dependency cache can exceed three minutes.
const TOPOLOGICAL_K_THEORY_TIMEOUT: Duration = Duration::from_secs(600);
// Smooth atlas saturation can also check cold analysis and chart dependencies.
const MANIFOLDS_DE_RHAM_TIMEOUT: Duration = Duration::from_secs(3600);
static LIBRARY_CHECK: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn library_check() -> std::sync::MutexGuard<'static, ()> {
    // This mutex only serializes child processes; a failed test leaves no shared data.
    LIBRARY_CHECK
        .lock()
        .unwrap_or_else(|error| error.into_inner())
}

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
    let _check = library_check();
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
fn topological_k_theory_foundations_examples_succeed() {
    let _check = library_check();
    let workspace = workspace_root();
    let path = workspace.join("tests/projects/topological-k-theory");
    let output = run_ref_file_with_timeout(
        &workspace,
        &path,
        &["--full-check-local"],
        TOPOLOGICAL_K_THEORY_TIMEOUT,
    )
    .unwrap_or_else(|error| panic!("{error}"));
    assert!(output.status.success(), "{}", output_details(&output));
}

#[test]
fn manifolds_de_rham_examples_succeed() {
    let _check = library_check();
    let workspace = workspace_root();
    let path = workspace.join("tests/projects/manifolds-de-rham");
    let output = run_ref_file_with_timeout(
        &workspace,
        &path,
        &["--module", "manifolds_de_rham_tests", "--full-check-local"],
        MANIFOLDS_DE_RHAM_TIMEOUT,
    )
    .unwrap_or_else(|error| panic!("{error}"));
    assert!(output.status.success(), "{}", output_details(&output));
}

#[test]
fn pointwise_quotient_representations_succeed() {
    let _check = library_check();
    let workspace = workspace_root();
    for representation in [
        "01-direct-type",
        "02-function-alias",
        "03-explicit-lambda",
        "04-scoped-lambda",
        "05-alias-equality",
    ] {
        let path = workspace
            .join("tests/projects/pointwise-quotient")
            .join(representation);
        let output = run_ref_file_with_timeout(&workspace, &path, &["--no-cache"], LIBRARY_TIMEOUT)
            .unwrap_or_else(|error| panic!("{error}"));
        assert!(output.status.success(), "{}", output_details(&output));
    }
}

#[test]
fn product_compactness_specialization_succeeds() {
    let _check = library_check();
    let workspace = workspace_root();
    let path = workspace.join("tests/projects/product-compactness");
    let output = run_ref_file_with_timeout(&workspace, &path, &["--no-cache"], LIBRARY_TIMEOUT)
        .unwrap_or_else(|error| panic!("{error}"));
    assert!(output.status.success(), "{}", output_details(&output));
}

#[test]
fn category_examples_succeed() {
    let _check = library_check();
    let workspace = workspace_root();
    let path = workspace.join("tests/projects/category");
    let output = run_ref_file_with_timeout(&workspace, &path, &[], LIBRARY_TIMEOUT)
        .unwrap_or_else(|error| panic!("{error}"));
    assert!(output.status.success(), "{}", output_details(&output));
}

#[test]
fn module_expression_library_examples_succeed() {
    let _check = library_check();
    let workspace = workspace_root();
    let path = workspace.join("tests/projects/module-expressions");
    let output = run_ref_file_with_timeout(
        &workspace,
        &path,
        &["--no-cache"],
        TOPOLOGICAL_K_THEORY_TIMEOUT,
    )
    .unwrap_or_else(|error| panic!("{error}"));
    assert!(output.status.success(), "{}", output_details(&output));
}

#[test]
fn packages_resolve_temporary_module_expressions() {
    let fixture = FixtureDirectory::new();
    fixture.write("shared/ref.toml", "[package]\nname = \"shared\"\n");
    fixture.write(
        "shared/src/root.ref",
        r"\module Family(A: \Set) { \definition Carrier: \Set := A; }",
    );
    fixture.write(
        "main/ref.toml",
        "[package]\nname = \"main\"\n[dependencies]\nshared = { path = \"../shared\" }\n",
    );
    fixture.write(
        "main/src/root.ref",
        r"\module Local(A: \Set) { \definition Carrier: \Set := A; }
        \module Consumer {
            \definition dependency(A: \Set): \Set := shared.Family[A := A].Carrier;
            \definition rooted(A: \Set): \Set := \root.Local[A := A].Carrier;
            \definition same(A: \Set)(x: dependency A): rooted A := x;
        }",
    );
    let output =
        run_ref_file_with_args(&workspace_root(), &fixture.0.join("main"), &["--no-cache"])
            .unwrap_or_else(|error| panic!("{error}"));
    assert!(output.status.success(), "{}", output_details(&output));
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
fn module_selection_checks_children_and_reports_missing_modules() {
    let fixture = FixtureDirectory::new();
    let root = fixture.write(
        "root.ref",
        r"\module Good { \definition identity(A: \Set)(x: A): A := x; }
        \module Bad { \module Child { \definition invalid: \Set := \Prop; } }",
    );
    let good = run_ref_file_with_args(&fixture.0, &root, &["--module", "Good"]).unwrap();
    assert!(good.status.success(), "{}", output_details(&good));
    let bad = run_ref_file_with_args(&fixture.0, &root, &["--module", "Bad"]).unwrap();
    assert_eq!(bad.status.code(), Some(1), "{}", output_details(&bad));
    assert!(String::from_utf8_lossy(&bad.stderr).contains("Elaboration Error:"));
    let missing = run_ref_file_with_args(&fixture.0, &root, &["--module", "Missing"]).unwrap();
    assert_eq!(
        missing.status.code(),
        Some(1),
        "{}",
        output_details(&missing)
    );
    assert!(String::from_utf8_lossy(&missing.stderr).contains("Module Selection Error:"));
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
fn compact_diagnostics_preserve_errors_and_goal_context() {
    let workspace = workspace_root();
    let fixture = FixtureDirectory::new();
    let root = fixture.write("root.ref", "\\module Child;\n");
    fixture.write("Child.ref", "\\definition bad: \\Prop := \\Set;\n");
    for path in [
        root,
        workspace.join("tests/ng/metavariables/contextual_unsolved_goal.ref"),
        workspace.join("tests/ng/metavariables/solved_inspection_program.ref"),
    ] {
        let normal = run_ref_file_with_args(&workspace, &path, &["--no-cache"]).unwrap();
        let compact = run_ref_file_with_environment(
            &workspace,
            &path,
            &["--no-cache"],
            PROCESS_TIMEOUT,
            &[("REF_TYPE_COMPACT_DIAGNOSTICS", "1")],
        )
        .unwrap();
        assert_eq!(normal.status.code(), Some(1));
        assert_eq!(compact.status.code(), normal.status.code());
        let normal = String::from_utf8_lossy(&normal.stderr);
        let compact = String::from_utf8_lossy(&compact.stderr);
        assert!(!compact.contains("constraints:"), "{compact}");
        for line in compact.lines().filter(|line| line.contains(".ref:")) {
            assert!(normal.contains(line), "source location changed: {compact}");
        }
        assert!(compact.contains('^'), "{compact}");
        if path.ends_with("contextual_unsolved_goal.ref")
            || path.ends_with("solved_inspection_program.ref")
        {
            assert!(normal.contains("constraints:"), "{normal}");
            for expected in ["inspection hole", "context:", "goal:", "A:"] {
                assert!(compact.contains(expected), "missing {expected}: {compact}");
            }
            let expected = if path.ends_with("contextual_unsolved_goal.ref") {
                "x:"
            } else {
                "solution:"
            };
            assert!(compact.contains(expected), "missing {expected}: {compact}");
        } else {
            assert!(normal.contains("[Failed]"), "{normal}");
            assert!(!compact.contains("[Failed]"), "{compact}");
            assert!(compact.contains("Child.ref:1:1"), "{compact}");
            // The first error line must retain the original failure message.
            let error = compact
                .lines()
                .find(|line| line.contains("Error:"))
                .unwrap();
            assert!(normal.contains(error), "error message changed: {compact}");
        }
    }
}

#[test]
fn compact_diagnostics_return_the_first_error_without_rechecking_other_modules() {
    let fixture = FixtureDirectory::new();
    let root = fixture.write("root.ref", "\\module First;\n\\module Second;\n");
    for name in ["First.ref", "Second.ref"] {
        fixture.write(name, "\\definition bad: \\Prop := \\Set;\n");
    }
    let normal = run_ref_file(&fixture.0, &root).unwrap();
    let compact = run_ref_file_with_environment(
        &fixture.0,
        &root,
        &[],
        PROCESS_TIMEOUT,
        &[("REF_TYPE_COMPACT_DIAGNOSTICS", "1")],
    )
    .unwrap();
    assert_eq!(normal.status.code(), Some(1));
    assert_eq!(compact.status.code(), normal.status.code());
    let normal = String::from_utf8_lossy(&normal.stderr);
    let compact = String::from_utf8_lossy(&compact.stderr);
    assert!(normal.contains("First.ref:1:1"), "{normal}");
    assert!(normal.contains("Second.ref:1:1"), "{normal}");
    assert!(compact.contains("First.ref:1:1"), "{compact}");
    assert!(!compact.contains("Second.ref:"), "{compact}");
}

#[test]
fn compact_parse_errors_skip_independent_typechecking() {
    let fixture = FixtureDirectory::new();
    let root = fixture.write("root.ref", "\\module Broken;\n\\module Good;\n");
    fixture.write("Broken.ref", "\\definition bad: \\Prop := ;\n");
    fixture.write("Good.ref", "\\infer \\Set;\n");
    let normal = run_ref_file(&fixture.0, &root).unwrap();
    let compact = run_ref_file_with_environment(
        &fixture.0,
        &root,
        &[],
        PROCESS_TIMEOUT,
        &[("REF_TYPE_COMPACT_DIAGNOSTICS", "1")],
    )
    .unwrap();
    assert_eq!(normal.status.code(), Some(1));
    assert_eq!(compact.status.code(), normal.status.code());
    assert!(String::from_utf8_lossy(&normal.stdout).contains("\\Set"));
    assert!(compact.stdout.is_empty());
    let normal = String::from_utf8_lossy(&normal.stderr);
    let compact = String::from_utf8_lossy(&compact.stderr);
    assert!(compact.contains("Broken.ref:1:"), "{compact}");
    let diagnostic_lines = |text: &str| {
        text.lines()
            .filter(|line| {
                !line.starts_with("check ")
                    && !line.starts_with("skip ")
                    && !line.starts_with("shared (")
                    && !line.starts_with("total (")
            })
            .map(str::to_owned)
            .collect::<Vec<_>>()
    };
    assert_eq!(diagnostic_lines(&compact), diagnostic_lines(&normal));
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
  \check S.value: Unit;
  \check S.result: \F(Unit);
  \check C.value: Unit;
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
    assert!(
        String::from_utf8_lossy(&normal.stderr)
            .lines()
            .all(|line| line.starts_with("check ")
                || line.starts_with("skip ")
                || line.starts_with("shared (")
                || line.starts_with("total ("))
    );
    let stderr = String::from_utf8_lossy(&traced.stderr);
    assert!(stderr.contains("kernel_check"), "{stderr}");
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

#[test]
fn separate_processes_restore_dependency_environments_after_an_edit() {
    let fixture = FixtureDirectory::new();
    let root = fixture.write("root.ref", r"\module Base; \module Use;");
    fixture.write(
        "Base.ref",
        r"\inductive Unit: \Set := | unit: Unit; \definition value: Unit := Unit::unit;",
    );
    fixture.write("Use.ref", r"\import \root.Base[] \as B; \infer B.value;");
    let cache = fixture.0.join("cache");
    let args = ["--cache-dir", cache.to_str().unwrap(), "--cache-stats"];
    let first = run_ref_file_with_args(&fixture.0, &root, &args).unwrap();
    assert!(first.status.success(), "{}", output_details(&first));
    fixture.write(
        "Use.ref",
        r"\import \root.Base[] \as B; \definition copy: B.Unit := B.value; \normalize copy;",
    );
    let changed = run_ref_file_with_args(&fixture.0, &root, &args).unwrap();
    assert!(changed.status.success(), "{}", output_details(&changed));
    let stats = String::from_utf8_lossy(&changed.stderr);
    assert!(stats.contains("checked_modules: 1"), "{stats}");
    assert!(stats.contains("environment_hits: 1"), "{stats}");
    let clean =
        run_ref_file_with_args(&fixture.0, &root, &["--no-cache", "--cache-stats"]).unwrap();
    assert!(clean.status.success(), "{}", output_details(&clean));
    assert_eq!(changed.stdout, clean.stdout);
    assert!(String::from_utf8_lossy(&clean.stderr).contains("environment_bytes: 0"));
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
fn full_check_local_stops_at_a_cached_dependency_and_detects_its_own_edits() {
    let fixture = FixtureDirectory::new();
    let root = dependency_chain(&fixture);
    let first = run_ref_file_with_args(&fixture.0, &root, &["--full-check-local"]).unwrap();
    assert!(first.status.success(), "{}", output_details(&first));
    assert!(
        progress_lines(&first)
            .iter()
            .any(|line| line.starts_with("check a.Base "))
    );
    // Invalid UTF-8 proves that the transitive source is not read at all.
    fs::write(fixture.0.join("a/src/Base.ref"), [0xff]).unwrap();
    let cached =
        run_ref_file_with_args(&fixture.0, &root, &["--full-check-local", "--cache-stats"])
            .unwrap();
    assert!(cached.status.success(), "{}", output_details(&cached));
    assert_eq!(first.stdout, cached.stdout);
    let lines = progress_lines(&cached);
    assert!(
        lines.iter().any(|line| line.starts_with("skip a.Base ")),
        "{lines:?}"
    );
    assert!(
        lines.iter().any(|line| line.starts_with("skip b.Bridge ")),
        "{lines:?}"
    );
    assert!(
        lines.iter().any(|line| line.starts_with("check c.Client ")),
        "{lines:?}"
    );
    assert!(
        String::from_utf8_lossy(&cached.stderr).contains("environment_hits: 1"),
        "{}",
        output_details(&cached)
    );
    for args in [vec![], vec!["--full-check"], vec!["--no-cache"]] {
        let output = run_ref_file_with_args(&fixture.0, &root, &args).unwrap();
        assert_eq!(output.status.code(), Some(1), "{}", output_details(&output));
        assert!(String::from_utf8_lossy(&output.stderr).contains("Base.ref"));
    }
    fixture.write("c/ref.toml", "[package]\nname = \"c\"\n[dependencies]\na = { path = \"../a\" }\nb = { path = \"../b\" }\n");
    let direct = run_ref_file_with_args(&fixture.0, &root, &["--full-check-local"]).unwrap();
    assert_eq!(direct.status.code(), Some(1), "{}", output_details(&direct));
    assert!(String::from_utf8_lossy(&direct.stderr).contains("Base.ref"));
    fixture.write(
        "c/ref.toml",
        "[package]\nname = \"c\"\n[dependencies]\nb = { path = \"../b\" }\n",
    );
    fixture.write(
        "b/src/root.ref",
        r"\module Bridge { \import a.Base[] \as A; \definition P: \Prop := A.P; \infer P; }",
    );
    let changed = run_ref_file_with_args(&fixture.0, &root, &["--full-check-local"]).unwrap();
    assert_eq!(
        changed.status.code(),
        Some(1),
        "{}",
        output_details(&changed)
    );
    assert!(String::from_utf8_lossy(&changed.stderr).contains("Base.ref"));
    fixture.write(
        "a/src/Base.ref",
        r"\definition P: \Prop := \forall (P: \Prop) -> P -> P;",
    );
    let changed = run_ref_file_with_args(&fixture.0, &root, &["--full-check-local"]).unwrap();
    assert!(changed.status.success(), "{}", output_details(&changed));
    assert!(
        progress_lines(&changed)
            .iter()
            .any(|line| line.starts_with("check b.Bridge "))
    );
    fixture.write(
        "c/src/root.ref",
        r"\module Client { \definition bad: \Prop := \Set; }",
    );
    let invalid = run_ref_file_with_args(&fixture.0, &root, &["--full-check-local"]).unwrap();
    assert_eq!(
        invalid.status.code(),
        Some(1),
        "{}",
        output_details(&invalid)
    );
    assert!(
        progress_lines(&invalid)
            .iter()
            .any(|line| line.starts_with("check c.Client "))
    );
}

#[test]
fn damaged_dependency_source_cache_falls_back_to_current_sources() {
    let fixture = FixtureDirectory::new();
    let root = dependency_chain(&fixture);
    fixture.write("c/unloaded/ref.toml", "[package]\nname = \"unloaded\"\n");
    fixture.write("c/unloaded/src/root.ref", "invalid syntax");
    let first = run_ref_file(&fixture.0, &root).unwrap();
    assert!(first.status.success(), "{}", output_details(&first));
    let mut source_records = 0;
    for entry in fs::read_dir(root.join("refcache")).unwrap() {
        let path = entry.unwrap().path();
        if path.to_string_lossy().ends_with(".sources.json") {
            source_records += 1;
            fs::write(path, "truncated").unwrap();
        }
    }
    assert_eq!(source_records, 3);
    fixture.write("a/src/Base.ref", r"\definition P: \Prop := \Set;");
    let output = run_ref_file_with_args(&fixture.0, &root, &["--full-check-local"]).unwrap();
    assert_eq!(output.status.code(), Some(1), "{}", output_details(&output));
    assert!(String::from_utf8_lossy(&output.stderr).contains("Base.ref:1:"));
}

#[test]
fn diagnostic_cli_options_override_the_environment() {
    let workspace = workspace_root();
    let path = workspace.join("tests/ng/metavariables/contextual_unsolved_goal.ref");
    for (mode, environment, detailed) in [("compact", "0", false), ("detailed", "1", true)] {
        let result = run_ref_file_with_environment(
            &workspace,
            &path,
            &["--no-cache", "--diagnostics", mode],
            PROCESS_TIMEOUT,
            &[
                ("REF_TYPE_COMPACT_DIAGNOSTICS", environment),
                ("REF_TYPE_PROFILE_DIAGNOSTICS", "1"),
            ],
        )
        .unwrap();
        assert_eq!(result.status.code(), Some(1));
        let stderr = String::from_utf8_lossy(&result.stderr);
        assert_eq!(stderr.contains("constraints:"), detailed, "{stderr}");
        for expected in ["context:", "goal:", "diagnostics phase=", "rss_delta_kib="] {
            assert!(stderr.contains(expected), "{stderr}");
        }
    }
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
fn structure_result_arrows_check_lambdas_and_their_applications() {
    let fixture = FixtureDirectory::new();
    let root = fixture.write(
        "root.ref",
        r"\module Playground(Carrier: \Set, x: Carrier) {
  \structure A[Carrier: \Set] { a: Carrier }
  \structure B[Carrier: \Set] { b: Carrier }
  \definition AtoB[Carrier: \Set]: A[Carrier] -> B[Carrier] :=
    \fun (data: A[Carrier]) => B[Carrier] { b := data.a };
  \definition choose[Carrier: \Set]: A[Carrier] -> A[Carrier] -> B[Carrier] :=
    \fun (left, right: A[Carrier]) => B[Carrier] { b := right.a };
  \definition make[Carrier: \Set]: Carrier -> B[Carrier] :=
    \fun (value: Carrier) => B[Carrier] { b := value };
  \definition dependent: \forall (Carrier: \Set) -> A[Carrier] -> B[Carrier] :=
    \fun (Carrier: \Set) => \fun (data: A[Carrier]) => B[Carrier] { b := data.a };
  \definition captured: \forall (value: Carrier) -> B[Carrier] :=
    \fun (value: Carrier) => B[Carrier] { b := (\fun (x: Carrier) => value) x };
  \definition input: A[Carrier] := A[Carrier] { a := x };
  \definition output: B[Carrier] := AtoB[Carrier] input;
  \definition chosen: B[Carrier] := choose[Carrier] input input;
  \definition made: B[Carrier] := make[Carrier] x;
  \definition dep: B[Carrier] := dependent Carrier input;
  \definition cap: B[Carrier] := captured x;
  \definition sameDependent: dep.b = x := \refl(x);
  \definition sameCaptured: cap.b = x := \refl(x);
  \definition same: output.b = x := \refl(x);
  \definition sameChosen: chosen.b = x := \refl(x);
  \definition sameMade: made.b = x := \refl(x);
}
",
    );
    let result = run_ref_file_with_args(&fixture.0, &root, &["--no-cache"]).unwrap();
    assert!(result.status.success(), "{}", output_details(&result));
}

#[test]
fn structure_type_projection_diagnostics_explain_value_access_and_keep_the_location() {
    let fixture = FixtureDirectory::new();
    let source = r"\module Playground {
  \structure A: \SetKind {
    Carrier: \Set,
    a: Carrier,
  }

  \structure ALaw {
    data: A,
    some: A.a = A.a,
  }
}";
    let root = fixture.write("root.ref", source);
    let result = run_ref_file_with_args(&fixture.0, &root, &["--no-cache"]).unwrap();
    assert_eq!(result.status.code(), Some(1), "{}", output_details(&result));
    let stderr = String::from_utf8_lossy(&result.stderr);
    for expected in ["structure type 'A'", "data.a", "A::a", "root.ref:9:", "^^^"] {
        assert!(stderr.contains(expected), "missing {expected}: {stderr}");
    }
    fixture.write("root.ref", &source.replace("A.a = A.a", "data.a = data.a"));
    let valid = run_ref_file_with_args(&fixture.0, &root, &["--no-cache"]).unwrap();
    assert!(valid.status.success(), "{}", output_details(&valid));
}

#[test]
fn generated_projection_diagnostics_show_the_rejected_product_sorts() {
    let fixture = FixtureDirectory::new();
    let root = fixture.write(
        "root.ref",
        r"\module M { \structure Bad: \Prop { b: \Prop } }",
    );
    for mode in ["compact", "detailed"] {
        let result =
            run_ref_file_with_args(&fixture.0, &root, &["--no-cache", "--diagnostics", mode])
                .unwrap();
        assert_eq!(result.status.code(), Some(1), "{}", output_details(&result));
        let stderr = String::from_utf8_lossy(&result.stderr);
        for expected in [
            "Generated projection b",
            r"domain \Prop and body \PropKind",
            "root.ref:1:",
        ] {
            assert!(stderr.contains(expected), "missing {expected}: {stderr}");
        }
    }
}

#[test]
fn structure_result_lambdas_check_their_parameter_annotations() {
    let fixture = FixtureDirectory::new();
    let root = fixture.write(
        "root.ref",
        r"\module M(A: \Set, B: \Set) {
  \structure Box[Carrier: \Set] { value: Carrier }
  \definition bad: A -> Box[B] := \fun (value: B) => Box[B] { value := value };
}",
    );
    let result = run_ref_file_with_args(&fixture.0, &root, &["--no-cache"]).unwrap();
    assert_eq!(result.status.code(), Some(1), "{}", output_details(&result));
    let stderr = String::from_utf8_lossy(&result.stderr);
    assert!(stderr.contains("not convertible"), "{stderr}");
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

#[test]
fn separate_processes_restore_set_transport_with_aliased_macros() {
    let fixture = FixtureDirectory::new();
    let source = r"\module T(A: \Set, F: A -> \Set) {
      \macro identity($a, $u) := \transporteq $a \with x: _ => F x \by { base: $u };
    }
    \module M(A: \Set, F: A -> \Set, a: A, u: F a) {
      \definition cast: F a := \idelim a = a \with x: _ => F x \by { base: u, equality: \refl(a) };
      \definition identity: cast = u := self!{a u};
      \use \root.T[A := A, F := F]::identity \as self;
    }
    \module N(A: \Set, F: A -> \Set, a: A, u: F a) {
      \import \root.M[A := A, F := F, a := a, u := u] \as M;
      \definition law: M.cast = u := M.identity;
    }";
    let root = fixture.write("root.ref", source);
    let cache = fixture.0.join("cache");
    let args = ["--cache-dir", cache.to_str().unwrap(), "--cache-stats"];
    let first = run_ref_file_with_args(&fixture.0, &root, &args).unwrap();
    assert!(first.status.success(), "{}", output_details(&first));
    let warm = run_ref_file_with_args(&fixture.0, &root, &args).unwrap();
    assert!(warm.status.success(), "{}", output_details(&warm));
    assert!(String::from_utf8_lossy(&warm.stderr).contains("checked_modules: 0"));
    fixture.write(
        "root.ref",
        &source.replace("\\definition law:", "\\definition law2:"),
    );
    let restored = run_ref_file_with_args(&fixture.0, &root, &args).unwrap();
    assert!(restored.status.success(), "{}", output_details(&restored));
    let clean = run_ref_file_with_args(&fixture.0, &root, &["--no-cache"]).unwrap();
    assert!(clean.status.success(), "{}", output_details(&clean));
    assert_eq!(restored.stdout, clean.stdout);
}
