use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

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

fn run_ref_file(workspace: &Path, path: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_cli"))
        .arg("file")
        .arg(path)
        .current_dir(workspace)
        .output()
        .unwrap_or_else(|error| panic!("failed to run {}: {error}", path.display()))
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
        let output = run_ref_file(&workspace, &path);
        if output.status.success() != should_succeed {
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
    let output = run_ref_file(&workspace, &path);

    assert!(
        output.status.success(),
        "{} was expected to succeed\n{}",
        path.display(),
        output_details(&output),
    );
}
