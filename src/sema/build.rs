use sha2::{Digest, Sha256};
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

fn collect(path: &Path, files: &mut Vec<PathBuf>) {
    if path.is_dir() {
        println!("cargo:rerun-if-changed={}", path.display());
        for entry in fs::read_dir(path).unwrap() {
            collect(&entry.unwrap().path(), files);
        }
    } else if path.extension().is_some_and(|extension| extension == "rs")
        || path.file_name().is_some_and(|name| name == "Cargo.toml")
    {
        files.push(path.to_owned());
    }
}
fn main() {
    let root = PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").unwrap()).join("../..");
    let mut files = vec![root.join("Cargo.lock"), root.join("Cargo.toml")];
    for name in [
        "kernel",
        "syntax",
        "project",
        "resolve",
        "elaboration",
        "sema",
    ] {
        collect(&root.join("src").join(name), &mut files);
    }
    files.sort();
    let mut hash = Sha256::new();
    for file in files {
        println!("cargo:rerun-if-changed={}", file.display());
        let bytes = fs::read(file).unwrap();
        hash.update((bytes.len() as u64).to_le_bytes());
        hash.update(bytes);
    }
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".into());
    hash.update(Command::new(rustc).arg("-vV").output().unwrap().stdout);
    hash.update(std::env::var("TARGET").unwrap());
    let revision: String = hash
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect();
    println!("cargo:rustc-env=REF_SEMA_REVISION={revision}");
}
