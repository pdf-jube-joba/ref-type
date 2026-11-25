//! Resolver-only measurement: cargo run --manifest-path benchmarks/Cargo.toml --bin resolve-bench -- PATH
use std::{path::Path, time::Instant};

fn main() {
    let mut arguments = std::env::args().skip(1);
    let path = arguments.next().expect("package or .ref path");
    assert!(arguments.next().is_none(), "expected one benchmark input");
    let started = Instant::now();
    let modules = if path.ends_with(".ref") {
        project::module_loader::load_modules_from_root(Path::new(&path)).unwrap()
    } else {
        project::package_loader::load_package(Path::new(&path))
            .unwrap()
            .modules
    };
    eprintln!("load_ms={}", started.elapsed().as_millis());
    let _costs = timing::costs::Session::start();
    let started = Instant::now();
    let resolved = resolve::resolve(&modules)
        .unwrap_or_else(|error| panic!("{error} at {:?} {:?}", error.module, error.location));
    eprintln!(
        "resolve_ms={} modules={} declarations={} references={}",
        started.elapsed().as_millis(),
        resolved.modules.len(),
        resolved.declarations.len(),
        resolved.references.len()
    );
}
