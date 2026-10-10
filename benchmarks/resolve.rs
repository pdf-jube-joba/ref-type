//! Resolver-only measurement: cargo run -p resolve --example resolve-bench -- libs/std
use std::{path::Path, time::Instant};

fn main() {
    let path = std::env::args().nth(1).expect("package or .ref path");
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
