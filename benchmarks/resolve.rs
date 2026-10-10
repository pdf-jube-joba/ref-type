//! Resolver-only measurement: cargo run -p resolve --example resolve-bench -- libs/std
use std::{path::Path, time::Instant};

/// Predict source-module completion order without running the type checker.
fn completion_order(project: &resolve::Project) {
    use resolve::hir::{Module, ModuleBody, ModuleItem};
    use std::collections::{BTreeMap, HashMap};
    fn collect(
        module: &Module,
        prefix: &mut Vec<String>,
        paths: &mut HashMap<resolve::hir::ModuleId, Vec<String>>,
    ) {
        prefix.push(module.name.0.clone());
        let end = prefix
            .iter()
            .position(|name| name.starts_with('<'))
            .unwrap_or(prefix.len());
        paths.insert(module.id, prefix[..end].to_vec());
        if let ModuleBody::Inline(items) = &module.body {
            for item in items {
                if let ModuleItem::ChildModule { module } = item {
                    collect(module, prefix, paths);
                }
            }
        }
        prefix.pop();
    }
    let mut paths = HashMap::new();
    for module in &project.modules {
        collect(module, &mut Vec::new(), &mut paths);
    }
    let mut last = BTreeMap::new();
    for (position, step) in project.order.iter().enumerate() {
        let id = match step {
            resolve::CheckStep::Parameters(id)
            | resolve::CheckStep::Declaration { module: id, .. } => id,
        };
        last.insert(paths[id].clone(), position);
    }
    let mut ordered: Vec<_> = last.into_iter().collect();
    ordered.sort_by_key(|(_, position)| *position);
    let mut counts = BTreeMap::new();
    for (index, (path, position)) in ordered.into_iter().enumerate() {
        let count = counts.entry(path[0].clone()).or_insert(0);
        *count += 1;
        let next = project
            .order
            .get(position + 1)
            .map(|step| {
                let id = match step {
                    resolve::CheckStep::Parameters(id)
                    | resolve::CheckStep::Declaration { module: id, .. } => id,
                };
                paths[id].join(".")
            })
            .unwrap_or_default();
        println!(
            "complete={} package_complete={count} step={position} module={} next_module={next}",
            index + 1,
            path.join(".")
        );
    }
}

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
    let package_order = std::env::args().any(|arg| arg == "--package-order");
    let resolved = if package_order {
        let mut session = resolve::Session::default();
        let mut resolved = None;
        for module in &modules {
            resolved = Some(session.append(module).unwrap());
        }
        resolved.expect("at least one package")
    } else {
        resolve::resolve(&modules)
            .unwrap_or_else(|error| panic!("{error} at {:?} {:?}", error.module, error.location))
    };
    eprintln!(
        "resolve_ms={} modules={} declarations={} references={}",
        started.elapsed().as_millis(),
        resolved.modules.len(),
        resolved.declarations.len(),
        resolved.references.len()
    );
    if package_order {
        completion_order(&resolved);
    }
}
