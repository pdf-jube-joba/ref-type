use crate::{
    module_loader::load_modules_from_root,
    syntax::{Identifier, Module, ModuleBody, ModuleInstantiatePath, ModuleItem, SourceSpan},
};
use std::{
    collections::{HashMap, HashSet},
    fs,
    path::{Path, PathBuf},
};

pub struct PackageGraph {
    pub packages: Vec<PackageInfo>,
    pub modules: Vec<Module>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PackageId(pub usize);

pub struct PackageInfo {
    pub id: PackageId,
    pub name: String,
    pub directory: PathBuf,
    pub dependencies: Vec<PackageId>,
}

#[derive(Clone)]
struct Package {
    name: String,
    directory: PathBuf,
    dependencies: Vec<(String, PathBuf)>,
}

/// Load path dependencies once per canonical directory and return them before their users.
pub fn load_package(directory: &Path) -> Result<PackageGraph, String> {
    let mut loader = Loader::default();
    loader.visit(directory)?;
    Ok(PackageGraph {
        packages: loader.packages,
        modules: loader.modules,
    })
}

#[derive(Default)]
struct Loader {
    active: HashSet<PathBuf>,
    loaded: HashMap<PathBuf, PackageId>,
    names: HashMap<String, PathBuf>,
    packages: Vec<PackageInfo>,
    modules: Vec<Module>,
}

impl Loader {
    fn visit(&mut self, directory: &Path) -> Result<PackageId, String> {
        let directory = directory.canonicalize().map_err(|error| {
            format!(
                "cannot open package directory {}: {error}",
                directory.display()
            )
        })?;
        if let Some(id) = self.loaded.get(&directory) {
            return Ok(*id);
        }
        if !self.active.insert(directory.clone()) {
            return Err(format!(
                "cyclic package dependency at {}",
                directory.display()
            ));
        }
        let result = self.visit_new(&directory);
        self.active.remove(&directory);
        result
    }

    fn visit_new(&mut self, directory: &Path) -> Result<PackageId, String> {
        let package = read_manifest(directory)?;
        if let Some(previous) = self.names.get(&package.name)
            && previous != directory
        {
            return Err(format!(
                "package name '{}' is used by both {} and {}",
                package.name,
                previous.display(),
                directory.display()
            ));
        }
        self.names
            .insert(package.name.clone(), directory.to_path_buf());
        let mut available = HashSet::from([package.name.clone()]);
        let mut dependencies = Vec::new();
        for (dependency, path) in &package.dependencies {
            let id = self.visit(path)?;
            let actual = &self.packages[id.0].name;
            if dependency != actual {
                return Err(format!(
                    "dependency '{dependency}' refers to package '{actual}' at {}",
                    path.display()
                ));
            }
            available.insert(actual.clone());
            dependencies.push(id);
        }
        let source = package.directory.join("src/root.ref");
        let mut children = load_modules_from_root(&source)?;
        for child in &mut children {
            qualify_imports(child, &package.name, &available);
        }
        let items = children
            .into_iter()
            .map(|module| ModuleItem::ChildModule {
                module: Box::new(module),
            })
            .collect();
        self.modules.push(Module {
            name: Identifier(package.name.clone()),
            parameters: Vec::new(),
            body: ModuleBody::Inline(items),
            span: SourceSpan { start: 0, end: 0 },
            declaration_spans: Vec::new(),
            source: None,
            header_source: None,
        });
        let id = PackageId(self.packages.len());
        self.packages.push(PackageInfo {
            id,
            name: package.name,
            directory: directory.to_path_buf(),
            dependencies,
        });
        self.loaded.insert(directory.to_path_buf(), id);
        Ok(id)
    }
}

fn read_manifest(directory: &Path) -> Result<Package, String> {
    let path = directory.join("ref.toml");
    let source = fs::read_to_string(&path)
        .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    let value: toml::Table =
        toml::from_str(&source).map_err(|error| format!("invalid {}: {error}", path.display()))?;
    let name = value
        .get("package")
        .and_then(|package| package.get("name"))
        .and_then(toml::Value::as_str)
        .ok_or_else(|| format!("{} requires [package].name", path.display()))?;
    if !valid_name(name) {
        return Err(format!(
            "invalid package name '{name}' in {}",
            path.display()
        ));
    }
    let mut dependencies = Vec::new();
    if let Some(table) = value.get("dependencies") {
        let table = table
            .as_table()
            .ok_or_else(|| format!("[dependencies] must be a table in {}", path.display()))?;
        for (name, specification) in table {
            if !valid_name(name) {
                return Err(format!(
                    "invalid dependency name '{name}' in {}",
                    path.display()
                ));
            }
            let specification = specification
                .as_table()
                .ok_or_else(|| format!("dependency '{name}' must use {{ path = ... }}"))?;
            if specification.len() != 1 {
                return Err(format!("dependency '{name}' must contain only path"));
            }
            let dependency_path = specification
                .get("path")
                .and_then(toml::Value::as_str)
                .ok_or_else(|| format!("dependency '{name}' requires a path"))?;
            dependencies.push((name.clone(), directory.join(dependency_path)));
        }
    }
    Ok(Package {
        name: name.into(),
        directory: directory.into(),
        dependencies,
    })
}

fn valid_name(name: &str) -> bool {
    let mut characters = name.chars();
    characters
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic())
        && characters.all(|character| character.is_ascii_alphanumeric() || character == '_')
}

fn qualify_imports(module: &mut Module, package: &str, available: &HashSet<String>) {
    let ModuleBody::Inline(items) = &mut module.body else {
        return;
    };
    for item in items {
        match item {
            ModuleItem::ChildModule { module } => qualify_imports(module, package, available),
            ModuleItem::Import { path, .. } => {
                let replacement = match path {
                    ModuleInstantiatePath::FromRoot { calls } => {
                        Some((package.to_owned(), calls.clone()))
                    }
                    ModuleInstantiatePath::FromImport { import_name, calls }
                        if available.contains(import_name.as_str()) =>
                    {
                        Some((import_name.0.clone(), calls.clone()))
                    }
                    _ => None,
                };
                if let Some((name, calls)) = replacement {
                    let mut qualified = Vec::with_capacity(calls.len() + 1);
                    qualified.push((Identifier(name), Vec::new()));
                    qualified.extend(calls);
                    *path = ModuleInstantiatePath::FromRoot { calls: qualified };
                }
            }
            _ => {}
        }
    }
}
