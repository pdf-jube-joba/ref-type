use crate::error::Error;
use crate::module_loader::{DiskSource, SourceProvider, load_modules_in_scope};
use std::{
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
};
use syntax::syntax::{
    Identifier, Module, ModuleBody, ModuleInstantiatePath, ModuleItem, SourceSpan,
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
pub(crate) struct Package {
    name: String,
    directory: PathBuf,
    pub(crate) dependencies: Vec<(String, PathBuf)>,
}

/// Load path dependencies once per canonical directory and return them before their users.
pub fn load_package(directory: &Path) -> Result<PackageGraph, crate::error::Error> {
    load_package_with(directory, &mut DiskSource)
}

pub fn load_package_with(
    directory: &Path,
    provider: &mut dyn SourceProvider,
) -> Result<PackageGraph, crate::error::Error> {
    let mut loader = Loader::default();
    loader.visit(directory, provider)?;
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
    fn visit(
        &mut self,
        directory: &Path,
        provider: &mut dyn SourceProvider,
    ) -> Result<PackageId, crate::error::Error> {
        let directory = provider.identity(directory)?;
        if let Some(id) = self.loaded.get(&directory) {
            return Ok(*id);
        }
        if !self.active.insert(directory.clone()) {
            return Err(Error::PackageCycle {
                directory: directory.clone(),
            });
        }
        let result = self.visit_new(&directory, provider);
        self.active.remove(&directory);
        result
    }

    fn visit_new(
        &mut self,
        directory: &Path,
        provider: &mut dyn SourceProvider,
    ) -> Result<PackageId, crate::error::Error> {
        let package = read_manifest(directory, provider)?;
        if let Some(previous) = self.names.get(&package.name)
            && previous != directory
        {
            return Err(Error::DuplicatePackage {
                name: package.name.clone(),
                first: previous.clone(),
                second: directory.to_owned(),
            });
        }
        self.names
            .insert(package.name.clone(), directory.to_path_buf());
        let mut available = HashSet::from([package.name.clone()]);
        let mut dependencies = Vec::new();
        for (dependency, path) in &package.dependencies {
            let id = self.visit(path, provider)?;
            let actual = &self.packages[id.0].name;
            if dependency != actual {
                return Err(Error::DependencyNameMismatch {
                    expected: dependency.clone(),
                    actual: actual.clone(),
                    path: path.clone(),
                });
            }
            available.insert(actual.clone());
            dependencies.push(id);
        }
        let source = package.directory.join("src/root.ref");
        let mut children =
            load_modules_in_scope(&source, provider, std::slice::from_ref(&package.name))?;
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

fn read_manifest(
    directory: &Path,
    provider: &mut dyn SourceProvider,
) -> Result<Package, crate::error::Error> {
    let source = provider.read(&directory.join("ref.toml"))?;
    parse_manifest(directory, &source.text)
}

pub(crate) fn parse_manifest(directory: &Path, text: &str) -> Result<Package, crate::error::Error> {
    let path = directory.join("ref.toml");
    let value: toml::Table = toml::from_str(text).map_err(|error| Error::Manifest {
        path: path.clone(),
        source: std::sync::Arc::new(error),
    })?;
    let name = value
        .get("package")
        .and_then(|package| package.get("name"))
        .and_then(toml::Value::as_str)
        .ok_or_else(|| Error::MissingPackageName { path: path.clone() })?;
    if !valid_name(name) {
        return Err(Error::InvalidPackageName {
            name: name.to_owned(),
            path: path.clone(),
        });
    }
    let mut dependencies = Vec::new();
    if let Some(table) = value.get("dependencies") {
        let table = table
            .as_table()
            .ok_or_else(|| Error::DependenciesMustBeTable { path: path.clone() })?;
        for (name, specification) in table {
            if !valid_name(name) {
                return Err(Error::InvalidDependencyName {
                    name: name.clone(),
                    path: path.clone(),
                });
            }
            let specification = specification
                .as_table()
                .ok_or_else(|| Error::DependencyMustUsePath { name: name.clone() })?;
            if specification.len() != 1 {
                return Err(Error::DependencyMustContainOnlyPath { name: name.clone() });
            }
            let dependency_path = specification
                .get("path")
                .and_then(toml::Value::as_str)
                .ok_or_else(|| Error::MissingDependencyPath { name: name.clone() })?;
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
    use syntax::visit::ModulePaths;
    module.visit_module_paths(&mut |path| {
        let replacement = match path {
            ModuleInstantiatePath::FromRoot { calls } => Some((package.to_owned(), calls.clone())),
            ModuleInstantiatePath::FromImport { import_name, calls }
                if available.contains(import_name.as_str()) =>
            {
                Some((import_name.0.clone(), calls.clone()))
            }
            _ => None,
        };
        if let Some((name, calls)) = replacement {
            let mut qualified = vec![(Identifier(name), Vec::new())];
            qualified.extend(calls);
            *path = ModuleInstantiatePath::FromRoot { calls: qualified };
        }
    });
}
