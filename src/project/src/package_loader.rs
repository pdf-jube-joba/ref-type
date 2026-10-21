use crate::error::Error;
use crate::module_loader::{DiskSource, SourceProvider, load_modules_in_scope};
use std::{
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
    sync::Arc,
};
use syntax::syntax::{
    Identifier, Module, ModuleBody, ModuleInstantiatePath, ModuleItem, SourceFile, SourceId,
    SourceSpan,
};

#[derive(Clone)]
pub struct PackageGraph {
    pub packages: Vec<PackageInfo>,
    pub modules: Vec<Module>,
    pub entry_packages: Vec<PackageId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct PackageId(pub usize);

/// Language-level identity of a package instance, independent of graph visit order.
#[derive(
    Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct PackageInstanceId(pub PathBuf);

#[derive(Clone)]
pub struct PackageInfo {
    pub id: PackageId,
    pub name: String,
    pub directory: PathBuf,
    pub dependencies: Vec<PackageId>,
    pub instance: PackageInstanceId,
    pub named_dependencies: Vec<(String, PackageId)>,
    pub manifest: Arc<SourceFile>,
    pub sources: Vec<SourceId>,
}

#[derive(Clone)]
pub(crate) struct Package {
    name: String,
    directory: PathBuf,
    pub(crate) dependencies: Vec<(String, PathBuf)>,
}

pub(crate) struct Manifest {
    pub package: Option<Package>,
    pub workspace: Option<crate::workspace::Workspace>,
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
    let directory = provider.identity(directory)?;
    let manifest = read_manifest(&directory, provider)?;
    let mut entry_packages = Vec::new();
    if manifest.package.is_some() {
        entry_packages.push(loader.visit(&directory, provider)?);
    }
    if let Some(workspace) = manifest.workspace {
        for package in workspace.packages {
            let id = loader.visit(&package, provider)?;
            if !entry_packages.contains(&id) {
                entry_packages.push(id);
            }
        }
    }
    Ok(PackageGraph {
        packages: loader.packages,
        modules: loader.modules,
        entry_packages,
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
        let manifest = provider.read(&directory.join("ref.toml"))?;
        let package = parse_manifest(directory, &manifest.text)?
            .package
            .ok_or_else(|| Error::MissingPackageName {
                path: directory.join("ref.toml"),
            })?;
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
        let mut named_dependencies = Vec::new();
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
            named_dependencies.push((dependency.clone(), id));
        }
        let source = package.directory.join("src/root.ref");
        let mut children =
            load_modules_in_scope(&source, provider, std::slice::from_ref(&package.name))?;
        for child in &mut children {
            qualify_imports(child, &package.name, &available);
        }
        fn source_ids(module: &Module, sources: &mut std::collections::BTreeSet<PathBuf>) {
            for source in [&module.source, &module.header_source]
                .into_iter()
                .flatten()
            {
                sources.insert(source.id.0.clone());
            }
            if let ModuleBody::Inline(items) = &module.body {
                for item in items.iter() {
                    if let ModuleItem::ChildModule { module } = item {
                        source_ids(module, sources);
                    }
                }
            }
        }
        let mut sources = std::collections::BTreeSet::new();
        for child in &children {
            source_ids(child, &mut sources);
        }
        let items = children
            .into_iter()
            .map(|module| ModuleItem::ChildModule {
                module: Box::new(module),
            })
            .collect::<Vec<_>>()
            .into();
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
            instance: PackageInstanceId(directory.to_path_buf()),
            named_dependencies,
            manifest,
            sources: sources.into_iter().map(SourceId).collect(),
        });
        self.loaded.insert(directory.to_path_buf(), id);
        Ok(id)
    }
}

fn read_manifest(
    directory: &Path,
    provider: &mut dyn SourceProvider,
) -> Result<Manifest, crate::error::Error> {
    let source = provider.read(&directory.join("ref.toml"))?;
    parse_manifest(directory, &source.text)
}

pub(crate) fn parse_manifest(
    directory: &Path,
    text: &str,
) -> Result<Manifest, crate::error::Error> {
    let path = directory.join("ref.toml");
    let value: toml::Table = toml::from_str(text).map_err(|error| Error::Manifest {
        path: path.clone(),
        source: std::sync::Arc::new(error),
    })?;
    let workspace = crate::workspace::parse(directory, value.get("workspace"))?;
    let package = if value.contains_key("package") || workspace.is_none() {
        Some(parse_package(directory, &value)?)
    } else {
        None
    };
    Ok(Manifest { package, workspace })
}

fn parse_package(directory: &Path, value: &toml::Table) -> Result<Package, Error> {
    let path = directory.join("ref.toml");
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
