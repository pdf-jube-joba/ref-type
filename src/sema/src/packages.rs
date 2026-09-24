//! Local package inputs and package-qualified module resolution.
use super::{
    Diagnostic, FileSnapshot, Location,
    tree::{ModuleTree, attach_source},
};
use std::{
    collections::{BTreeMap, HashMap},
    path::{Path, PathBuf},
    sync::Arc,
};
use syntax::{Identifier, Module, ModuleBody, ModuleInstantiatePath, ModuleItem, SourceSpan};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PackageId(pub u64);

impl PackageId {
    pub(crate) fn module_name(self) -> String {
        format!("$package{}", self.0)
    }
    pub(crate) fn from_module_name(name: &str) -> Option<Self> {
        name.strip_prefix("$package")?.parse().ok().map(Self)
    }
}

#[derive(Debug, Clone)]
pub struct Package {
    pub id: PackageId,
    pub name: String,
    pub manifest: Location,
    pub root: PathBuf,
    pub dependencies: BTreeMap<String, PackageId>,
}

#[derive(Debug, Clone, Default)]
pub struct PackageGraph {
    pub root: Option<PackageId>,
    pub packages: BTreeMap<PackageId, Package>,
}

struct Manifest {
    name: String,
    dependencies: BTreeMap<String, String>,
}

fn manifest(text: &str) -> Result<Manifest, String> {
    let value = text
        .parse::<toml::Table>()
        .map_err(|error| error.to_string())?;
    for key in value.keys() {
        if !matches!(key.as_str(), "package" | "dependencies") {
            return Err(format!("unknown manifest entry '{key}'"));
        }
    }
    let package = value
        .get("package")
        .and_then(toml::Value::as_table)
        .ok_or("expected [package]")?;
    if package.keys().any(|key| key != "name") {
        return Err("[package] accepts only name".into());
    }
    let name = package
        .get("name")
        .and_then(toml::Value::as_str)
        .filter(|name| !name.is_empty())
        .ok_or("expected package.name")?;
    let mut dependencies = BTreeMap::new();
    if let Some(value) = value.get("dependencies") {
        for (alias, value) in value.as_table().ok_or("expected [dependencies]")? {
            if !alias
                .chars()
                .enumerate()
                .all(|(i, c)| c == '_' || c.is_ascii_alphabetic() || i > 0 && c.is_ascii_digit())
                || alias.is_empty()
            {
                return Err(format!("invalid dependency name '{alias}'"));
            }
            let entry = value
                .as_table()
                .ok_or_else(|| format!("dependency '{alias}' requires a path table"))?;
            if entry.len() != 1 || !entry.contains_key("path") {
                return Err(format!("dependency '{alias}' requires only path"));
            }
            let path = entry["path"]
                .as_str()
                .filter(|path| !path.is_empty())
                .ok_or_else(|| format!("dependency '{alias}' requires a nonempty path"))?;
            dependencies.insert(alias.clone(), path.to_owned());
        }
    }
    Ok(Manifest {
        name: name.to_owned(),
        dependencies,
    })
}

impl ModuleTree {
    pub(super) fn load_packages(
        &mut self,
        root: &Path,
        read: &mut impl FnMut(&Path) -> Result<Arc<FileSnapshot>, String>,
    ) {
        self.packages.root =
            self.load_package(root, read, &mut HashMap::new(), &mut Vec::new(), None);
    }

    fn load_package(
        &mut self,
        path: &Path,
        read: &mut impl FnMut(&Path) -> Result<Arc<FileSnapshot>, String>,
        seen: &mut HashMap<PathBuf, PackageId>,
        active: &mut Vec<(PathBuf, Location)>,
        importer: Option<Location>,
    ) -> Option<PackageId> {
        let file = match read(path) {
            Ok(file) => file,
            Err(message) => {
                self.diagnostics
                    .push(Diagnostic::error("package", message, importer));
                return None;
            }
        };
        let location = file.location(SourceSpan {
            start: 0,
            end: file.source.text.len(),
        });
        self.files.insert(file.id, file.clone());
        if let Some(start) = active.iter().position(|(path, _)| *path == file.identity) {
            let chain = active[start..]
                .iter()
                .map(|(path, _)| path.display().to_string())
                .chain(std::iter::once(file.identity.display().to_string()))
                .collect::<Vec<_>>()
                .join(" -> ");
            let mut diagnostic = Diagnostic::error(
                "package",
                format!("cyclic package dependencies: {chain}"),
                importer.or(Some(location)),
            );
            diagnostic.secondary = active[start..]
                .iter()
                .map(|(_, location)| (*location, "package in dependency cycle".into()))
                .collect();
            self.diagnostics.push(diagnostic);
            return None;
        }
        if let Some(id) = seen.get(&file.identity) {
            return Some(*id);
        }
        let manifest = match manifest(&file.source.text) {
            Ok(manifest) => manifest,
            Err(message) => {
                self.diagnostics
                    .push(Diagnostic::error("package", message, Some(location)));
                return None;
            }
        };
        let id = PackageId(file.id.0);
        seen.insert(file.identity.clone(), id);
        active.push((file.identity.clone(), location));
        let directory = file.source.id.0.parent().unwrap();
        let mut dependencies = BTreeMap::new();
        for (alias, path) in manifest.dependencies {
            let path = directory.join(path).join("ref.toml");
            if let Some(target) = self.load_package(&path, read, seen, active, Some(location)) {
                dependencies.insert(alias, target);
            }
        }
        active.pop();
        let root = directory.join("src/root.ref");
        self.packages.packages.insert(
            id,
            Package {
                id,
                name: manifest.name,
                manifest: location,
                root: root.clone(),
                dependencies: dependencies.clone(),
            },
        );
        let source = match read(&root) {
            Ok(file) => file,
            Err(message) => {
                self.diagnostics
                    .push(Diagnostic::error("source", message, Some(location)));
                return Some(id);
            }
        };
        let parsed = self.parse(source.clone(), false);
        let mut items = parsed.items.clone();
        let mut used = HashMap::from([(source.identity.clone(), "package root".to_string())]);
        for item in &mut items {
            if let ModuleItem::ChildModule { module } = item {
                attach_source(module, &source);
                self.resolve(module, &[], root.parent().unwrap(), &mut used, read);
            }
        }
        let mut module = Module {
            name: Identifier::new(id.module_name()),
            parameters: Vec::new(),
            body: ModuleBody::Inline(items),
            span: SourceSpan {
                start: 0,
                end: source.source.text.len(),
            },
            declaration_spans: parsed.item_spans.clone(),
            source: Some(source.source.clone()),
            header_source: None,
        };
        self.resolve_package_imports(&mut module, id, &dependencies, 0);
        self.modules.push(module);
        Some(id)
    }

    fn resolve_package_imports(
        &mut self,
        module: &mut Module,
        id: PackageId,
        dependencies: &BTreeMap<String, PackageId>,
        depth: usize,
    ) {
        let file = module
            .source
            .as_ref()
            .and_then(|source| self.files.values().find(|file| file.source.id == source.id))
            .cloned();
        if let Some(file) = &file {
            self.file_packages.insert(file.id, id);
        }
        let ModuleBody::Inline(items) = &mut module.body else {
            return;
        };
        for (index, item) in items.iter_mut().enumerate() {
            match item {
                ModuleItem::ChildModule { module } => {
                    self.resolve_package_imports(module, id, dependencies, depth + 1)
                }
                ModuleItem::Import { path, import_name } => {
                    let resolution = match path {
                        ModuleInstantiatePath::FromPackage { package, calls } => dependencies
                            .get(package.as_str())
                            .copied()
                            .map(|id| (id, calls.clone()))
                            .ok_or_else(|| {
                                format!(
                                    "dependency '{}' is not declared in ref.toml",
                                    package.as_str()
                                )
                            }),
                        ModuleInstantiatePath::FromRoot { calls } => Ok((id, calls.clone())),
                        ModuleInstantiatePath::FromCurrent { back_parent, .. }
                            if *back_parent > depth =>
                        {
                            Err("parent import escapes the package root".into())
                        }
                        _ => continue,
                    };
                    match resolution {
                        Ok((target, mut calls)) => {
                            calls.insert(0, (Identifier::new(target.module_name()), Vec::new()));
                            *path = ModuleInstantiatePath::FromRoot { calls };
                        }
                        Err(message) => {
                            let location = file
                                .as_ref()
                                .map(|file| file.location(module.declaration_spans[index]));
                            self.diagnostics.push(Diagnostic::error(
                                "package",
                                message.clone(),
                                location,
                            ));
                            *item = ModuleItem::Error {
                                name: Some(import_name.clone()),
                                message,
                            };
                        }
                    }
                }
                _ => {}
            }
        }
    }
}
