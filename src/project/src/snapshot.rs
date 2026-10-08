use ::syntax::syntax::{SourceFile, SourceId};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path, PathBuf},
    sync::Arc,
};

/// An immutable set of source texts, including manifests and unsaved buffers.
/// Queries never read the filesystem through a snapshot.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct SourceSnapshot {
    entry: PathBuf,
    #[serde(with = "source_texts")]
    files: BTreeMap<PathBuf, Arc<SourceFile>>,
    aliases: BTreeMap<PathBuf, PathBuf>,
}

// Checkpoint SourceFile serialization intentionally omits text. Dependency
// snapshots must retain it so transitive packages can be loaded without disk IO.
mod source_texts {
    use super::*;
    use serde::{Deserialize, Serialize};

    pub fn serialize<S: serde::Serializer>(
        files: &BTreeMap<PathBuf, Arc<SourceFile>>,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        files
            .iter()
            .map(|(path, source)| (path, &source.text))
            .collect::<BTreeMap<_, _>>()
            .serialize(serializer)
    }

    pub fn deserialize<'de, D: serde::Deserializer<'de>>(
        deserializer: D,
    ) -> Result<BTreeMap<PathBuf, Arc<SourceFile>>, D::Error> {
        Ok(BTreeMap::<PathBuf, String>::deserialize(deserializer)?
            .into_iter()
            .map(|(path, text)| {
                let source = Arc::new(SourceFile {
                    id: SourceId(path.clone()),
                    text,
                });
                (path, source)
            })
            .collect())
    }
}

pub fn absolute(path: &Path) -> PathBuf {
    let path = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .expect("current directory is available")
            .join(path)
    };
    let mut result = PathBuf::new();
    for part in path.components() {
        match part {
            Component::CurDir => {}
            Component::ParentDir => {
                result.pop();
            }
            part => result.push(part.as_os_str()),
        }
    }
    result
}

impl SourceSnapshot {
    pub fn new(entry: impl AsRef<Path>) -> Self {
        Self {
            entry: absolute(entry.as_ref()),
            files: BTreeMap::new(),
            aliases: BTreeMap::new(),
        }
    }

    /// Capture source trees and path dependencies. A later edit on disk does
    /// not change this snapshot. Invalid syntax is reported by semantic queries.
    pub fn read(entry: impl AsRef<Path>) -> Result<Self, String> {
        Self::read_with_dependency_cache(entry, |_, _| None)
    }

    /// Read each dependency's own tree before consulting a previously checked
    /// snapshot of its transitive dependencies.
    pub fn read_with_dependency_cache(
        entry: impl AsRef<Path>,
        mut cached: impl FnMut(&Self, &Path) -> Option<Self>,
    ) -> Result<Self, String> {
        let mut snapshot = Self::new(entry);
        let mut roots = vec![snapshot.root_directory().to_path_buf()];
        let mut visited = BTreeSet::new();
        while let Some(root) = roots.pop() {
            let identity = root
                .canonicalize()
                .map_err(|e| format!("cannot open {}: {e}", root.display()))?;
            snapshot.aliases.insert(root.clone(), identity.clone());
            if !visited.insert(identity) {
                continue;
            }
            let mut own = Self::new(&root);
            own.aliases.insert(root.clone(), snapshot.identity(&root));
            own.read_tree(&root, &mut BTreeSet::new())?;
            if root != snapshot.root_directory()
                && let Some(saved) = cached(&own, &root)
            {
                // An explicitly visited package wins over a transitive snapshot.
                for (path, source) in saved.files {
                    snapshot.files.entry(path).or_insert(source);
                }
                for (path, identity) in saved.aliases {
                    snapshot.aliases.entry(path).or_insert(identity);
                }
                snapshot.files.extend(own.files);
                snapshot.aliases.extend(own.aliases);
                continue;
            }
            snapshot.files.extend(own.files);
            snapshot.aliases.extend(own.aliases);
            if let Some(source) = snapshot.source(root.join("ref.toml"))
                && let Ok(manifest) = crate::package_loader::parse_manifest(&root, &source.text)
            {
                for (_, path) in manifest.dependencies {
                    roots.push(absolute(&path));
                }
            }
        }
        Ok(snapshot)
    }

    /// Restrict a captured snapshot to one package and its path dependencies.
    pub fn package_snapshot(&self, root: impl AsRef<Path>) -> Self {
        let mut result = Self::new(root);
        let mut pending = vec![result.entry.clone()];
        let mut visited = BTreeSet::new();
        while let Some(root) = pending.pop() {
            let root = self.identity(root);
            if !visited.insert(root.clone()) {
                continue;
            }
            result.files.extend(
                self.files
                    .iter()
                    .filter(|(path, _)| path.starts_with(&root))
                    .map(|(path, source)| (path.clone(), source.clone())),
            );
            result.aliases.extend(
                self.aliases
                    .iter()
                    .filter(|(_, identity)| identity.starts_with(&root))
                    .map(|(path, identity)| (path.clone(), identity.clone())),
            );
            if let Some(source) = self.source(root.join("ref.toml"))
                && let Ok(manifest) = crate::package_loader::parse_manifest(&root, &source.text)
            {
                pending.extend(manifest.dependencies.into_iter().map(|(_, path)| path));
            }
        }
        result
    }

    fn read_tree(&mut self, root: &Path, visited: &mut BTreeSet<PathBuf>) -> Result<(), String> {
        let identity = root.canonicalize().map_err(|e| e.to_string())?;
        self.aliases.insert(root.to_path_buf(), identity.clone());
        if !visited.insert(identity) {
            return Ok(());
        }
        for entry in
            fs::read_dir(root).map_err(|e| format!("cannot read {}: {e}", root.display()))?
        {
            let entry = entry.map_err(|e| e.to_string())?;
            let path = entry.path();
            if path.is_dir() {
                if !matches!(
                    entry.file_name().to_str(),
                    Some("target" | ".git" | ".ref-cache" | "refcache")
                ) {
                    self.read_tree(&path, visited)?;
                }
            } else if path.extension().is_some_and(|ext| ext == "ref")
                || entry.file_name() == "ref.toml"
            {
                let text = fs::read_to_string(&path)
                    .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
                self.aliases.insert(
                    path.clone(),
                    path.canonicalize().map_err(|error| error.to_string())?,
                );
                self.insert(path, text);
            }
        }
        Ok(())
    }

    pub fn identity(&self, path: impl AsRef<Path>) -> PathBuf {
        let path = absolute(path.as_ref());
        for ancestor in path.ancestors() {
            if let Some(identity) = self.aliases.get(ancestor) {
                let suffix = path.strip_prefix(ancestor).expect("ancestor is a prefix");
                return if suffix.as_os_str().is_empty() {
                    identity.clone()
                } else {
                    identity.join(suffix)
                };
            }
        }
        path
    }

    pub fn entry(&self) -> &Path {
        &self.entry
    }
    pub fn root_directory(&self) -> &Path {
        if self
            .entry
            .extension()
            .is_some_and(|extension| extension == "ref")
        {
            self.entry.parent().unwrap_or(Path::new("/"))
        } else {
            &self.entry
        }
    }
    pub fn default_cache_directory(&self) -> PathBuf {
        self.root_directory().join("refcache")
    }
    pub fn files(&self) -> impl Iterator<Item = (&Path, &Arc<SourceFile>)> {
        self.files
            .iter()
            .map(|(path, source)| (path.as_path(), source))
    }
    pub fn source(&self, path: impl AsRef<Path>) -> Option<&Arc<SourceFile>> {
        self.files.get(&self.identity(path.as_ref()))
    }
    pub fn with_file(&self, path: impl AsRef<Path>, text: impl Into<String>) -> Self {
        let mut next = self.clone();
        next.insert(path, text);
        next
    }
    pub fn without_file(&self, path: impl AsRef<Path>) -> Self {
        let mut next = self.clone();
        next.files.remove(&self.identity(path.as_ref()));
        next
    }
    pub fn insert(&mut self, path: impl AsRef<Path>, text: impl Into<String>) {
        let path = self.identity(path.as_ref());
        self.files.insert(
            path.clone(),
            Arc::new(SourceFile {
                id: SourceId(path),
                text: text.into(),
            }),
        );
    }
}
