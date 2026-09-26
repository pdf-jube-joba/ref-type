use ::syntax::syntax::{SourceFile, SourceId};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path, PathBuf},
    sync::Arc,
};

/// An immutable set of source texts, including manifests and unsaved buffers.
/// Queries never read the filesystem through a snapshot.
#[derive(Clone, Debug)]
pub struct SourceSnapshot {
    entry: PathBuf,
    files: BTreeMap<PathBuf, Arc<SourceFile>>,
    aliases: BTreeMap<PathBuf, PathBuf>,
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
        let mut snapshot = Self::new(entry);
        let mut roots = vec![
            if snapshot.entry.extension().is_some_and(|ext| ext == "ref") {
                snapshot.entry.parent().unwrap().to_path_buf()
            } else {
                snapshot.entry.clone()
            },
        ];
        let mut visited = BTreeSet::new();
        while let Some(root) = roots.pop() {
            let identity = root
                .canonicalize()
                .map_err(|e| format!("cannot open {}: {e}", root.display()))?;
            snapshot.aliases.insert(root.clone(), identity.clone());
            if !visited.insert(identity) {
                continue;
            }
            snapshot.read_tree(&root, &mut BTreeSet::new())?;
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
