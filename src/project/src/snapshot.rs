use crate::error::{Error, IoOperation};
use ::syntax::syntax::{SourceFile, SourceId};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path, PathBuf},
    sync::{Arc, OnceLock},
};

/// An immutable set of source texts, including manifests and unsaved buffers.
/// Queries never read the filesystem through a snapshot.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct SourceSnapshot {
    entry: PathBuf,
    #[serde(with = "source_texts")]
    files: BTreeMap<PathBuf, SourceText>,
    aliases: BTreeMap<PathBuf, PathBuf>,
    #[serde(default)]
    workspace_root: Option<PathBuf>,
}

/// Text and its digest have the same immutable lifetime, including unsaved edits.
#[derive(Clone, Debug)]
struct SourceText {
    source: Arc<SourceFile>,
    digest: Arc<OnceLock<[u8; 32]>>,
}
impl SourceText {
    fn new(path: PathBuf, text: String) -> Self {
        Self {
            source: Arc::new(SourceFile {
                id: SourceId(path),
                text,
            }),
            digest: Arc::new(OnceLock::new()),
        }
    }
    fn digest(&self) -> [u8; 32] {
        *self
            .digest
            .get_or_init(|| Sha256::digest(self.source.text.as_bytes()).into())
    }
}

/// Reuses source allocations and digests after validating their current contents.
/// Retention is bounded independently of snapshots and parsing/query caches.
pub struct SourceCache {
    entries: BTreeMap<PathBuf, (u64, SourceText)>,
    generation: u64,
    budget: usize,
    bytes: usize,
}
impl Default for SourceCache {
    fn default() -> Self {
        Self::with_budget(64 * 1024 * 1024)
    }
}
impl SourceCache {
    pub fn with_budget(bytes: usize) -> Self {
        Self {
            entries: BTreeMap::new(),
            generation: 0,
            budget: bytes,
            bytes: 0,
        }
    }
    pub fn len(&self) -> usize {
        self.entries.len()
    }
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
    pub fn bytes(&self) -> usize {
        self.bytes
    }
    pub fn clear(&mut self) {
        self.entries.clear();
        self.bytes = 0;
    }
    fn next_generation(&mut self) {
        self.generation = self.generation.wrapping_add(1);
        self.entries
            .retain(|_, (generation, _)| generation.saturating_add(1) >= self.generation);
        self.bytes = self
            .entries
            .values()
            .map(|(_, text)| text.source.text.len())
            .sum();
    }
    fn read(&mut self, path: &Path) -> Result<SourceText, Error> {
        // Metadata alone cannot detect same-size edits with restored timestamps.
        // Every acquisition confirms bytes, including the first in a new process.
        let text =
            fs::read_to_string(path).map_err(|e| Error::io(IoOperation::ReadSource, path, e))?;
        if let Some((generation, cached)) = self.entries.get_mut(path)
            && cached.source.text == text
        {
            *generation = self.generation;
            return Ok(cached.clone());
        }
        if let Some((_, old)) = self.entries.remove(path) {
            self.bytes -= old.source.text.len();
        }
        let value = SourceText::new(path.to_path_buf(), text);
        if value.source.text.len() <= self.budget {
            while self.bytes + value.source.text.len() > self.budget || self.entries.len() >= 16_384
            {
                let oldest = self
                    .entries
                    .iter()
                    .min_by_key(|(_, (generation, _))| *generation)
                    .map(|(path, _)| path.clone())
                    .expect("retained entries exceed budget");
                self.bytes -= self.entries.remove(&oldest).unwrap().1.source.text.len();
            }
            self.bytes += value.source.text.len();
            self.entries
                .insert(path.to_path_buf(), (self.generation, value.clone()));
        }
        Ok(value)
    }
}

// Checkpoint SourceFile serialization intentionally omits text. Dependency
// snapshots must retain it so transitive packages can be loaded without disk IO.
mod source_texts {
    use super::*;
    use serde::{Deserialize, Serialize};

    pub fn serialize<S: serde::Serializer>(
        files: &BTreeMap<PathBuf, SourceText>,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        files
            .iter()
            .map(|(path, source)| (path, &source.source.text))
            .collect::<BTreeMap<_, _>>()
            .serialize(serializer)
    }

    pub fn deserialize<'de, D: serde::Deserializer<'de>>(
        deserializer: D,
    ) -> Result<BTreeMap<PathBuf, SourceText>, D::Error> {
        Ok(BTreeMap::<PathBuf, String>::deserialize(deserializer)?
            .into_iter()
            .map(|(path, text)| {
                let source = SourceText::new(path.clone(), text);
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
            workspace_root: None,
        }
    }

    /// Capture source trees and path dependencies. A later edit on disk does
    /// not change this snapshot. Invalid syntax is reported by semantic queries.
    pub fn read(entry: impl AsRef<Path>) -> Result<Self, crate::error::Error> {
        Self::read_with_dependency_cache(entry, |_, _| None)
    }

    /// Read every reachable dependency tree, including transitive dependencies.
    /// The callback is a compatibility hook and cannot bypass source validation.
    pub fn read_with_dependency_cache(
        entry: impl AsRef<Path>,
        mut cached: impl FnMut(&Self, &Path) -> Option<Self>,
    ) -> Result<Self, crate::error::Error> {
        Self::read_cached(entry, &mut SourceCache::default(), &mut cached)
    }

    pub fn read_with_source_cache(
        entry: impl AsRef<Path>,
        cache: &mut SourceCache,
    ) -> Result<Self, Error> {
        Self::read_cached(entry, cache, &mut |_, _| None)
    }

    fn read_cached(
        entry: impl AsRef<Path>,
        cache: &mut SourceCache,
        cached: &mut impl FnMut(&Self, &Path) -> Option<Self>,
    ) -> Result<Self, Error> {
        cache.next_generation();
        let mut snapshot = Self::new(entry);
        if let Some(workspace) = crate::workspace::discover(snapshot.root_directory())? {
            let manifest = workspace.directory.join("ref.toml");
            let text = fs::read_to_string(&manifest)
                .map_err(|error| Error::io(IoOperation::ReadSource, &manifest, error))?;
            snapshot.insert(manifest, text);
            snapshot.workspace_root = Some(workspace.directory);
        }
        let mut roots = vec![snapshot.root_directory().to_path_buf()];
        let mut visited = BTreeSet::new();
        while let Some(root) = roots.pop() {
            let identity = root
                .canonicalize()
                .map_err(|e| Error::io(IoOperation::Open, &root, e))?;
            snapshot.aliases.insert(root.clone(), identity.clone());
            if !visited.insert(identity) {
                continue;
            }
            let mut own = Self::new(&root);
            own.aliases.insert(root.clone(), snapshot.identity(&root));
            let manifest_path = root.join("ref.toml");
            let workspace_manifest = fs::read_to_string(&manifest_path).ok().filter(|text| {
                crate::package_loader::parse_manifest(&root, text).is_ok_and(|manifest| {
                    manifest.package.is_none() && manifest.workspace.is_some()
                })
            });
            if let Some(text) = workspace_manifest {
                own.insert(manifest_path, text);
            } else {
                own.read_tree(&root, &mut BTreeSet::new(), cache)?;
            }
            // Every reachable package is visited and checked against disk.
            if root != snapshot.root_directory()
                && let Some(saved) = cached(&own, &root)
            {
                for (path, source) in &mut own.files {
                    if let Some(previous) = saved.files.get(path)
                        && previous.source.text == source.source.text
                    {
                        *source = previous.clone();
                    }
                }
            }
            snapshot.files.extend(own.files);
            snapshot.aliases.extend(own.aliases);
            if let Some(source) = snapshot.source(root.join("ref.toml"))
                && let Ok(manifest) = crate::package_loader::parse_manifest(&root, &source.text)
            {
                if let Some(package) = &manifest.package {
                    roots.extend(package.dependencies.iter().map(|(_, path)| absolute(path)));
                }
                if snapshot.identity(&root) == snapshot.identity(snapshot.root_directory()) {
                    roots.extend(
                        manifest
                            .workspace
                            .iter()
                            .flat_map(|workspace| &workspace.packages)
                            .cloned(),
                    );
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
                pending.extend(
                    manifest.package.iter().flat_map(|package| {
                        package.dependencies.iter().map(|(_, path)| path.clone())
                    }),
                );
            }
        }
        result
    }

    fn read_tree(
        &mut self,
        root: &Path,
        visited: &mut BTreeSet<PathBuf>,
        cache: &mut SourceCache,
    ) -> Result<(), crate::error::Error> {
        let identity = root
            .canonicalize()
            .map_err(|e| Error::io(IoOperation::Open, root, e))?;
        self.aliases.insert(root.to_path_buf(), identity.clone());
        if !visited.insert(identity) {
            return Ok(());
        }
        for entry in
            fs::read_dir(root).map_err(|e| Error::io(IoOperation::ReadDirectory, root, e))?
        {
            let entry = entry.map_err(|e| Error::io(IoOperation::ReadEntry, root, e))?;
            let path = entry.path();
            if path.is_dir() {
                if !matches!(
                    entry.file_name().to_str(),
                    Some("target" | ".git" | ".ref-cache" | "ref-cache" | "refcache")
                ) {
                    self.read_tree(&path, visited, cache)?;
                }
            } else if path.extension().is_some_and(|ext| ext == "ref")
                || entry.file_name() == "ref.toml"
            {
                self.aliases.insert(
                    path.clone(),
                    path.canonicalize()
                        .map_err(|error| Error::io(IoOperation::Open, &path, error))?,
                );
                let identity = self.identity(&path);
                self.files.insert(identity.clone(), cache.read(&identity)?);
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
        self.workspace_root
            .as_deref()
            .unwrap_or_else(|| self.root_directory())
            .join("refcache")
    }
    pub fn files(&self) -> impl Iterator<Item = (&Path, &Arc<SourceFile>)> {
        self.files
            .iter()
            .map(|(path, source)| (path.as_path(), &source.source))
    }
    /// Captured aliases that determine the identity of a source or its package.
    pub fn source_identities(&self) -> impl Iterator<Item = (&Path, &Path)> {
        self.aliases
            .iter()
            .filter(|(_, identity)| {
                self.files
                    .range((*identity).clone()..)
                    .next()
                    .is_some_and(|(path, _)| path.starts_with(identity))
            })
            .map(|(path, identity)| (path.as_path(), identity.as_path()))
    }
    pub fn source(&self, path: impl AsRef<Path>) -> Option<&Arc<SourceFile>> {
        self.files
            .get(&self.identity(path.as_ref()))
            .map(|text| &text.source)
    }
    /// Cached SHA-256 of precisely the text captured by this snapshot.
    pub fn content_digest(&self, path: impl AsRef<Path>) -> Option<[u8; 32]> {
        self.files
            .get(&self.identity(path.as_ref()))
            .map(SourceText::digest)
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
        self.files
            .insert(path.clone(), SourceText::new(path, text.into()));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    fn temporary_sources(label: &str) -> PathBuf {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let root = std::env::temp_dir().join(format!(
            "ref-source-{label}-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&root).unwrap();
        root
    }

    #[test]
    fn source_cache_reuses_digest_but_validates_same_size_same_timestamp_edits() {
        let root = temporary_sources("edits");
        let path = root.join("Main.ref");
        fs::write(&path, "first").unwrap();
        let mut cache = SourceCache::default();
        let before = SourceSnapshot::read_with_source_cache(&root, &mut cache).unwrap();
        let digest = before.content_digest(&path).unwrap();
        let repeated = SourceSnapshot::read_with_source_cache(&root, &mut cache).unwrap();
        assert!(Arc::ptr_eq(
            before.source(&path).unwrap(),
            repeated.source(&path).unwrap()
        ));
        assert!(Arc::ptr_eq(
            &before.files[&path].digest,
            &repeated.files[&path].digest
        ));
        assert_eq!(repeated.files[&path].digest.get(), Some(&digest));
        let timestamp = fs::metadata(&path).unwrap().modified().unwrap();
        fs::write(&path, "other").unwrap();
        fs::File::options()
            .write(true)
            .open(&path)
            .unwrap()
            .set_modified(timestamp)
            .unwrap();
        let changed = SourceSnapshot::read_with_source_cache(&root, &mut cache).unwrap();
        assert_ne!(changed.content_digest(&path), Some(digest));
        assert_eq!(before.source(&path).unwrap().text, "first");
        let fresh =
            SourceSnapshot::read_with_source_cache(&root, &mut SourceCache::default()).unwrap();
        assert_eq!(fresh.content_digest(&path), changed.content_digest(&path));
        fs::remove_file(&path).unwrap();
        let deleted = SourceSnapshot::read_with_source_cache(&root, &mut cache).unwrap();
        assert!(deleted.source(&path).is_none());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn immutable_buffer_edits_share_only_unchanged_digest_cells() {
        let mut original = SourceSnapshot::new("/source-cache-buffer");
        original.insert("/source-cache-buffer/Main.ref", "disk");
        original.insert("/source-cache-buffer/Other.ref", "unchanged");
        let path = Path::new("/source-cache-buffer/Main.ref");
        let other = Path::new("/source-cache-buffer/Other.ref");
        let previous = original.content_digest(path).unwrap();
        let edited = original.with_file(path, "buffer");
        assert_ne!(edited.content_digest(path), Some(previous));
        assert_eq!(original.content_digest(path), Some(previous));
        assert!(Arc::ptr_eq(
            &original.files[other].digest,
            &edited.files[other].digest
        ));
        assert!(edited.without_file(path).content_digest(path).is_none());
    }

    #[test]
    fn source_retention_obeys_bytes_and_generations_without_invalidating_snapshots() {
        let root = temporary_sources("budget");
        let a = root.join("A.ref");
        let b = root.join("B.ref");
        fs::write(&a, "12345678").unwrap();
        fs::write(&b, "abcdefgh").unwrap();
        let mut cache = SourceCache::with_budget(8);
        let held = cache.read(&a).unwrap();
        cache.read(&b).unwrap();
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.bytes(), 8);
        assert_eq!(held.source.text, "12345678");
        cache.next_generation();
        cache.next_generation();
        assert!(cache.is_empty());
        assert_eq!(cache.bytes(), 0);
        cache.read(&a).unwrap();
        cache.clear();
        assert!(cache.is_empty());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn cached_dependency_snapshot_validates_transitive_sources() {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let root = std::env::temp_dir().join(format!(
            "ref-type-source-validation-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        for (name, dependency) in [("A", None), ("B", Some("A")), ("C", Some("B"))] {
            fs::create_dir_all(root.join(name).join("src")).unwrap();
            let mut manifest = format!("[package]\nname = '{name}'\n");
            if let Some(dependency) = dependency {
                manifest.push_str(&format!(
                    "[dependencies]\n{dependency} = {{ path = '../{dependency}' }}\n"
                ));
            }
            fs::write(root.join(name).join("ref.toml"), manifest).unwrap();
            fs::write(root.join(name).join("src/root.ref"), "\\module Original {}").unwrap();
        }
        let before = SourceSnapshot::read(root.join("C")).unwrap();
        fs::write(root.join("A/src/root.ref"), "\\module Changed {}").unwrap();
        let after = SourceSnapshot::read_with_dependency_cache(root.join("C"), |_, path| {
            Some(before.package_snapshot(path))
        })
        .unwrap();
        assert_eq!(
            after.source(root.join("A/src/root.ref")).unwrap().text,
            "\\module Changed {}"
        );
        assert_eq!(
            before.source(root.join("A/src/root.ref")).unwrap().text,
            "\\module Original {}"
        );
        fs::remove_dir_all(root).unwrap();
    }
}
