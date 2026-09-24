//! Versioned source inputs. Filesystem access belongs to the host, never a query.
use crate::syntax::{SourceFile, SourceId, SourceSpan};
use std::{
    collections::BTreeMap,
    path::{Component, Path, PathBuf},
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(pub u64);

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RevisionId(pub u64);

impl RevisionId {
    fn fresh() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(1);
        Self(NEXT.fetch_add(1, Ordering::Relaxed))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Location {
    pub file: FileId,
    pub revision: RevisionId,
    pub range: SourceSpan,
}

#[derive(Debug, Clone)]
pub struct FileSnapshot {
    pub id: FileId,
    pub revision: RevisionId,
    pub source: Arc<SourceFile>,
    pub(crate) identity: PathBuf,
}

impl FileSnapshot {
    pub fn location(&self, range: SourceSpan) -> Location {
        Location {
            file: self.id,
            revision: self.revision,
            range,
        }
    }
}

#[derive(Debug, Clone)]
struct FileInput {
    path: PathBuf,
    identity: PathBuf,
    disk: Option<Arc<str>>,
    overlay: Option<Arc<str>>,
    revision: RevisionId,
    snapshot: Option<Arc<FileSnapshot>>,
}

#[derive(Debug, Clone, Default)]
struct Inputs {
    revision: RevisionId,
    files: BTreeMap<FileId, FileInput>,
    paths: BTreeMap<PathBuf, FileId>,
}

/// Copy-on-write VFS with separate disk and unsaved buffer contents.
#[derive(Debug, Clone)]
pub struct SourceDatabase {
    base: PathBuf,
    inputs: Arc<Inputs>,
}

impl SourceDatabase {
    pub fn new(base: impl AsRef<Path>) -> std::io::Result<Self> {
        Ok(Self {
            base: normalize(&std::path::absolute(base)?),
            inputs: Arc::new(Inputs {
                revision: RevisionId::fresh(),
                ..Inputs::default()
            }),
        })
    }

    pub fn revision(&self) -> RevisionId {
        self.inputs.revision
    }

    pub fn absolute_path(&self, path: &Path) -> PathBuf {
        normalize(&self.base.join(path))
    }

    pub fn file_id(&self, path: impl AsRef<Path>) -> Option<FileId> {
        self.inputs
            .paths
            .get(&self.absolute_path(path.as_ref()))
            .copied()
    }

    pub fn file(&self, id: FileId) -> Option<Arc<FileSnapshot>> {
        self.inputs.files.get(&id)?.snapshot.clone()
    }

    pub fn files(&self) -> impl Iterator<Item = Arc<FileSnapshot>> + '_ {
        self.inputs
            .files
            .values()
            .filter_map(|file| file.snapshot.clone())
    }

    pub fn set_disk(&mut self, path: impl AsRef<Path>, text: Option<String>) -> FileId {
        self.update(path.as_ref(), text, false)
    }

    pub(crate) fn set_disk_identity(
        &mut self,
        path: &Path,
        text: Option<String>,
        identity: PathBuf,
    ) -> FileId {
        let id = self.set_disk(path, text);
        if self.inputs.files[&id].identity != identity {
            let inputs = Arc::make_mut(&mut self.inputs);
            inputs.revision = RevisionId::fresh();
            let file = inputs.files.get_mut(&id).unwrap();
            file.identity = identity;
            Self::refresh(id, file, inputs.revision);
        }
        id
    }

    pub fn set_overlay(&mut self, path: impl AsRef<Path>, text: String) -> FileId {
        self.update(path.as_ref(), Some(text), true)
    }

    pub fn close_overlay(&mut self, path: impl AsRef<Path>) -> FileId {
        self.update(path.as_ref(), None, true)
    }

    pub fn rename(&mut self, id: FileId, path: impl AsRef<Path>) -> Result<(), String> {
        let path = self.absolute_path(path.as_ref());
        if self.inputs.paths.get(&path) == Some(&id) {
            return Ok(());
        }
        if self.inputs.paths.contains_key(&path) {
            return Err("destination path already has a file identity".into());
        }
        if !self.inputs.files.contains_key(&id) {
            return Err("unknown file identity".into());
        }
        let inputs = Arc::make_mut(&mut self.inputs);
        inputs.revision = RevisionId::fresh();
        let file = inputs.files.get_mut(&id).unwrap();
        inputs.paths.remove(&file.path);
        inputs.paths.insert(path.clone(), id);
        file.path = path;
        file.identity = file.path.clone();
        Self::refresh(id, file, inputs.revision);
        Ok(())
    }

    fn update(&mut self, path: &Path, text: Option<String>, overlay: bool) -> FileId {
        let path = self.absolute_path(path);
        if let Some(id) = self.inputs.paths.get(&path) {
            let file = &self.inputs.files[id];
            let previous = if overlay { &file.overlay } else { &file.disk };
            if previous.as_deref() == text.as_deref() {
                return *id;
            }
        }
        let inputs = Arc::make_mut(&mut self.inputs);
        inputs.revision = RevisionId::fresh();
        let next_id = FileId(inputs.files.len() as u64);
        let id = *inputs.paths.entry(path.clone()).or_insert(next_id);
        let file = inputs.files.entry(id).or_insert_with(|| FileInput {
            identity: path.clone(),
            path,
            disk: None,
            overlay: None,
            revision: inputs.revision,
            snapshot: None,
        });
        if overlay {
            file.overlay = text.map(Arc::from);
        } else {
            file.disk = text.map(Arc::from);
        }
        Self::refresh(id, file, inputs.revision);
        id
    }

    fn refresh(id: FileId, file: &mut FileInput, revision: RevisionId) {
        file.revision = revision;
        file.snapshot = file.overlay.as_ref().or(file.disk.as_ref()).map(|text| {
            Arc::new(FileSnapshot {
                id,
                revision,
                identity: file.identity.clone(),
                source: Arc::new(SourceFile {
                    id: SourceId(file.path.clone()),
                    text: text.to_string(),
                }),
            })
        });
    }
}

fn normalize(path: &Path) -> PathBuf {
    let mut result = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                result.pop();
            }
            component => result.push(component),
        }
    }
    result
}
