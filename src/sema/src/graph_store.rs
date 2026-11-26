//! Session graph pages share the manifest store's leases, integrity checks and GC.
use crate::{
    artifact_store::{ArtifactStore, ObjectKind, ObjectRef},
    cache::Fingerprint,
};
use std::{cell::RefCell, collections::BTreeMap, io, rc::Rc, sync::Arc};

pub(crate) struct GraphPages {
    store: Arc<ArtifactStore>,
    references: RefCell<BTreeMap<Fingerprint, ObjectRef>>,
    stage_checkpoint: bool,
}
impl std::fmt::Debug for GraphPages {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GraphPages")
            .field("pages", &self.references.borrow().len())
            .finish()
    }
}
impl GraphPages {
    pub(crate) fn new(store: Arc<ArtifactStore>) -> Rc<Self> {
        Self::with_checkpoint_staging(store, false)
    }
    pub(crate) fn for_package_check(store: Arc<ArtifactStore>) -> Rc<Self> {
        Self::with_checkpoint_staging(store, true)
    }
    fn with_checkpoint_staging(store: Arc<ArtifactStore>, stage_checkpoint: bool) -> Rc<Self> {
        Rc::new(Self {
            store,
            references: RefCell::new(BTreeMap::new()),
            stage_checkpoint,
        })
    }
    fn track(&self, reference: ObjectRef) -> io::Result<Vec<u8>> {
        let encoded = crate::artifact_store::serialize(&reference).map_err(io::Error::other)?;
        self.references
            .borrow_mut()
            .insert(reference.digest, reference);
        Ok(encoded)
    }
    pub(crate) fn clear(&self) {
        self.references.borrow_mut().clear();
    }
    pub(crate) fn references(&self) -> Vec<ObjectRef> {
        self.references.borrow().values().cloned().collect()
    }
    pub(crate) fn validate(&self, references: &[ObjectRef]) -> Option<()> {
        self.store
            .pin_objects(&references.iter().collect::<Vec<_>>())
            .ok()?;
        for reference in references {
            if reference.kind != ObjectKind::Environment {
                return None;
            }
            self.store.read_pinned_object(reference).ok()?;
            self.references
                .borrow_mut()
                .insert(reference.digest, reference.clone());
        }
        Some(())
    }
}
impl elaboration::GraphStore for GraphPages {
    fn identity(&self) -> String {
        self.store.directory().to_string_lossy().into_owned()
    }
    fn write(&self, bytes: &[u8]) -> io::Result<Vec<u8>> {
        let reference = self
            .store
            .write_object(ObjectKind::Environment, bytes)
            .map_err(io::Error::other)?;
        self.track(reference)
    }
    fn write_checkpoint_segment(&self, bytes: &[u8]) -> io::Result<Vec<u8>> {
        if !self.stage_checkpoint {
            return self.write(bytes);
        }
        let reference = self
            .store
            .write_checkpoint_object(ObjectKind::Environment, bytes)
            .map_err(io::Error::other)?;
        self.track(reference)
    }
    fn read(&self, reference: &[u8]) -> io::Result<Vec<u8>> {
        let reference: ObjectRef =
            crate::artifact_store::deserialize(reference).map_err(io::Error::other)?;
        if reference.kind != ObjectKind::Environment {
            return Err(io::Error::other("invalid graph object kind"));
        }
        self.store
            .read_pinned_object(&reference)
            .map_err(io::Error::other)
    }
    fn retain(&self, reference: &[u8]) -> io::Result<()> {
        let reference: ObjectRef =
            crate::artifact_store::deserialize(reference).map_err(io::Error::other)?;
        if reference.kind != ObjectKind::Environment {
            return Err(io::Error::other("invalid graph object kind"));
        }
        self.references
            .borrow_mut()
            .insert(reference.digest, reference);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicUsize, Ordering},
    };

    struct Directory(PathBuf);
    impl Drop for Directory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn pages_are_cached_before_checkpointing_and_survive_collection() {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let directory = Directory(std::env::temp_dir().join(format!(
            "ref-type-paging-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        )));
        let store = Arc::new(ArtifactStore::new(directory.0.join("refcache")));
        let pages = GraphPages::new(store.clone());
        let checker = elaboration::Checker::default();
        let arena = checker.kernel_environment().arena().clone();
        arena.set_resident_budget(1024 * 1024);
        let expressions: Vec<_> = elaboration::with_graph_store(pages.clone(), || {
            (0..32768).map(|index| arena.bound(index)).collect()
        });
        assert!(arena.store_stats().evictions > 0);
        assert!(!pages.references().is_empty());
        assert!(store.directory().join("objects").is_dir());
        store.set_budget(0);
        store.collect().unwrap();
        let loads = arena.store_stats().loads;
        let _loaded = arena.get(expressions[7]);
        assert!(arena.store_stats().loads > loads);
    }
}
