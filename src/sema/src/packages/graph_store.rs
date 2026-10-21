//! Session graph pages share the manifest store's leases, integrity checks and GC.
use crate::{
    artifact_store::{ArtifactStore, ObjectKind, ObjectRef},
    cache::Fingerprint,
};
use std::{cell::RefCell, collections::BTreeMap, io, rc::Rc, sync::Arc};

pub(super) struct GraphPages {
    store: Arc<ArtifactStore>,
    references: RefCell<BTreeMap<Fingerprint, ObjectRef>>,
}
impl std::fmt::Debug for GraphPages {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GraphPages")
            .field("pages", &self.references.borrow().len())
            .finish()
    }
}
impl GraphPages {
    pub(super) fn new(store: Arc<ArtifactStore>) -> Rc<Self> {
        Rc::new(Self {
            store,
            references: RefCell::new(BTreeMap::new()),
        })
    }
    pub(super) fn clear(&self) {
        self.references.borrow_mut().clear();
    }
    pub(super) fn references(&self) -> Vec<ObjectRef> {
        self.references.borrow().values().cloned().collect()
    }
    pub(super) fn validate(&self, references: &[ObjectRef]) -> Option<()> {
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
        let encoded = crate::artifact_store::serialize(&reference).map_err(io::Error::other)?;
        self.references
            .borrow_mut()
            .insert(reference.digest, reference);
        Ok(encoded)
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
