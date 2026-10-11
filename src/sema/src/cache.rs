use crate::{ModuleResult, error::CacheError};
use sha2::{Digest, Sha256};
use std::path::PathBuf;

pub(crate) type Fingerprint = [u8; 32];
pub(crate) fn fingerprint(bytes: &[u8]) -> Fingerprint {
    Sha256::digest(bytes).into()
}

/// Locally trusted semantic artifacts. Obsolete formats and damaged objects miss.
pub(crate) struct DiskCache {
    v2: crate::artifact_store::ArtifactStore,
}
impl DiskCache {
    pub fn new(directory: PathBuf) -> Self {
        Self {
            v2: crate::artifact_store::ArtifactStore::new(directory),
        }
    }
    pub fn store(&self) -> &crate::artifact_store::ArtifactStore {
        &self.v2
    }
    pub fn set_budget(&self, bytes: u64) {
        self.v2.set_budget(bytes);
    }
    pub fn read(&self, key: &Fingerprint) -> Option<ModuleResult> {
        let manifest = self.v2.read_manifest(key).ok()?;
        let (_, object) = manifest.results.first()?;
        let result: ModuleResult =
            crate::artifact_store::deserialize(&self.v2.read_object(object).ok()?).ok()?;
        (result.status == crate::ModuleStatus::Verified).then_some(result)
    }

    pub fn write(&self, key: &Fingerprint, result: &ModuleResult) -> Result<(), CacheError> {
        if result.status != crate::ModuleStatus::Verified {
            return Ok(());
        }
        let object = self.v2.write_object(
            crate::artifact_store::ObjectKind::Result,
            &crate::artifact_store::serialize(result)?,
        )?;
        self.v2.publish(&crate::artifact_store::StoreManifest {
            key: *key,
            input: *key,
            coverage: vec![result.path.clone()],
            results: vec![(result.path.clone(), object)],
            ..Default::default()
        })
    }

    pub fn read_environment(&self, key: &Fingerprint) -> Option<Vec<u8>> {
        let manifest = self.v2.read_manifest(key).ok()?;
        self.v2.read_object(manifest.environment.as_ref()?).ok()
    }

    pub fn write_environment(&self, key: &Fingerprint, payload: &[u8]) -> Result<(), CacheError> {
        let object = self
            .v2
            .write_object(crate::artifact_store::ObjectKind::Environment, payload)?;
        self.v2.publish(&crate::artifact_store::StoreManifest {
            key: *key,
            input: *key,
            environment: Some(object),
            ..Default::default()
        })
    }
}
