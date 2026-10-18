use crate::{ModuleResult, error::CacheError};
use sha2::{Digest, Sha256};
use std::path::PathBuf;

pub(crate) type Fingerprint = [u8; 32];
pub(crate) fn fingerprint(bytes: &[u8]) -> Fingerprint {
    Sha256::digest(bytes).into()
}

pub(crate) fn snapshot_key(
    snapshot: &crate::SourceSnapshot,
    configuration: &str,
    compact: bool,
) -> Fingerprint {
    let mut digest = Sha256::new();
    let mut field = |bytes: &[u8]| {
        digest.update((bytes.len() as u64).to_le_bytes());
        digest.update(bytes);
    };
    field(b"ref-type.complete-query");
    field(env!("REF_SEMA_REVISION").as_bytes());
    field(configuration.as_bytes());
    field(&[u8::from(compact)]);
    field(snapshot.entry().as_os_str().as_encoded_bytes());
    for (path, identity) in snapshot.source_identities() {
        field(b"identity");
        field(path.as_os_str().as_encoded_bytes());
        field(identity.as_os_str().as_encoded_bytes());
    }
    for (path, _) in snapshot.files() {
        field(b"source");
        field(path.as_os_str().as_encoded_bytes());
        field(&snapshot.content_digest(path).expect("captured source"));
    }
    digest.finalize().into()
}

/// Locally trusted semantic artifacts. Obsolete formats and damaged objects miss.
pub(crate) struct DiskCache {
    store: crate::artifact_store::ArtifactStore,
}
impl DiskCache {
    pub fn new(directory: PathBuf) -> Self {
        Self {
            store: crate::artifact_store::ArtifactStore::new(directory),
        }
    }
    pub fn store(&self) -> &crate::artifact_store::ArtifactStore {
        &self.store
    }
    pub fn set_budget(&self, bytes: u64) {
        self.store.set_budget(bytes);
    }

    pub fn read_query(&self, key: &Fingerprint) -> Option<crate::SemanticResult> {
        let manifest = self.store.read_manifest(key).ok()?;
        let (_, object) = manifest.results.first()?;
        let result: crate::SemanticResult =
            crate::artifact_store::deserialize(&self.store.read_object(object).ok()?).ok()?;
        result.is_success().then_some(result)
    }

    pub fn write_query(
        &self,
        key: &Fingerprint,
        result: &crate::SemanticResult,
    ) -> Result<(), CacheError> {
        let object = self.store.write_object(
            crate::artifact_store::ObjectKind::Result,
            &crate::artifact_store::serialize(result)?,
        )?;
        self.store.publish(&crate::artifact_store::StoreManifest {
            key: *key,
            input: *key,
            results: vec![(Vec::new(), object)],
            ..Default::default()
        })
    }
    pub fn read(&self, key: &Fingerprint) -> Option<ModuleResult> {
        let manifest = self.store.read_manifest(key).ok()?;
        let (_, object) = manifest.results.first()?;
        let result: ModuleResult =
            crate::artifact_store::deserialize(&self.store.read_object(object).ok()?).ok()?;
        (result.status == crate::ModuleStatus::Verified).then_some(result)
    }

    pub fn write(&self, key: &Fingerprint, result: &ModuleResult) -> Result<(), CacheError> {
        if result.status != crate::ModuleStatus::Verified {
            return Ok(());
        }
        let object = self.store.write_object(
            crate::artifact_store::ObjectKind::Result,
            &crate::artifact_store::serialize(result)?,
        )?;
        self.store.publish(&crate::artifact_store::StoreManifest {
            key: *key,
            input: *key,
            coverage: vec![result.path.clone()],
            results: vec![(result.path.clone(), object)],
            ..Default::default()
        })
    }

    pub fn read_environment(&self, key: &Fingerprint) -> Option<Vec<u8>> {
        let manifest = self.store.read_manifest(key).ok()?;
        self.store.read_object(manifest.environment.as_ref()?).ok()
    }

    pub fn write_environment(&self, key: &Fingerprint, payload: &[u8]) -> Result<(), CacheError> {
        let object = self
            .store
            .write_object(crate::artifact_store::ObjectKind::Environment, payload)?;
        self.store.publish(&crate::artifact_store::StoreManifest {
            key: *key,
            input: *key,
            environment: Some(object),
            ..Default::default()
        })
    }
}
