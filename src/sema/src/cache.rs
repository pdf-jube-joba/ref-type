use crate::ModuleResult;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    fs::{self, OpenOptions},
    io::Write,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

pub(crate) type Fingerprint = [u8; 32];
pub(crate) fn fingerprint(bytes: &[u8]) -> Fingerprint {
    Sha256::digest(bytes).into()
}
fn hex(key: &Fingerprint) -> String {
    key.iter().map(|byte| format!("{byte:02x}")).collect()
}

const SCHEMA: u32 = 10;

#[derive(Serialize, Deserialize)]
struct Record {
    schema: u32,
    key: Fingerprint,
    checksum: Fingerprint,
    payload: String,
}

/// Locally trusted semantic results and checking environments.
/// Obsolete records and damaged files are recoverable misses.
pub(crate) struct DiskCache {
    directory: PathBuf,
}
impl DiskCache {
    pub fn new(directory: PathBuf) -> Self {
        Self { directory }
    }
    pub fn read(&self, key: &Fingerprint) -> Option<ModuleResult> {
        let payload = self.read_payload(key, "json")?;
        let result: ModuleResult = serde_json::from_str(&payload).ok()?;
        (result.status == crate::ModuleStatus::Verified).then_some(result)
    }

    fn read_payload(&self, key: &Fingerprint, extension: &str) -> Option<String> {
        let path = self.directory.join(format!("{}.{extension}", hex(key)));
        if fs::metadata(&path).ok()?.len() > 64 * 1024 * 1024 {
            return None;
        }
        let record: Record = serde_json::from_slice(&fs::read(path).ok()?).ok()?;
        if record.schema != SCHEMA
            || record.key != *key
            || record.checksum != fingerprint(record.payload.as_bytes())
        {
            return None;
        }
        Some(record.payload)
    }
    pub fn write(&self, key: &Fingerprint, result: &ModuleResult) -> Result<(), String> {
        if result.status != crate::ModuleStatus::Verified {
            return Ok(());
        }
        let payload = serde_json::to_string(result).map_err(|error| error.to_string())?;
        self.write_payload(key, "json", payload)
    }

    fn write_payload(
        &self,
        key: &Fingerprint,
        extension: &str,
        payload: String,
    ) -> Result<(), String> {
        let bytes = serde_json::to_vec(&Record {
            schema: SCHEMA,
            key: *key,
            checksum: fingerprint(payload.as_bytes()),
            payload,
        })
        .map_err(|error| error.to_string())?;
        self.write_bytes(key, extension, &bytes)
    }

    pub fn read_sources(
        &self,
        own: &crate::SourceSnapshot,
        root: &Path,
    ) -> Option<crate::SourceSnapshot> {
        let key = source_key(own, root);
        let saved: crate::SourceSnapshot =
            serde_json::from_str(&self.read_payload(&key, "sources.json")?).ok()?;
        (saved.identity(saved.entry()) == own.identity(root) && source_key(&saved, root) == key)
            .then_some(saved)
    }

    pub fn write_sources(
        &self,
        snapshot: &crate::SourceSnapshot,
        packages: &[PathBuf],
    ) -> Result<(), String> {
        for root in packages {
            let saved = snapshot.package_snapshot(root);
            self.write_payload(
                &source_key(&saved, root),
                "sources.json",
                serde_json::to_string(&saved).map_err(|error| error.to_string())?,
            )?;
        }
        Ok(())
    }

    fn write_bytes(&self, key: &Fingerprint, extension: &str, bytes: &[u8]) -> Result<(), String> {
        fs::create_dir_all(&self.directory).map_err(|error| error.to_string())?;
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let temporary = self.directory.join(format!(
            ".{}-{}.tmp",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let destination = self.directory.join(format!("{}.{extension}", hex(key)));
        let result = (|| -> std::io::Result<()> {
            let mut file = OpenOptions::new()
                .create_new(true)
                .write(true)
                .open(&temporary)?;
            file.write_all(bytes)?;
            file.sync_all()?;
            fs::rename(&temporary, destination)
        })();
        if result.is_err() {
            let _ = fs::remove_file(temporary);
        }
        result.map_err(|error| error.to_string())
    }
}

fn source_key(snapshot: &crate::SourceSnapshot, root: &Path) -> Fingerprint {
    let root = snapshot.identity(root);
    let mut bytes = env!("REF_SEMA_REVISION").as_bytes().to_vec();
    bytes.extend(root.to_string_lossy().as_bytes());
    for (path, source) in snapshot.files().filter(|(path, _)| path.starts_with(&root)) {
        bytes.extend(path.to_string_lossy().as_bytes());
        bytes.extend(fingerprint(source.text.as_bytes()));
    }
    fingerprint(&bytes)
}

impl DiskCache {
    pub fn read_environment(&self, key: &Fingerprint) -> Option<Vec<u8>> {
        let path = self.directory.join(format!("{}.env", hex(key)));
        if fs::metadata(&path).ok()?.len() > (elaboration::MAX_ENVIRONMENT_BYTES + 72) as u64 {
            return None;
        }
        let bytes = fs::read(path).ok()?;
        let payload = bytes.get(72..)?;
        if &bytes[..8] != b"REFENV01"
            || &bytes[8..40] != key
            || bytes[40..72] != fingerprint(payload)
        {
            return None;
        }
        Some(payload.to_vec())
    }

    pub fn write_environment(&self, key: &Fingerprint, payload: &[u8]) -> Result<(), String> {
        let mut bytes = b"REFENV01".to_vec();
        bytes.extend(key);
        bytes.extend(fingerprint(payload));
        bytes.extend(payload);
        self.write_bytes(key, "env", &bytes)
    }
}
