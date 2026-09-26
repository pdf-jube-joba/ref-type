use crate::ModuleResult;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    fs::{self, OpenOptions},
    io::Write,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

pub(crate) type Fingerprint = [u8; 32];
pub(crate) fn fingerprint(bytes: &[u8]) -> Fingerprint {
    Sha256::digest(bytes).into()
}
fn hex(key: &Fingerprint) -> String {
    key.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[derive(Serialize, Deserialize)]
struct Record {
    key: Fingerprint,
    checksum: Fingerprint,
    payload: String,
}

/// Cache files contain checked semantic results, never executable code or
/// kernel objects. Every miss, obsolete record or damaged file is recoverable.
pub(crate) struct DiskCache {
    directory: PathBuf,
}
impl DiskCache {
    pub fn new(directory: PathBuf) -> Self {
        Self { directory }
    }
    pub fn read(&self, key: &Fingerprint) -> Option<ModuleResult> {
        let path = self.directory.join(format!("{}.json", hex(key)));
        if fs::metadata(&path).ok()?.len() > 64 * 1024 * 1024 {
            return None;
        }
        let record: Record = serde_json::from_slice(&fs::read(path).ok()?).ok()?;
        if record.key != *key || record.checksum != fingerprint(record.payload.as_bytes()) {
            return None;
        }
        let result: ModuleResult = serde_json::from_str(&record.payload).ok()?;
        (result.status == crate::ModuleStatus::Verified).then_some(result)
    }
    pub fn write(&self, key: &Fingerprint, result: &ModuleResult) -> Result<(), String> {
        if result.status != crate::ModuleStatus::Verified {
            return Ok(());
        }
        fs::create_dir_all(&self.directory).map_err(|error| error.to_string())?;
        let payload = serde_json::to_string(result).map_err(|error| error.to_string())?;
        let bytes = serde_json::to_vec(&Record {
            key: *key,
            checksum: fingerprint(payload.as_bytes()),
            payload,
        })
        .map_err(|error| error.to_string())?;
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let temporary = self.directory.join(format!(
            ".{}-{}.tmp",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let destination = self.directory.join(format!("{}.json", hex(key)));
        let result = (|| -> std::io::Result<()> {
            let mut file = OpenOptions::new()
                .create_new(true)
                .write(true)
                .open(&temporary)?;
            file.write_all(&bytes)?;
            file.sync_all()?;
            fs::rename(&temporary, destination)
        })();
        if result.is_err() {
            let _ = fs::remove_file(temporary);
        }
        result.map_err(|error| error.to_string())
    }
}
