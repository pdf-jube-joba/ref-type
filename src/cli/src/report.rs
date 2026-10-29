//! Stable observations of a CLI invocation, independent of cache representation.
use serde::{Deserialize, Serialize};
use std::{fs::File, io::Write, path::Path};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Outcome {
    Accepted,
    Rejected,
    StorageFailure,
    Interrupted,
    TimeLimit,
    MemoryLimit,
    InternalError,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Cache {
    pub verification_reused: bool,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(default)]
pub struct Execution {
    pub workers: u64,
    pub recoveries: u64,
    pub peak_rss_kib: u64,
    pub peak_virtual_kib: u64,
    pub cpu_micros: u64,
    pub elapsed_micros: u64,
    pub collection_requests: u64,
    pub source_steps: u64,
    pub duplicate_source_steps: u64,
    pub replayed_source_steps: u64,
    pub lost_steps: u64,
    pub last_module: Option<Vec<String>>,
    pub last_checkpoint: usize,
}

impl Execution {
    pub fn merge(&mut self, other: &Self) {
        self.peak_rss_kib = self.peak_rss_kib.max(other.peak_rss_kib);
        self.peak_virtual_kib = self.peak_virtual_kib.max(other.peak_virtual_kib);
        self.cpu_micros += other.cpu_micros;
        self.collection_requests += other.collection_requests;
        if other.last_module.is_some() {
            self.last_module.clone_from(&other.last_module);
        }
        self.last_checkpoint = self.last_checkpoint.max(other.last_checkpoint);
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Report {
    pub version: u32,
    pub outcome: Outcome,
    pub cache: Cache,
    #[serde(default)]
    pub execution: Execution,
    #[serde(default)]
    pub checking: sema::QueryStats,
    #[serde(default)]
    pub storage: sema::artifact_store::CacheStoreStats,
    /// Authoritative normal-check coverage, including validated cached results.
    #[serde(default)]
    pub verified_modules: Vec<Vec<String>>,
    #[serde(default)]
    pub checked_modules: Vec<Vec<String>>,
}

impl Report {
    pub fn checked(success: bool, verification_reused: bool) -> Self {
        Self {
            version: 2,
            verified_modules: Vec::new(),
            checked_modules: Vec::new(),
            execution: Execution::default(),
            checking: sema::QueryStats::default(),
            storage: sema::artifact_store::CacheStoreStats::default(),
            outcome: if success {
                Outcome::Accepted
            } else {
                Outcome::Rejected
            },
            cache: Cache {
                verification_reused,
            },
        }
    }

    pub fn internal_error() -> Self {
        Self {
            outcome: Outcome::InternalError,
            ..Self::checked(false, false)
        }
    }

    pub fn write(&self, path: &Path) -> anyhow::Result<()> {
        let temporary = path.with_extension(format!("json.{}.tmp", std::process::id()));
        let mut file = File::create(&temporary)?;
        let mut bytes = serde_json::to_vec_pretty(self)?;
        bytes.push(b'\n');
        file.write_all(&bytes)?;
        file.sync_all()?;
        std::fs::rename(temporary, path)?;
        Ok(())
    }
}
