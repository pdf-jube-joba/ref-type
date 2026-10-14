//! Stable observations of a CLI invocation, independent of cache representation.
use serde::{Deserialize, Serialize};
use std::{fs::File, io::Write, path::Path};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Outcome {
    Accepted,
    Rejected,
    InternalError,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Cache {
    pub verification_reused: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Report {
    pub version: u32,
    pub outcome: Outcome,
    pub cache: Cache,
}

impl Report {
    pub fn checked(success: bool, verification_reused: bool) -> Self {
        Self {
            version: 1,
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
        let mut file = File::create(path)?;
        serde_json::to_writer_pretty(&mut file, self)?;
        file.write_all(b"\n")?;
        Ok(())
    }
}
