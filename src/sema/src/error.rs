//! Cache failures retain serialization and filesystem causes.
use std::path::PathBuf;

#[derive(Debug)]
pub enum CacheError {
    Serialization(serde_json::Error),
    Io {
        operation: CacheOperation,
        path: PathBuf,
        source: std::io::Error,
    },
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CacheOperation {
    CreateDirectory,
    WriteRecord,
}
impl From<serde_json::Error> for CacheError {
    fn from(error: serde_json::Error) -> Self {
        Self::Serialization(error)
    }
}
impl std::fmt::Display for CacheError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Serialization(error) => error.fmt(f),
            Self::Io {
                operation,
                path,
                source,
            } => write!(f, "{operation:?} {}: {source}", path.display()),
        }
    }
}
impl std::error::Error for CacheError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Serialization(error) => Some(error),
            Self::Io { source, .. } => Some(source),
        }
    }
}
