//! Source and package loading failures with their original causes.
use std::{
    path::{Path, PathBuf},
    sync::Arc,
};

#[derive(Debug, Clone)]
pub enum Error {
    Io {
        operation: IoOperation,
        path: PathBuf,
        source: Arc<std::io::Error>,
    },
    Parse(syntax::parse::ParseError),
    InvalidExtension {
        path: PathBuf,
    },
    DuplicateSource {
        path: PathBuf,
        first: String,
        second: String,
    },
    PackageCycle {
        directory: PathBuf,
    },
    DuplicatePackage {
        name: String,
        first: PathBuf,
        second: PathBuf,
    },
    DependencyNameMismatch {
        expected: String,
        actual: String,
        path: PathBuf,
    },
    Manifest {
        path: PathBuf,
        source: Arc<toml::de::Error>,
    },
    MissingPackageName {
        path: PathBuf,
    },
    InvalidPackageName {
        name: String,
        path: PathBuf,
    },
    InvalidDependencyName {
        name: String,
        path: PathBuf,
    },
    DependenciesMustBeTable {
        path: PathBuf,
    },
    DependencyMustUsePath {
        name: String,
    },
    DependencyMustContainOnlyPath {
        name: String,
    },
    MissingDependencyPath {
        name: String,
    },
    MissingSource {
        path: PathBuf,
    },
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IoOperation {
    Open,
    ReadSource,
    ReadDirectory,
    ReadEntry,
}
impl Error {
    pub fn io(operation: IoOperation, path: &Path, source: std::io::Error) -> Self {
        Self::Io {
            operation,
            path: path.to_owned(),
            source: Arc::new(source),
        }
    }
}
impl From<syntax::parse::ParseError> for Error {
    fn from(error: syntax::parse::ParseError) -> Self {
        Self::Parse(error)
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io {
                operation,
                path,
                source,
            } => match operation {
                IoOperation::Open => write!(f, "cannot open {}: {source}", path.display()),
                IoOperation::ReadSource => write!(
                    f,
                    "failed to read source file at {}: {source}",
                    path.display()
                ),
                IoOperation::ReadDirectory | IoOperation::ReadEntry => {
                    write!(f, "cannot read {}: {source}", path.display())
                }
            },
            Self::Parse(error) => error.fmt(f),
            Self::InvalidExtension { path } => write!(
                f,
                "root source file must have the .ref extension: {}",
                path.display()
            ),
            Self::DuplicateSource {
                path,
                first,
                second,
            } => write!(
                f,
                "source file {} is used by both module '{first}' and module '{second}'",
                path.display()
            ),
            Self::PackageCycle { directory } => {
                write!(f, "cyclic package dependency at {}", directory.display())
            }
            Self::DuplicatePackage {
                name,
                first,
                second,
            } => write!(
                f,
                "package name '{name}' is used by both {} and {}",
                first.display(),
                second.display()
            ),
            Self::DependencyNameMismatch {
                expected,
                actual,
                path,
            } => write!(
                f,
                "dependency '{expected}' refers to package '{actual}' at {}",
                path.display()
            ),
            Self::Manifest { path, source } => write!(f, "invalid {}: {source}", path.display()),
            Self::MissingPackageName { path } => {
                write!(f, "{} requires [package].name", path.display())
            }
            Self::InvalidPackageName { name, path } => {
                write!(f, "invalid package name '{name}' in {}", path.display())
            }
            Self::InvalidDependencyName { name, path } => {
                write!(f, "invalid dependency name '{name}' in {}", path.display())
            }
            Self::DependenciesMustBeTable { path } => {
                write!(f, "[dependencies] must be a table in {}", path.display())
            }
            Self::DependencyMustUsePath { name } => {
                write!(f, "dependency '{name}' must use {{ path = ... }}")
            }
            Self::DependencyMustContainOnlyPath { name } => {
                write!(f, "dependency '{name}' must contain only path")
            }
            Self::MissingDependencyPath { name } => {
                write!(f, "dependency '{name}' requires a path")
            }
            Self::MissingSource { path } => write!(f, "source file is missing: {}", path.display()),
        }
    }
}
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io { source, .. } => Some(source.as_ref()),
            Self::Parse(error) => Some(error),
            Self::Manifest { source, .. } => Some(source.as_ref()),
            _ => None,
        }
    }
}

impl diagnostics::DiagnosticError for Error {
    fn diagnostic_data(&self) -> diagnostics::DiagnosticData {
        use diagnostics::DiagnosticData as Data;
        match self {
            Self::Io {
                operation,
                path,
                source,
            } => Data::new("project.Io")
                .with("operation", format!("{operation:?}"))
                .with("path", path.to_string_lossy().into_owned())
                .caused_by(
                    Data::new(format!("io.{:?}", source.kind()))
                        .with("message", source.to_string()),
                ),
            Self::Parse(error) => error.diagnostic_data(),
            Self::Manifest { path, source } => Data::new("project.Manifest")
                .with("path", path.to_string_lossy().into_owned())
                .with("start", source.span().map_or(0, |span| span.start))
                .with("end", source.span().map_or(0, |span| span.end))
                .with("message", source.message().to_owned()),
            Self::InvalidExtension { path } => Data::new("project.InvalidExtension")
                .with("path", path.to_string_lossy().into_owned()),
            Self::DuplicateSource {
                path,
                first,
                second,
            } => Data::new("project.DuplicateSource")
                .with("path", path.to_string_lossy().into_owned())
                .with("first", first.clone())
                .with("second", second.clone()),
            Self::PackageCycle { directory } => Data::new("project.PackageCycle")
                .with("directory", directory.to_string_lossy().into_owned()),
            Self::DuplicatePackage {
                name,
                first,
                second,
            } => Data::new("project.DuplicatePackage")
                .with("name", name.clone())
                .with("first", first.to_string_lossy().into_owned())
                .with("second", second.to_string_lossy().into_owned()),
            Self::DependencyNameMismatch {
                expected,
                actual,
                path,
            } => Data::new("project.DependencyNameMismatch")
                .with("expected", expected.clone())
                .with("actual", actual.clone())
                .with("path", path.to_string_lossy().into_owned()),
            Self::MissingPackageName { path } => Data::new("project.MissingPackageName")
                .with("path", path.to_string_lossy().into_owned()),
            Self::InvalidPackageName { name, path } => Data::new("project.InvalidPackageName")
                .with("name", name.clone())
                .with("path", path.to_string_lossy().into_owned()),
            Self::InvalidDependencyName { name, path } => {
                Data::new("project.InvalidDependencyName")
                    .with("name", name.clone())
                    .with("path", path.to_string_lossy().into_owned())
            }
            Self::DependenciesMustBeTable { path } => Data::new("project.DependenciesMustBeTable")
                .with("path", path.to_string_lossy().into_owned()),
            Self::DependencyMustUsePath { name } => {
                Data::new("project.DependencyMustUsePath").with("name", name.clone())
            }
            Self::DependencyMustContainOnlyPath { name } => {
                Data::new("project.DependencyMustContainOnlyPath").with("name", name.clone())
            }
            Self::MissingDependencyPath { name } => {
                Data::new("project.MissingDependencyPath").with("name", name.clone())
            }
            Self::MissingSource { path } => {
                Data::new("project.MissingSource").with("path", path.to_string_lossy().into_owned())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module_loader::{DiskSource, SourceProvider};

    #[test]
    fn failed_reads_retain_the_path_operation_and_io_cause() {
        let path = std::env::temp_dir()
            .join(format!("ref-type-missing-{}", std::process::id()))
            .join("root.ref");
        let error = DiskSource.read(&path).unwrap_err();
        let Error::Io {
            operation,
            path: actual,
            source,
        } = &error
        else {
            panic!("expected an I/O failure: {error}");
        };
        assert_eq!(*operation, IoOperation::ReadSource);
        assert_eq!(*actual, path);
        assert_eq!(source.kind(), std::io::ErrorKind::NotFound);
        assert!(std::error::Error::source(&error).is_some());
    }
}
