//! Workspace membership and the shared default cache directory.
use crate::{Error, absolute, error::IoOperation, package_loader::parse_manifest};
use std::{
    fs,
    path::{Path, PathBuf},
};

pub(crate) struct Workspace {
    pub directory: PathBuf,
    pub packages: Vec<PathBuf>,
}

pub(crate) fn parse(
    directory: &Path,
    value: Option<&toml::Value>,
) -> Result<Option<Workspace>, Error> {
    let Some(value) = value else { return Ok(None) };
    let invalid = || Error::InvalidWorkspace {
        path: directory.join("ref.toml"),
        message: "[workspace].packages must be an array of nonempty package paths".into(),
    };
    let paths = value
        .get("packages")
        .and_then(toml::Value::as_array)
        .ok_or_else(invalid)?;
    let packages = paths
        .iter()
        .map(|path| {
            let path = path
                .as_str()
                .filter(|path| !path.is_empty())
                .ok_or_else(invalid)?;
            Ok(absolute(&directory.join(path)))
        })
        .collect::<Result<Vec<_>, Error>>()?;
    Ok(Some(Workspace {
        directory: directory.to_path_buf(),
        packages,
    }))
}

pub(crate) fn discover(directory: &Path) -> Result<Option<Workspace>, Error> {
    let directory = directory
        .canonicalize()
        .map_err(|error| Error::io(IoOperation::Open, directory, error))?;
    let mut package = None;
    for ancestor in directory.ancestors() {
        let path = ancestor.join("ref.toml");
        let text = match fs::read_to_string(&path) {
            Ok(text) => text,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
            Err(error) => return Err(Error::io(IoOperation::ReadSource, &path, error)),
        };
        let manifest = parse_manifest(ancestor, &text)?;
        if package.is_none() && manifest.package.is_some() {
            package = Some(ancestor.to_path_buf());
        }
        if let Some(workspace) = manifest.workspace {
            let member = package.as_deref().unwrap_or(&directory);
            if (manifest.package.is_some() && member == ancestor)
                || (package.is_none() && directory == ancestor)
                || workspace
                    .packages
                    .iter()
                    .any(|path| path.canonicalize().unwrap_or_else(|_| path.clone()) == member)
            {
                return Ok(Some(workspace));
            }
        }
    }
    Ok(None)
}

/// Resolve the default cache before loading sources; an explicit CLI path takes precedence.
pub fn default_cache_directory(entry: impl AsRef<Path>) -> Result<PathBuf, Error> {
    let entry = absolute(entry.as_ref());
    let directory = if entry
        .extension()
        .is_some_and(|extension| extension == "ref")
    {
        entry.parent().expect("absolute source path has a parent")
    } else {
        &entry
    };
    Ok(discover(directory)?
        .map_or_else(|| directory.to_path_buf(), |workspace| workspace.directory)
        .join("refcache"))
}
