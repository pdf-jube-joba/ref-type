//! Portable source references retain the nominal package root and a relative file.
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::{
    cell::RefCell,
    path::{Component, PathBuf},
};

thread_local! {
    static PACKAGE_ROOTS: RefCell<Vec<PathBuf>> = const { RefCell::new(Vec::new()) };
}
#[derive(Serialize, Deserialize)]
enum Reference {
    Package { root: PathBuf, relative: PathBuf },
    Standalone(PathBuf),
}

/// A thread-local encoding scope; its guard cannot move to another thread.
pub struct PackageRootsGuard {
    previous: Vec<PathBuf>,
    _thread: std::marker::PhantomData<std::rc::Rc<()>>,
}
impl Drop for PackageRootsGuard {
    fn drop(&mut self) {
        PACKAGE_ROOTS.with_borrow_mut(|roots| *roots = std::mem::take(&mut self.previous));
    }
}
/// Supply canonical package instance roots from the current immutable snapshot.
pub fn package_roots_guard(roots: &[PathBuf]) -> PackageRootsGuard {
    PackageRootsGuard {
        previous: PACKAGE_ROOTS
            .with_borrow_mut(|previous| std::mem::replace(previous, roots.to_vec())),
        _thread: std::marker::PhantomData,
    }
}
/// Nested calls restore previous roots, including when serialization panics.
pub fn with_package_roots<T>(roots: &[PathBuf], operation: impl FnOnce() -> T) -> T {
    let _guard = package_roots_guard(roots);
    operation()
}
pub fn serialize<S: Serializer>(path: &PathBuf, serializer: S) -> Result<S::Ok, S::Error> {
    if serializer.is_human_readable() {
        return path.serialize(serializer);
    }
    let reference = PACKAGE_ROOTS.with_borrow(|roots| {
        roots
            .iter()
            .filter(|root| path.starts_with(root))
            .max_by_key(|root| root.components().count())
            .map(|root| Reference::Package {
                root: root.clone(),
                relative: path.strip_prefix(root).unwrap().to_owned(),
            })
            .unwrap_or_else(|| Reference::Standalone(path.clone()))
    });
    reference.serialize(serializer)
}
pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<PathBuf, D::Error> {
    if deserializer.is_human_readable() {
        return PathBuf::deserialize(deserializer);
    }
    match Reference::deserialize(deserializer)? {
        Reference::Standalone(path) => Ok(path),
        Reference::Package { root, relative } => {
            if !root.is_absolute()
                || relative
                    .components()
                    .any(|part| !matches!(part, Component::Normal(_)))
            {
                return Err(serde::de::Error::custom(
                    "invalid package-relative source identity",
                ));
            }
            Ok(root.join(relative))
        }
    }
}
