//! Package input identity depends on the manifest graph, never its visit prefix.
use crate::cache::{Fingerprint, fingerprint};
use project::{
    SourceSnapshot,
    package_loader::{PackageInfo, PackageInstanceId},
};
use std::{collections::BTreeSet, path::Path};

#[derive(Clone, Debug)]
pub(crate) struct PackageDependency {
    pub name: String,
    pub index: usize,
    pub instance: PackageInstanceId,
    pub key: Fingerprint,
}
#[derive(Clone, Debug)]
pub(crate) struct PackageInput {
    pub key: Fingerprint,
    pub instance: PackageInstanceId,
    pub dependencies: Vec<PackageDependency>,
}

/// Every item has an explicit tag and length, including fixed-size hashes.
#[derive(Default)]
struct Input(Vec<u8>);
impl Input {
    fn field(&mut self, tag: u8, value: &[u8]) {
        self.0.push(tag);
        self.0
            .extend_from_slice(&(value.len() as u64).to_le_bytes());
        self.0.extend_from_slice(value);
    }
    fn path(&mut self, tag: u8, value: &Path) {
        self.field(tag, value.as_os_str().as_encoded_bytes());
    }
    fn finish(self) -> Fingerprint {
        fingerprint(&self.0)
    }
}

/// The loader already diagnoses cycles and returns dependencies before users.
pub(crate) fn inputs(
    snapshot: &SourceSnapshot,
    packages: &[PackageInfo],
    configuration: &str,
) -> Vec<PackageInput> {
    let mut result: Vec<PackageInput> = Vec::with_capacity(packages.len());
    for (index, package) in packages.iter().enumerate() {
        let mut input = Input::default();
        input.field(0, b"ref-type.package-input");
        input.field(1, env!("REF_SEMA_REVISION").as_bytes());
        input.field(2, configuration.as_bytes());
        input.path(3, &package.instance.0);
        input.field(4, package.name.as_bytes());
        input.field(
            5,
            &snapshot
                .content_digest(package.directory.join("ref.toml"))
                .unwrap_or_else(|| fingerprint(package.manifest.text.as_bytes())),
        );
        let mut paths: BTreeSet<_> = package
            .sources
            .iter()
            .map(|source| snapshot.identity(&source.0))
            .collect();
        // Capture additions and removals too. Nested path packages own their tree.
        paths.extend(snapshot.files().filter_map(|(path, _)| {
            let owner = packages
                .iter()
                .enumerate()
                .filter(|(_, candidate)| path.starts_with(&candidate.directory))
                .max_by_key(|(_, candidate)| candidate.directory.components().count())
                .map(|(owner, _)| owner);
            (owner == Some(index) && path.extension().is_some_and(|ext| ext == "ref"))
                .then(|| path.to_path_buf())
        }));
        for path in paths {
            input.path(6, path.strip_prefix(&package.directory).unwrap_or(&path));
            match snapshot.content_digest(&path) {
                Some(digest) => input.field(7, &digest),
                None => input.field(8, &[]),
            }
        }
        let mut dependencies = package
            .named_dependencies
            .iter()
            .map(|(name, id)| {
                let dependency = &result[id.0];
                PackageDependency {
                    name: name.clone(),
                    index: id.0,
                    instance: dependency.instance.clone(),
                    key: dependency.key,
                }
            })
            .collect::<Vec<_>>();
        dependencies.sort_by(|a, b| {
            a.name
                .cmp(&b.name)
                .then_with(|| a.instance.cmp(&b.instance))
        });
        for dependency in &dependencies {
            input.field(9, dependency.name.as_bytes());
            input.path(10, &dependency.instance.0);
            input.field(11, &dependency.key);
        }
        result.push(PackageInput {
            key: input.finish(),
            instance: package.instance.clone(),
            dependencies,
        });
    }
    result
}

/// Paths are package-relative logical module paths, with repeated occurrences
/// distinguished by the resolver's existing occurrence suffixes.
pub(crate) fn artifact_key(
    input: &Fingerprint,
    coverage: impl IntoIterator<Item = Vec<String>>,
) -> Fingerprint {
    let coverage: BTreeSet<_> = coverage.into_iter().collect();
    let mut key = Input::default();
    key.field(0, b"ref-type.package-artifact");
    key.field(1, input);
    for path in coverage {
        let mut encoded = Input::default();
        for component in path {
            encoded.field(0, component.as_bytes());
        }
        key.field(2, &encoded.0);
    }
    key.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use project::package_loader::PackageId;
    use std::{path::PathBuf, sync::Arc};
    use syntax::syntax::{SourceFile, SourceId};

    fn package(index: usize, name: &str, dependencies: Vec<(String, PackageId)>) -> PackageInfo {
        let directory = PathBuf::from(format!("/inputs/{name}"));
        let manifest = Arc::new(SourceFile {
            id: SourceId(directory.join("ref.toml")),
            text: format!("[package]\nname = '{name}'\n"),
        });
        PackageInfo {
            id: PackageId(index),
            name: name.into(),
            directory: directory.clone(),
            dependencies: dependencies.iter().map(|(_, id)| *id).collect(),
            named_dependencies: dependencies,
            instance: PackageInstanceId(directory.clone()),
            manifest,
            sources: vec![SourceId(directory.join("src/root.ref"))],
        }
    }
    fn snapshot(packages: &[PackageInfo]) -> SourceSnapshot {
        let mut snapshot = SourceSnapshot::new("/inputs/entry");
        for package in packages {
            snapshot.insert(&package.manifest.id.0, package.manifest.text.clone());
            snapshot.insert(&package.sources[0].0, "\\module M {}");
        }
        snapshot
    }
    #[test]
    fn unrelated_prefix_and_consumer_do_not_change_dependency_keys() {
        let original = vec![
            package(0, "A", vec![]),
            package(1, "B", vec![("A".into(), PackageId(0))]),
        ];
        let baseline = inputs(&snapshot(&original), &original, "");
        let reordered = vec![
            package(0, "Noise", vec![]),
            package(1, "A", vec![]),
            package(2, "B", vec![("A".into(), PackageId(1))]),
        ];
        let changed = inputs(&snapshot(&reordered), &reordered, "");
        assert_eq!(baseline[0].key, changed[1].key);
        assert_eq!(baseline[1].key, changed[2].key);
    }
    #[test]
    fn transitive_source_edits_and_manifest_edits_propagate() {
        let packages = vec![
            package(0, "A", vec![]),
            package(1, "B", vec![("A".into(), PackageId(0))]),
            package(2, "C", vec![("B".into(), PackageId(1))]),
        ];
        let snapshot = snapshot(&packages);
        let baseline = inputs(&snapshot, &packages, "");
        for edited in [
            snapshot.with_file("/inputs/A/src/root.ref", "\\module Changed {}"),
            snapshot.with_file("/inputs/A/ref.toml", "[package]\nname = 'A'\n# edit\n"),
        ] {
            let changed = inputs(&edited, &packages, "");
            assert!(
                baseline
                    .iter()
                    .zip(&changed)
                    .all(|(before, after)| before.key != after.key)
            );
        }
    }
    #[test]
    fn coverage_is_canonical_and_components_are_unambiguous() {
        let input = [17; 32];
        assert_eq!(
            artifact_key(&input, [vec!["B".into()], vec!["A".into()]]),
            artifact_key(
                &input,
                [vec!["A".into()], vec!["B".into()], vec!["A".into()]]
            )
        );
        assert_ne!(
            artifact_key(&input, [vec!["ab".into(), "c".into()]]),
            artifact_key(&input, [vec!["a".into(), "bc".into()]])
        );
    }
}
