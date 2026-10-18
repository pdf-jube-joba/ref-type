use sema::{
    Database, SourceSnapshot,
    artifact_store::{ArtifactStore, StoreManifest},
};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ref-artifact-graph-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&path).unwrap();
        Self(path)
    }
    fn package(&self, name: &str, dependencies: &[&str], body: &str) -> PathBuf {
        let directory = self.0.join(name);
        fs::create_dir_all(directory.join("src")).unwrap();
        let mut manifest = format!("[package]\nname = '{name}'\n[dependencies]\n");
        for dependency in dependencies {
            manifest += &format!("{dependency} = {{path = '../{dependency}'}}\n");
        }
        fs::write(directory.join("ref.toml"), manifest).unwrap();
        fs::write(directory.join("src/root.ref"), body).unwrap();
        directory
    }
    fn diamond(&self) -> PathBuf {
        self.package(
            "base",
            &[],
            r"\module Core { \inductive Unit: \Set := | unit: Unit; }",
        );
        self.package("left", &["base"], r"\module Core { \import base.Core[] \as B; \definition value: B.Unit := B.Unit::unit; }");
        self.package(
            "right",
            &["base"],
            r"\module Core { \import base.Core[] \as B; \definition id[x: B.Unit]: B.Unit := x; }",
        );
        self.package("app", &["left", "right"], APP)
    }
}
const APP: &str =
    r"\module Main { \import left.Core[] \as L; \import right.Core[] \as R; \infer R.id L.value; }";
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn files(root: &Path) -> Vec<PathBuf> {
    let mut pending = vec![root.to_owned()];
    let mut result = Vec::new();
    while let Some(root) = pending.pop() {
        if let Ok(entries) = fs::read_dir(root) {
            for entry in entries {
                let path = entry.unwrap().path();
                if path.is_dir() {
                    pending.push(path);
                } else {
                    result.push(path);
                }
            }
        }
    }
    result.sort();
    result
}
fn records(directory: &Path) -> BTreeMap<String, StoreManifest> {
    let store = ArtifactStore::new(directory);
    files(&directory.join("artifacts"))
        .into_iter()
        .filter_map(|path| {
            let stem = path.file_stem()?.to_str()?;
            if stem.len() != 64 {
                return None;
            }
            let mut key = [0; 32];
            for (i, byte) in key.iter_mut().enumerate() {
                *byte = u8::from_str_radix(&stem[i * 2..i * 2 + 2], 16).ok()?;
            }
            let manifest = store.read_manifest(&key).ok()?;
            manifest.resolver.as_ref()?;
            Some((manifest.coverage.first()?.first()?.clone(), manifest))
        })
        .collect()
}
fn independent_result(snapshot: &SourceSnapshot) -> std::sync::Arc<sema::SemanticResult> {
    Database::new().check_with_options(
        snapshot,
        &sema::CheckOptions {
            collect_statistics: true,
            ..Default::default()
        },
    )
}

#[test]
fn diamond_warm_results_read_no_environment_bytes() {
    let fixture = Fixture::new();
    let entry = fixture.diamond();
    let cache = fixture.0.join("cache");
    let snapshot = SourceSnapshot::read(entry).unwrap();
    let expected = independent_result(&snapshot);
    assert!(expected.is_success(), "{expected:?}");
    assert_eq!(Database::with_cache(&cache).check(&snapshot), expected);
    let mut warm = Database::with_cache(&cache);
    assert_eq!(warm.check(&snapshot), expected);
    assert_eq!(warm.stats().checked_modules, 0);
    assert_eq!(warm.cache_store_stats().environment_read_bytes, 0);
    assert_eq!(warm.cache_store_stats().environment_imports, 0);
    assert!(warm.cache_store_stats().result_read_bytes > 0);
    let manifests = records(&cache);
    assert_eq!(manifests.len(), 4);
    assert!(
        manifests["left"]
            .dependencies
            .contains(&manifests["base"].key)
    );
    assert!(
        manifests["right"]
            .dependencies
            .contains(&manifests["base"].key)
    );
}

#[test]
fn individual_and_partial_results_complete_warm_queries_without_environment_imports() {
    for preserve_partial in [false, true] {
        let fixture = Fixture::new();
        let entry = fixture.diamond();
        let cache = fixture.0.join("cache");
        let snapshot = SourceSnapshot::read(&entry).unwrap();
        let expected = Database::with_cache(&cache).check(&snapshot);
        assert!(expected.is_success(), "{expected:?}");
        let original = records(&cache)["app"].clone();
        assert!(original.coverage.len() >= 2);
        let manifest_path = |key: &[u8; 32]| {
            let key = key
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>();
            cache
                .join("artifacts")
                .join(&key[..2])
                .join(format!("{key}.manifest"))
        };
        fs::remove_file(manifest_path(&original.key)).unwrap();
        if preserve_partial {
            // One range exists only in a package result object, while the rest
            // exists only under individual module keys published by a worker.
            let mut partial = original.clone();
            partial.key = [171; 32];
            partial.coverage.truncate(1);
            partial
                .results
                .retain(|(path, _)| partial.coverage.contains(path));
            partial.resolver = None;
            partial.environment = None;
            let store = ArtifactStore::new(&cache);
            let mut removed = 0;
            for path in files(&cache.join("artifacts")) {
                let Some(stem) = path.file_stem().and_then(|stem| stem.to_str()) else {
                    continue;
                };
                if stem.len() != 64 {
                    continue;
                }
                let mut key = [0; 32];
                for (index, byte) in key.iter_mut().enumerate() {
                    *byte = u8::from_str_radix(&stem[index * 2..index * 2 + 2], 16).unwrap();
                }
                let manifest = store.read_manifest(&key).unwrap();
                if manifest.resolver.is_none()
                    && manifest.environment.is_none()
                    && manifest.coverage == partial.coverage
                {
                    fs::remove_file(path).unwrap();
                    removed += 1;
                }
            }
            assert!(removed > 0, "individual module result fixture missing");
            store.publish(&partial).unwrap();
        }
        let mut warm = Database::with_cache(&cache);
        // Select the entry subtree to exercise individual and partial records
        // independently of the complete-snapshot result.
        assert_eq!(
            warm.module_with_options(&snapshot, &["app".into()], &Default::default()),
            expected
        );
        assert_eq!(warm.stats().checked_modules, 0);
        assert_eq!(warm.cache_store_stats().environment_read_bytes, 0);
        assert_eq!(warm.cache_store_stats().environment_imports, 0);
        assert!(warm.cache_store_stats().result_read_bytes > 0);
        assert!(warm.memory_cache_stats().module_results > 0);

        let mut forced = Database::with_cache(&cache);
        assert_eq!(
            forced.check_with_options(
                &snapshot,
                &sema::CheckOptions {
                    force_local: true,
                    ..Default::default()
                }
            ),
            expected
        );
        assert!(
            forced.stats().checked_modules > 0,
            "forcing the entry package must bypass individual result reuse"
        );
    }
}

#[test]
fn different_consumers_and_unrelated_dependencies_preserve_artifact_keys() {
    let fixture = Fixture::new();
    let entry = fixture.diamond();
    let cache = fixture.0.join("cache");
    let snapshot = SourceSnapshot::read(&entry).unwrap();
    assert!(Database::with_cache(&cache).check(&snapshot).is_success());
    let original = records(&cache);
    fixture.package(
        "extra",
        &[],
        r"\module Core { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }",
    );
    let other = fixture.package("other", &["extra", "right", "left"], APP);
    let changed = SourceSnapshot::read(other).unwrap();
    let mut database = Database::with_cache(&cache);
    let result = database.check(&changed);
    assert!(result.is_success(), "{result:?}");
    assert_eq!(result, independent_result(&changed));
    let after = records(&cache);
    for name in ["base", "left", "right"] {
        assert_eq!(original[name], after[name], "changed {name}");
    }
    assert!(database.stats().package_hits >= 3, "{:?}", database.stats());
    assert!(database.cache_store_stats().environment_read_bytes > 0);
}

#[test]
fn transitive_dependency_changes_invalidate_its_consumers() {
    let fixture = Fixture::new();
    let entry = fixture.diamond();
    let cache = fixture.0.join("cache");
    let snapshot = SourceSnapshot::read(&entry).unwrap();
    assert!(Database::with_cache(&cache).check(&snapshot).is_success());
    let original = records(&cache);
    fixture.package("base", &[], r"\module Core { \inductive Unit: \Set := | unit: Unit; \definition added: \Prop := \forall (P: \Prop) -> P -> P; }");
    let snapshot = SourceSnapshot::read(&entry).unwrap();
    let mut changed = Database::with_cache(&cache);
    let result = changed.check(&snapshot);
    assert!(result.is_success(), "{result:?}");
    assert_eq!(result, independent_result(&snapshot));
    assert_eq!(changed.stats().package_hits, 0);
    for old in original.values() {
        let current = ArtifactStore::new(&cache)
            .list_matching(&old.input)
            .unwrap();
        assert!(current.iter().any(|manifest| manifest.key == old.key));
    }
    assert!(files(&cache.join("artifacts")).len() >= 8);
}

#[test]
fn distinct_package_instances_keep_distinct_nominal_types_after_import() {
    let fixture = Fixture::new();
    let cache = fixture.0.join("cache");
    let body = r"\module Core { \inductive Unit: \Set := | unit: Unit; }";
    for name in ["first", "second"] {
        let entry = fixture.package(name, &[], body);
        assert!(
            Database::with_cache(&cache)
                .check(&SourceSnapshot::read(entry).unwrap())
                .is_success()
        );
    }
    let app=fixture.package("app",&["first","second"],r"\module Main { \import first.Core[] \as A; \import second.Core[] \as B; \definition bad: B.Unit := A.Unit::unit; }");
    let snapshot = SourceSnapshot::read(app).unwrap();
    let expected = independent_result(&snapshot);
    assert!(!expected.is_success());
    assert_eq!(Database::with_cache(&cache).check(&snapshot), expected);
}

#[test]
fn package_process_helper() {
    let Some(entry) = std::env::var_os("REF_ARTIFACT_TEST_ENTRY") else {
        return;
    };
    let cache = std::env::var_os("REF_ARTIFACT_TEST_CACHE").unwrap();
    let snapshot = SourceSnapshot::read(PathBuf::from(entry)).unwrap();
    let result = Database::with_cache(PathBuf::from(cache)).check(&snapshot);
    assert!(result.is_success(), "{result:?}");
}

#[test]
fn independently_built_processes_publish_identical_objects() {
    let fixture = Fixture::new();
    let entry = fixture.diamond();
    let mut outputs = Vec::new();
    for name in ["cache1", "cache2"] {
        let cache = fixture.0.join(name);
        let result = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "package_process_helper", "--nocapture"])
            .env("REF_ARTIFACT_TEST_ENTRY", &entry)
            .env("REF_ARTIFACT_TEST_CACHE", &cache)
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        let objects = files(&cache.join("objects"))
            .into_iter()
            .map(|path| {
                (
                    path.file_name().unwrap().to_owned(),
                    fs::read(&path).unwrap(),
                )
            })
            .collect::<BTreeMap<_, _>>();
        assert!(!objects.is_empty());
        outputs.push(objects);
    }
    assert_eq!(
        outputs[0].keys().collect::<Vec<_>>(),
        outputs[1].keys().collect::<Vec<_>>()
    );
    assert_eq!(outputs[0], outputs[1]);
}

#[test]
fn saved_locations_use_package_identity_and_relative_file() {
    #[derive(serde::Serialize, serde::Deserialize, Debug, PartialEq, Eq)]
    enum SavedSource {
        Package { root: PathBuf, relative: PathBuf },
        Standalone(PathBuf),
    }
    let roots = vec![
        PathBuf::from("/virtual/pkg"),
        PathBuf::from("/virtual/pkg/nested"),
    ];
    let id = sema::syntax::SourceId("/virtual/pkg/nested/src/root.ref".into());
    let location = sema::Location {
        file: id.0.clone(),
        range: 3..9,
    };
    let encode = || sema::artifact_store::serialize(&id).unwrap();
    let standalone = encode();
    syntax::source_reference::with_package_roots(&roots, || {
        let encoded = encode();
        let saved: SavedSource = sema::artifact_store::deserialize(&encoded).unwrap();
        assert_eq!(
            saved,
            SavedSource::Package {
                root: "/virtual/pkg/nested".into(),
                relative: "src/root.ref".into()
            }
        );
        assert_eq!(
            sema::artifact_store::deserialize::<sema::syntax::SourceId>(&encoded).unwrap(),
            id
        );
        syntax::source_reference::with_package_roots(&[], || assert_eq!(encode(), standalone));
        assert_eq!(encode(), encoded);
        let bytes = sema::artifact_store::serialize(&location).unwrap();
        assert_eq!(
            sema::artifact_store::deserialize::<sema::Location>(&bytes).unwrap(),
            location
        );
        assert_eq!(
            serde_json::to_value(&location).unwrap()["file"],
            "/virtual/pkg/nested/src/root.ref"
        );
    });
    assert_eq!(encode(), standalone);
    assert_eq!(
        serde_json::to_value(&id).unwrap(),
        "/virtual/pkg/nested/src/root.ref"
    );
    let malformed = SavedSource::Package {
        root: "/virtual/pkg".into(),
        relative: "../outside.ref".into(),
    };
    let bytes = sema::artifact_store::serialize(&malformed).unwrap();
    assert!(sema::artifact_store::deserialize::<sema::syntax::SourceId>(&bytes).is_err());
}
