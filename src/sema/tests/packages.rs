use sema::{CheckOptions, Database, SourceSnapshot};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

struct Cache(PathBuf);
impl Cache {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        Self(std::env::temp_dir().join(format!(
            "ref-packages-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        )))
    }
}
impl Drop for Cache {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn project(name: &str) -> SourceSnapshot {
    let mut snapshot = SourceSnapshot::new(format!("/virtual/{name}"));
    snapshot.insert(
        format!("/virtual/{name}/ref.toml"),
        format!("[package]\nname = '{name}'\n[dependencies]\nbase = {{path = '../base'}}\n"),
    );
    snapshot.insert(
        format!("/virtual/{name}/src/root.ref"),
        r"\module Main { \import base.Core[] \as B; \definition p: \Prop := B.P; }",
    );
    snapshot.insert("/virtual/base/ref.toml", "[package]\nname = 'base'\n");
    snapshot.insert(
        "/virtual/base/src/root.ref",
        r"\module Core {
        \definition P: \Prop := \forall (P: \Prop) -> P -> P;
        \module Identity(A: \Set) { \definition id(x: A): A := x; }
        \inductive Unit: \Set := | unit: Unit;
    }",
    );
    snapshot
}

fn clean(snapshot: &SourceSnapshot) -> std::sync::Arc<sema::SemanticResult> {
    // Statistics uses the original whole-project resolver/checker path.
    Database::new().check_with_options(
        snapshot,
        &CheckOptions {
            collect_statistics: true,
            ..Default::default()
        },
    )
}

#[test]
fn package_environment_survives_a_different_caller_and_added_modules() {
    let cache = Cache::new();
    let first = project("app");
    let mut database = Database::with_cache(&cache.0);
    let result = database.check(&first);
    assert!(result.is_success(), "{result:?}");
    assert_eq!(result, clean(&first));
    assert_eq!(database.stats().package_writes, 2);
    let second = project("other").with_file(
        "/virtual/other/src/root.ref",
        r"
        \module Extra { \definition Q: \Prop := \forall (Q: \Prop) -> Q -> Q; }
        \module Main {
            \import base.Core[] \as B;
            \import base.Core[].Identity[A := B.Unit] \as I;
            \definition value: B.Unit := I.id B.Unit::unit;
            \infer value;
        }",
    );
    let mut restored = Database::with_cache(&cache.0);
    let result = restored.check(&second);
    assert!(result.is_success(), "{result:?}");
    assert_eq!(result, clean(&second));
    assert_eq!(restored.stats().package_hits, 1, "{:?}", restored.stats());
    assert_eq!(restored.stats().checked_modules, 3);
    let mut warm = Database::with_cache(&cache.0);
    assert_eq!(warm.check(&second), result);
    assert_eq!(warm.stats().checked_modules, 0);
    assert_eq!(warm.stats().package_hits, 2);
    assert_eq!(warm.stats().environment_hits, 0);
}

#[test]
fn package_source_settings_and_corruption_invalidate_artifacts() {
    let cache = Cache::new();
    let snapshot = project("app");
    assert!(Database::with_cache(&cache.0).check(&snapshot).is_success());
    let changed = snapshot.with_file(
        "/virtual/base/src/root.ref",
        r"\module Core { \definition P: \Prop := \forall (P: \Prop) -> P; }",
    );
    let mut database = Database::with_cache(&cache.0);
    assert_eq!(database.check(&changed), clean(&changed));
    assert_eq!(database.stats().package_hits, 0);
    let mut settings = Database::with_cache(&cache.0);
    assert!(
        settings
            .check_with_options(
                &snapshot,
                &CheckOptions {
                    configuration: "different".into(),
                    ..Default::default()
                }
            )
            .is_success()
    );
    assert_eq!(settings.stats().package_hits, 0);
    for file in fs::read_dir(&cache.0).unwrap() {
        let path = file.unwrap().path();
        if path.extension().is_some_and(|extension| extension == "pkg") {
            fs::write(path, b"broken").unwrap();
        }
    }
    let mut damaged = Database::with_cache(&cache.0);
    assert_eq!(damaged.check(&snapshot), clean(&snapshot));
    assert_eq!(damaged.stats().package_hits, 0);
}

#[test]
fn forced_local_check_restores_dependencies_and_partial_queries_remain_partial() {
    let cache = Cache::new();
    let snapshot = project("app");
    assert!(Database::with_cache(&cache.0).check(&snapshot).is_success());
    let mut local = Database::with_cache(&cache.0);
    assert_eq!(
        local.check_with_options(
            &snapshot,
            &CheckOptions {
                force_local: true,
                ..Default::default()
            }
        ),
        clean(&snapshot)
    );
    assert_eq!(local.stats().package_hits, 1);
    assert_eq!(local.stats().checked_modules, 2);
    let mut forced = Database::with_cache(&cache.0);
    assert!(
        forced
            .check_with_options(
                &snapshot,
                &CheckOptions {
                    force: true,
                    ..Default::default()
                }
            )
            .is_success()
    );
    assert_eq!(forced.stats().package_hits, 0);
    let broken = snapshot.with_file(
        "/virtual/base/src/root.ref",
        r"
        \module Core { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }
        \module Bad { \definition bad: \Prop := \Set; }",
    );
    let partial_cache = Cache::new();
    let mut partial = Database::with_cache(&partial_cache.0);
    let selected = partial.module_with_options(&broken, &["app".into()], &Default::default());
    assert!(selected.is_success(), "{selected:?}");
    let mut full = Database::with_cache(&partial_cache.0);
    assert!(!full.check(&broken).is_success());
    assert_eq!(full.stats().package_hits, 0);
}

#[test]
fn restored_package_keeps_macros_structures_reflection_and_source_locations() {
    let cache = Cache::new();
    let snapshot = project("app").with_file(
        "/virtual/base/src/root.ref",
        r"
        \module Core {
            \definition P: \Prop := \forall (P: \Prop) -> P -> P;
            \inductive Unit: \VType := | unit: Unit;
            \definition computation: \Box[\F(Unit)] := \box[_](\return(Unit::unit));
            \module Values(A: \Set, a: A) {
                \structure Box: \Set := { value: A, };
                \definition boxed: Box := Box { value := a };
                \macro chosen() := inner!{};
                \macro inner() := a;
            }
        }",
    );
    assert!(Database::with_cache(&cache.0).check(&snapshot).is_success());
    let source = r"\module Main {
        \import base.Core[] \as B;
        \import base.Core[].Values[A := B.Unit^, a := B.Unit^::unit] \as V;
        \use V::chosen;
        \check V.Box::value V.boxed: B.Unit^;
        \definition law: chosen!{} = B.Unit^::unit := \refl(B.Unit^::unit);
        \normalize \squash[_](B.computation);
    }";
    let edited = snapshot.with_file("/virtual/app/src/root.ref", source);
    let mut restored = Database::with_cache(&cache.0);
    let result = restored.check(&edited);
    assert!(result.is_success(), "{result:?}");
    assert_eq!(restored.stats().package_hits, 1);
    assert_eq!(result, clean(&edited));
    let target = result
        .definition_at("/virtual/app/src/root.ref", source.find("chosen!").unwrap())
        .unwrap();
    assert_eq!(target.id.name, "chosen");
    assert_eq!(
        target.location.file,
        PathBuf::from("/virtual/base/src/root.ref")
    );
}

#[test]
fn transitive_dependency_edits_invalidate_the_whole_dependent_prefix() {
    let cache = Cache::new();
    let mut snapshot = project("app");
    snapshot.insert(
        "/virtual/base/ref.toml",
        "[package]\nname = 'base'\n[dependencies]\nleaf = {path = '../leaf'}\n",
    );
    snapshot.insert("/virtual/leaf/ref.toml", "[package]\nname = 'leaf'\n");
    snapshot.insert(
        "/virtual/leaf/src/root.ref",
        r"\module Logic { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }",
    );
    snapshot.insert(
        "/virtual/base/src/root.ref",
        r"\module Core { \import leaf.Logic[] \as L; \definition P: \Prop := L.P; }",
    );
    assert!(Database::with_cache(&cache.0).check(&snapshot).is_success());
    let edited = snapshot.with_file(
        "/virtual/leaf/src/root.ref",
        r"\module Logic { \definition P: \Prop := \forall (P: \Prop) -> P; }",
    );
    let mut database = Database::with_cache(&cache.0);
    assert_eq!(database.check(&edited), clean(&edited));
    assert_eq!(database.stats().package_hits, 0);
    assert_eq!(database.stats().checked_modules, 6);
}

#[test]
fn result_only_package_records_skip_complete_queries_and_fall_back_for_continuations() {
    use sha2::{Digest, Sha256};
    let cache = Cache::new();
    let snapshot = project("app");
    let expected = Database::with_cache(&cache.0).check(&snapshot);
    assert!(expected.is_success());
    // Model a successful check whose environment exceeded the snapshot budget.
    for file in fs::read_dir(&cache.0).unwrap() {
        let path = file.unwrap().path();
        if !path.extension().is_some_and(|extension| extension == "pkg") {
            continue;
        }
        let mut bytes = fs::read(&path).unwrap();
        let length = u64::from_le_bytes(bytes[72..80].try_into().unwrap()) as usize;
        bytes.truncate(80 + length);
        let checksum = Sha256::digest(&bytes[72..]);
        bytes[40..72].copy_from_slice(&checksum);
        fs::write(path, bytes).unwrap();
    }
    let mut warm = Database::with_cache(&cache.0);
    assert_eq!(warm.check(&snapshot), expected);
    assert_eq!(warm.stats().package_hits, 2);
    assert_eq!(warm.stats().checked_modules, 0);
    let edited = snapshot.with_file(
        "/virtual/app/src/root.ref",
        r"\module Main { \import base.Core[] \as B; \definition q: \Prop := B.P; }",
    );
    let mut changed = Database::with_cache(&cache.0);
    assert_eq!(changed.check(&edited), clean(&edited));
    assert_eq!(changed.stats().package_hits, 0);
    assert!(changed.stats().checked_modules > 0);
}
