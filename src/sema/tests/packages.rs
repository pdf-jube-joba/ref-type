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

fn cache_files(cache: &Cache, category: &str) -> Vec<PathBuf> {
    let mut pending = vec![cache.0.join("v2").join(category)];
    let mut files = Vec::new();
    while let Some(directory) = pending.pop() {
        let Ok(entries) = fs::read_dir(directory) else {
            continue;
        };
        for entry in entries {
            let path = entry.unwrap().path();
            if path.is_dir() {
                pending.push(path);
            } else {
                files.push(path);
            }
        }
    }
    files
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
fn workspace_checks_and_forces_all_members_while_reusing_external_dependencies() {
    let cache = Cache::new();
    let mut snapshot = project("app");
    snapshot.insert(
        "/virtual/ref.toml",
        "[workspace]\npackages = ['app', 'other']\n",
    );
    snapshot.insert(
        "/virtual/other/ref.toml",
        "[package]\nname = 'other'\n[dependencies]\nbase = {path = '../base'}\n",
    );
    snapshot.insert(
        "/virtual/other/src/root.ref",
        r"\module Main { \import base.Core[] \as B; \definition p: \Prop := B.P; }",
    );
    let mut workspace = SourceSnapshot::new("/virtual");
    for (path, source) in snapshot.files() {
        workspace.insert(path, source.text.clone());
    }
    let result = Database::with_cache(&cache.0).check(&workspace);
    assert!(result.is_success(), "{result:?}");
    assert_eq!(result, clean(&workspace));
    assert!(
        result
            .modules
            .iter()
            .any(|module| module.path == ["other", "Main"])
    );
    let mut warm = Database::with_cache(&cache.0);
    assert_eq!(warm.check(&workspace), result);
    assert_eq!(warm.stats().checked_modules, 0);
    let mut forced = Database::with_cache(&cache.0);
    assert_eq!(
        forced.check_with_options(
            &workspace,
            &CheckOptions {
                force_local: true,
                ..Default::default()
            }
        ),
        result
    );
    assert_eq!(forced.stats().package_hits, 1);
    assert_eq!(forced.stats().checked_modules, 4);
    let broken = workspace.with_file(
        "/virtual/other/src/root.ref",
        r"\module Main { \definition bad: \Prop := \Set; }",
    );
    assert!(!Database::with_cache(&cache.0).check(&broken).is_success());
    assert!(
        Database::new()
            .module(&broken, &["app".into()])
            .is_success()
    );
}

thread_local! {
    static INTERRUPT_MODULE: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
    static READY_TO_INTERRUPT: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

fn interrupt_checkpoint(event: &sema::ProgressEvent) {
    match event {
        sema::ProgressEvent::ModuleFinished { path, .. } => {
            if INTERRUPT_MODULE.with_borrow(|target| target.as_deref() == Some(&path.join("."))) {
                READY_TO_INTERRUPT.set(true);
            }
        }
        sema::ProgressEvent::CheckpointSaved { .. } if READY_TO_INTERRUPT.replace(false) => {
            panic!("simulate termination after a durable checkpoint");
        }
        _ => {}
    }
}

fn interrupted(cache: &Cache, snapshot: &SourceSnapshot, module: &str) {
    INTERRUPT_MODULE.with_borrow_mut(|target| *target = Some(module.into()));
    READY_TO_INTERRUPT.set(false);
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        Database::with_cache(&cache.0).check_with_options(
            snapshot,
            &CheckOptions {
                checkpoint_interval: Some(std::time::Duration::ZERO),
                progress_events: Some(interrupt_checkpoint),
                ..Default::default()
            },
        )
    }));
    INTERRUPT_MODULE.with_borrow_mut(|target| *target = None);
    assert!(
        outcome.is_err(),
        "expected a saved checkpoint after {module}"
    );
}

fn resumable_project() -> SourceSnapshot {
    project("app").with_file(
        "/virtual/app/src/root.ref",
        r"
        \module First {
            \import base.Core[] \as B;
            \definition p: \Prop := B.P;
            \infer p;
            \module Child(A: \Set) { \definition id(x: A): A := x; }
            \definition q(x: B.Unit): B.Unit := Child[A := B.Unit].id x;
            \infer q;
        }
        \module Last {
            \import \root.First[] \as F;
            \import base.Core[] \as B;
            \import F.Child[A := B.Unit] \as I;
            \definition value: B.Unit := I.id B.Unit::unit;
            \infer value;
        }",
    )
}

#[test]
fn module_checkpoint_resumes_an_unfinished_package_with_outputs_and_children() {
    let cache = Cache::new();
    let snapshot = resumable_project();
    // A child finishes while its parent still has later checking steps.
    interrupted(&cache, &snapshot, "app.First.Child");
    interrupted(&cache, &snapshot, "app.First");
    let mut resumed = Database::with_cache(&cache.0);
    let result = resumed.check(&snapshot);
    assert_eq!(result, clean(&snapshot));
    assert!(result.is_success());
    assert_eq!(resumed.stats().checkpoint_hits, 1, "{:?}", resumed.stats());
    assert_eq!(resumed.stats().package_hits, 1);
    assert!(resumed.stats().reused_modules > 3);
    assert!(resumed.stats().checked_modules < 4);
    assert!(cache_files(&cache, "checkpoints").is_empty());
    let mut warm = Database::with_cache(&cache.0);
    assert_eq!(warm.check(&snapshot), result);
    assert_eq!(warm.stats().checked_modules, 0);
}

#[test]
fn module_checkpoints_invalidate_on_edits_settings_force_and_damage() {
    for mode in [
        "source",
        "dependency",
        "settings",
        "force",
        "force_local",
        "corrupt",
        "partial_query",
    ] {
        let cache = Cache::new();
        let mut snapshot = resumable_project();
        interrupted(&cache, &snapshot, "app.First.Child");
        let mut options = CheckOptions::default();
        match mode {
            "source" => {
                snapshot = snapshot.with_file(
                    "/virtual/app/src/Extra.ref",
                    r"\definition p: \Prop := \forall (P: \Prop) -> P -> P;",
                )
            }
            "dependency" => {
                snapshot = snapshot.with_file(
                    "/virtual/base/src/Extra.ref",
                    r"\definition p: \Prop := \forall (P: \Prop) -> P -> P;",
                )
            }
            "settings" => options.configuration = "changed".into(),
            "force" => options.force = true,
            "force_local" => options.force_local = true,
            "corrupt" => {
                for path in cache_files(&cache, "checkpoints") {
                    fs::write(path, b"truncated").unwrap();
                }
            }
            _ => {}
        }
        let mut resumed = Database::with_cache(&cache.0);
        let result = if mode == "partial_query" {
            resumed.module_with_options(&snapshot, &["app".into(), "First".into()], &options)
        } else {
            resumed.check_with_options(&snapshot, &options)
        };
        assert!(result.is_success(), "{mode}: {result:?}");
        if mode != "partial_query" {
            assert_eq!(result, clean(&snapshot), "{mode}");
        }
        assert_eq!(resumed.stats().checkpoint_hits, 0, "{mode}");
    }
}

#[test]
fn resumed_package_still_checks_errors_after_the_checkpoint() {
    let cache = Cache::new();
    let snapshot = resumable_project();
    let root = std::path::Path::new("/virtual/app/src/root.ref");
    let source = snapshot
        .source(root)
        .unwrap()
        .text
        .replace(r"\infer value;", r"\definition bad: B.Unit := \Set;");
    let snapshot = snapshot.with_file(root, source);
    interrupted(&cache, &snapshot, "app.First.Child");
    let mut resumed = Database::with_cache(&cache.0);
    let result = resumed.check(&snapshot);
    assert!(!result.is_success());
    assert_eq!(result, clean(&snapshot));
    assert_eq!(resumed.stats().checkpoint_hits, 1);
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
    for path in cache_files(&cache, "objects") {
        if fs::read(&path).unwrap().get(8) == Some(&1) {
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
    let failed = full.check(&broken);
    assert!(!failed.is_success());
    assert!(
        failed
            .modules
            .iter()
            .any(|module| module.path == ["base", "Bad"]
                && module.status != sema::ModuleStatus::Verified)
    );
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
        \use V.chosen;
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
fn result_only_package_records_skip_complete_queries_and_fall_back_for_continuations() {
    let cache = Cache::new();
    let snapshot = project("app");
    let expected = Database::with_cache(&cache.0).check(&snapshot);
    assert!(expected.is_success());
    // Model a successful check whose environment exceeded the snapshot budget.
    let store = sema::artifact_store::ArtifactStore::new(&cache.0);
    for path in cache_files(&cache, "artifacts") {
        let bytes = fs::read(path).unwrap();
        let mut manifest: sema::artifact_store::StoreManifest =
            sema::artifact_store::deserialize(&bytes[40..]).unwrap();
        manifest.environment = None;
        manifest.resolver = None;
        store.publish(&manifest).unwrap();
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
    assert_eq!(changed.stats().package_hits, 1);
    assert!(changed.stats().checked_modules > 2);
}
