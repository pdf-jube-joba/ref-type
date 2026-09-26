use sema::{Database, DeclarationId, ParseKind, SourceSnapshot};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

fn project() -> SourceSnapshot {
    let mut snapshot = SourceSnapshot::new("/virtual/root.ref");
    snapshot.insert(
        "/virtual/root.ref",
        "\\module Base;\n\\module Left;\n\\module Right;\n",
    );
    snapshot.insert(
        "/virtual/Base.ref",
        "\\definition P: \\Prop := \\forall (A: \\Prop) -> A -> A;\n",
    );
    snapshot.insert(
        "/virtual/Left.ref",
        "\\import \\root.Base[] \\as B;\n\\definition p: \\Prop := B.P;\n",
    );
    snapshot.insert(
        "/virtual/Right.ref",
        "\\definition Q: \\Prop := \\forall (A: \\Prop) -> A -> A;\n",
    );
    snapshot
}

struct Cache(PathBuf);
impl Cache {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        Self(std::env::temp_dir().join(format!(
            "ref-semantic-{}-{}",
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

#[test]
fn semantic_queries_preserve_types_definition_locations_and_references() {
    let snapshot = project();
    let mut database = Database::new();
    let result = database.check(&snapshot);
    assert!(result.is_success(), "{result:?}");
    let source = snapshot.source("/virtual/Left.ref").unwrap();
    let offset = source.text.find("B.P").unwrap();
    let definition = result.definition_at("/virtual/Left.ref", offset).unwrap();
    assert_eq!(
        definition.id,
        DeclarationId {
            module: vec!["Base".into()],
            name: "P".into()
        }
    );
    assert_eq!(definition.ty.as_deref(), Some("\\Prop"));
    assert_eq!(definition.location.file, PathBuf::from("/virtual/Base.ref"));
    assert_eq!(result.references_to(&definition.id).count(), 1);
    let limited = database.module(&snapshot, &["Right".into()]);
    assert_eq!(limited.modules.len(), 1);
    assert_eq!(database.stats().checked_modules, 0);
}

#[test]
fn unsaved_changes_reuse_unaffected_modules_and_leave_old_snapshots_intact() {
    let original = project();
    let mut database = Database::new();
    let first = database.check(&original);
    assert!(first.is_success(), "{first:?}");
    let second = database.check(&original);
    assert_eq!(first, second);
    assert_eq!(database.stats().checked_modules, 0);
    assert_eq!(database.stats().parsed_files, 0);
    let edited = original.with_file(
        "/virtual/Right.ref",
        "\\definition R: \\Prop := \\forall (A: \\Prop) -> A -> A;\n",
    );
    let changed = database.check(&edited);
    assert!(changed.is_success(), "{changed:?}");
    assert_eq!(database.stats().checked_modules, 1);
    assert_eq!(database.stats().reused_modules, 2);
    assert!(
        changed
            .declarations()
            .any(|declaration| declaration.id.name == "R")
    );
    assert_eq!(first, database.check(&original));
    assert_eq!(database.stats().checked_modules, 0);
}

#[test]
fn dependency_edits_invalidate_users_and_match_a_clean_check() {
    let original = project();
    let mut database = Database::new();
    assert!(database.check(&original).is_success());
    let edited = original.with_file("/virtual/Base.ref", "\\definition P: \\Prop := \\Set;\n");
    let changed = database.check(&edited);
    assert!(!changed.is_success());
    assert_eq!(database.stats().checked_modules, 2);
    assert_eq!(database.stats().reused_modules, 1);
    let clean = Database::new().check(&edited);
    assert_eq!(changed, clean);
    assert!(database.check(&original).is_success());
}

#[test]
fn persistent_results_survive_database_recreation_and_corruption_is_a_miss() {
    let cache = Cache::new();
    let snapshot = project();
    let first = Database::with_cache(&cache.0).check(&snapshot);
    assert!(first.is_success(), "{first:?}");
    let mut fresh = Database::with_cache(&cache.0);
    assert_eq!(first, fresh.check(&snapshot));
    assert_eq!(fresh.stats().checked_modules, 0);
    assert_eq!(fresh.stats().disk_hits, 3);
    for entry in fs::read_dir(&cache.0).unwrap() {
        fs::write(entry.unwrap().path(), "truncated").unwrap();
    }
    let mut corrupted = Database::with_cache(&cache.0);
    assert_eq!(first, corrupted.check(&snapshot));
    assert_eq!(corrupted.stats().disk_hits, 0);
    assert_eq!(corrupted.stats().checked_modules, 3);
}

#[test]
fn goals_and_earlier_declarations_remain_available_after_an_error() {
    let mut snapshot = SourceSnapshot::new("/virtual/root.ref");
    snapshot.insert(
        "/virtual/root.ref",
        r"\module M(A: \Set) {
        \definition before: \Set := A;
        \definition pending: A -> A := \fun (x: A) => ?;
    }",
    );
    let result = Database::new().check(&snapshot);
    assert!(!result.is_success());
    assert!(
        result
            .declarations()
            .any(|declaration| declaration.id.name == "before")
    );
    let goal = result.goals().next().unwrap();
    assert!(goal.context.contains('x'), "{goal:?}");
    assert_eq!(
        &snapshot.source(&goal.location.file).unwrap().text[goal.location.range.clone()],
        "?"
    );
    assert!(goal.judgement.is_some());
}

#[test]
fn parse_queries_do_not_run_elaboration() {
    let snapshot = project().with_file("/virtual/Right.ref", "\\definition Q: \\Prop := \\Set;\n");
    let mut database = Database::new();
    let first = database.parse(&snapshot, "/virtual/Right.ref", ParseKind::Module);
    let second = database.parse(&snapshot, "/virtual/Right.ref", ParseKind::Module);
    assert!(first.diagnostics.is_empty());
    assert!(std::sync::Arc::ptr_eq(&first, &second));
    assert_eq!(database.stats().checked_modules, 0);
    assert!(!database.check(&snapshot).is_success());
}

#[test]
fn inherited_import_and_macro_scope_changes_invalidate_children() {
    let mut snapshot = SourceSnapshot::new("/virtual/root.ref");
    snapshot.insert(
        "/virtual/root.ref",
        r"\module A { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }
        \module B { \import \root.A[] \as A0; \module Child { \definition p: \Prop := A0.P; } }",
    );
    let mut database = Database::new();
    assert!(database.check(&snapshot).is_success());
    let edited = snapshot.with_file(
        "/virtual/root.ref",
        r"\module A { \definition Q: \Prop := \forall (P: \Prop) -> P -> P; }
        \module B { \import \root.A[] \as A0; \module Child { \definition p: \Prop := A0.P; } }",
    );
    let changed = database.check(&edited);
    assert!(!changed.is_success());
    assert_eq!(changed, Database::new().check(&edited));
}

#[test]
fn syntax_errors_do_not_hide_independent_semantics() {
    let snapshot = project().with_file("/virtual/Left.ref", "\\definition broken: \\Prop := ;");
    let mut database = Database::new();
    let right = database.file(&snapshot, "/virtual/Right.ref");
    assert!(right.is_success(), "{right:?}");
    assert!(
        right
            .declarations()
            .any(|declaration| declaration.id.name == "Q")
    );
    let all = database.check(&snapshot);
    assert!(!all.is_success());
    assert!(
        all.declarations()
            .any(|declaration| declaration.id.name == "P")
    );
    let location = all.diagnostics[0].location.as_ref().unwrap();
    assert_eq!(location.file, PathBuf::from("/virtual/Left.ref"));
    assert_eq!(
        &snapshot.source(&location.file).unwrap().text[location.range.clone()],
        ";"
    );
}

#[test]
fn types_and_outputs_are_independent_of_other_modules_in_the_checking_batch() {
    let mut snapshot = project();
    snapshot.insert(
        "/virtual/Right.ref",
        r"\inductive Unit: \Set := | unit: Unit;
        \definition value: Unit := Unit::unit;
        \infer value;",
    );
    let mut database = Database::new();
    let all = database.check(&snapshot);
    assert!(all.is_success(), "{all:?}");
    let alone = Database::new().module(&snapshot, &["Right".into()]);
    assert!(alone.is_success(), "{alone:?}");
    assert_eq!(
        all.modules
            .iter()
            .find(|module| module.path == ["Right"])
            .unwrap(),
        &alone.modules[0]
    );
}

#[test]
fn imported_macro_changes_invalidate_expansions_and_references() {
    let mut snapshot = project();
    snapshot.insert("/virtual/Base.ref", r"\macro identity($P):= $P;");
    snapshot.insert("/virtual/Left.ref", r"\import \root.Base[] \as B;
        \use B.identity;
        \definition identityProof: \forall (P: \Prop) -> P -> P := identity!{\fun (P: \Prop) => \fun (p: P) => p};");
    let mut database = Database::new();
    let original = database.check(&snapshot);
    assert!(original.is_success(), "{original:?}");
    let edited = snapshot.with_file("/virtual/Base.ref", r"\macro identity($P):= \Set;");
    let changed = database.check(&edited);
    assert!(!changed.is_success(), "{changed:?}");
    assert_eq!(changed, Database::new().check(&edited));
}

#[test]
fn checking_configuration_is_part_of_persistent_identity() {
    let cache = Cache::new();
    let snapshot = project();
    assert!(Database::with_cache(&cache.0).check(&snapshot).is_success());
    let mut database = Database::with_cache(&cache.0);
    let result = database.check_with_options(
        &snapshot,
        &sema::CheckOptions {
            configuration: "different settings".into(),
            ..Default::default()
        },
    );
    assert!(result.is_success());
    assert_eq!(database.stats().disk_hits, 0);
    assert_eq!(database.stats().checked_modules, 3);
}

#[test]
fn changing_a_manifest_dependency_rechecks_the_imported_package() {
    let mut snapshot = SourceSnapshot::new("/virtual/app");
    snapshot.insert(
        "/virtual/app/ref.toml",
        "[package]\nname = 'app'\n[dependencies]\nbase = {path = '../base'}\n",
    );
    snapshot.insert(
        "/virtual/app/src/root.ref",
        r"\module Main { \import base.A[] \as A; \definition P: \Prop := A.P; }",
    );
    snapshot.insert("/virtual/base/ref.toml", "[package]\nname = 'base'\n");
    snapshot.insert(
        "/virtual/base/src/root.ref",
        r"\module A { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }",
    );
    let mut database = Database::new();
    let result = database.check(&snapshot);
    assert!(result.is_success(), "{result:?}");
    let edited = snapshot.with_file("/virtual/app/ref.toml", "[package]\nname = 'app'\n");
    let changed = database.check(&edited);
    assert!(!changed.is_success(), "{changed:?}");
    assert_eq!(changed, Database::new().check(&edited));
}

#[test]
fn constructors_associated_definitions_and_parameters_have_semantic_targets() {
    let mut snapshot = SourceSnapshot::new("/virtual/root.ref");
    snapshot.insert(
        "/virtual/root.ref",
        r"\module M(A: \Set) {
        \inductive Unit: \Set := | unit: Unit;
        \definition Unit::default: Unit := Unit::unit;
        \definition x: Unit := Unit::default;
        \definition T: \Set := A;
        \inductive VUnit: \VType := | unit: VUnit;
        \definition vx: VUnit := VUnit::unit;
    }",
    );
    let result = Database::new().check(&snapshot);
    assert!(result.is_success(), "{result:?}");
    let source = &snapshot.source("/virtual/root.ref").unwrap().text;
    for (text, expected) in [
        ("Unit::unit", "Unit::unit"),
        ("Unit::default;", "Unit::default"),
        (":= A;", "A"),
        ("VUnit::unit", "VUnit::unit"),
    ] {
        let start = source.find(text).unwrap();
        let offset = start + text.find("::").map_or(3, |offset| offset + 2);
        let definition = result
            .definition_at("/virtual/root.ref", offset)
            .unwrap_or_else(|| panic!("missing target for {text}: {result:?}"));
        assert_eq!(definition.id.name, expected);
        assert!(definition.ty.is_some());
    }
}

#[test]
fn macro_template_references_keep_the_definition_file() {
    let mut snapshot = project();
    snapshot.insert(
        "/virtual/Base.ref",
        r"\definition P: \Prop := \forall (P: \Prop) -> P -> P;
        \macro proposition() := P;",
    );
    snapshot.insert(
        "/virtual/Left.ref",
        r"\import \root.Base[] \as B; \use B.proposition;
        \definition result: \Prop := proposition!{};",
    );
    let result = Database::new().check(&snapshot);
    assert!(result.is_success(), "{result:?}");
    let target = DeclarationId {
        module: vec!["Base".into()],
        name: "P".into(),
    };
    let references: Vec<_> = result.references_to(&target).collect();
    assert_eq!(references.len(), 1, "{references:?}");
    assert_eq!(
        references[0].location.file,
        PathBuf::from("/virtual/Base.ref")
    );
    assert_eq!(
        &snapshot.source("/virtual/Base.ref").unwrap().text[references[0].location.range.clone()],
        "P"
    );
}

#[test]
fn unchanged_goal_results_are_shared_in_memory() {
    let snapshot = project().with_file(
        "/virtual/Right.ref",
        r"\definition pending: \forall (P: \Prop) -> P -> P := ?;",
    );
    let mut database = Database::new();
    let first = database.check(&snapshot);
    assert!(!first.is_success());
    let second = database.check(&snapshot);
    assert!(std::sync::Arc::ptr_eq(&first, &second));
    assert_eq!(database.stats().checked_modules, 0);
}

#[test]
fn repeated_module_names_have_distinct_semantic_identities() {
    let mut snapshot = SourceSnapshot::new("/virtual/root.ref");
    snapshot.insert("/virtual/root.ref", r"\module M {}");
    let mut database = Database::new();
    assert!(database.check(&snapshot).is_success());
    let edited = snapshot.with_file("/virtual/root.ref", r"\module M {} \module M {}");
    let result = database.check(&edited);
    assert!(result.is_success(), "{result:?}");
    assert_eq!(
        result
            .modules
            .iter()
            .map(|module| module.path.clone())
            .collect::<Vec<_>>(),
        [vec!["M".to_owned()], vec!["M#2".to_owned()]]
    );
}

#[test]
fn package_self_imports_use_the_same_scope_in_full_and_partial_checks() {
    let mut snapshot = SourceSnapshot::new("/virtual/pkg");
    snapshot.insert("/virtual/pkg/ref.toml", "[package]\nname = 'pkg'\n");
    snapshot.insert(
        "/virtual/pkg/src/root.ref",
        r"\module Base; \module User; \module Other;",
    );
    snapshot.insert(
        "/virtual/pkg/src/Base.ref",
        r"\definition P: \Prop := \forall (P: \Prop) -> P -> P;",
    );
    snapshot.insert(
        "/virtual/pkg/src/User.ref",
        r"\import \root.Base[] \as B; \definition x: \Prop := B.P;",
    );
    snapshot.insert(
        "/virtual/pkg/src/Other.ref",
        r"\definition P: \Prop := \forall (P: \Prop) -> P -> P;",
    );
    let mut database = Database::new();
    let first = database.check(&snapshot);
    assert!(first.is_success(), "{first:?}");
    let edited = snapshot.with_file(
        "/virtual/pkg/src/User.ref",
        r"\import \root.Base[] \as B; \definition y: \Prop := B.P;",
    );
    let changed = database.check(&edited);
    assert!(changed.is_success(), "{changed:?}");
    assert!(database.stats().reused_modules > 0);
    assert_eq!(changed, Database::new().check(&edited));
}
