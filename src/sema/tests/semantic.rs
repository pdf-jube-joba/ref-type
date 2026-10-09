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

#[test]
fn editing_std_nat_basic_program_preserves_termination_imports() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../libs/std");
    let file = root.join("src/Data/Nat/Basic/Program.ref");
    let snapshot = SourceSnapshot::read(&root).unwrap();
    let mut database = Database::new();
    let first = database.file(&snapshot, &file);
    assert!(first.is_success(), "{:?}", first.diagnostics);
    let text = &snapshot.source(&file).unwrap().text;
    let edited = snapshot.with_file(
        &file,
        format!(
            r"{text}
\definition environmentProbe: \Prop := \forall (P: \Prop) -> P -> P;"
        ),
    );
    let changed = database.file(&edited, &file);
    assert!(changed.is_success(), "{:?}", changed.diagnostics);
    assert_eq!(database.stats().environment_hits, 1);
    assert_eq!(changed, Database::new().file(&edited, &file));
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
fn temporary_module_dependencies_invalidate_cached_users() {
    let original = project().with_file(
        "/virtual/Left.ref",
        r"\definition p: \Prop := \root.Base[].P;",
    );
    let mut database = Database::new();
    let initial = database.check(&original);
    assert!(initial.is_success(), "{initial:?}");
    assert_eq!(database.check(&original), initial);
    assert_eq!(database.stats().checked_modules, 0);
    let edited = original.with_file("/virtual/Base.ref", r"\definition P: \Set := \Prop;");
    let changed = database.check(&edited);
    assert!(!changed.is_success(), "{changed:?}");
    assert_eq!(changed, Database::new().check(&edited));
    assert!(database.check(&original).is_success());
}

#[test]
fn cached_temporary_modules_preserve_local_contexts() {
    let mut snapshot = SourceSnapshot::new("/virtual/root.ref");
    snapshot.insert("/virtual/root.ref", r"\module Library; \module Use;");
    snapshot.insert(
        "/virtual/Library.ref",
        r"
        \module Family(A: \Set) { \structure Box: \Set { value: A, } }
        \definition get(A: \Set)(x: Family[A := A].Box): A := x.value;
        \inductive Unit: \VType := | unit: Unit;
        \module Value(x: Unit) { \definition value: Unit := x; }
        \definition identity(x: Unit): \F(Unit) := \return Value[x := x].value;
    ",
    );
    let user = r"\import \root.Library[] \as L;
        \definition beta(x: L.Unit^): L.identity^ x = x := \refl(x);
        \definition get(A: \Set)(x: L.Family[A := A].Box): A := L.get A x;
    ";
    snapshot.insert("/virtual/Use.ref", user);
    let cache = Cache::new();
    let initial = Database::with_cache(&cache.0).check(&snapshot);
    assert!(initial.is_success(), "{initial:?}");
    let edited = snapshot.with_file(
        "/virtual/Use.ref",
        format!("{user}\n\\definition p: \\Prop := \\forall (P: \\Prop) -> P -> P;"),
    );
    let mut restored = Database::with_cache(&cache.0);
    let result = restored.check(&edited);
    assert!(result.is_success(), "{result:?}");
    assert!(
        restored.stats().environment_hits > 0,
        "{:?}",
        restored.stats()
    );
    assert_eq!(result, Database::new().check(&edited));
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

#[test]
fn block_let_errors_cover_only_the_failing_statement() {
    let cases = [
        (
            r"\let x: A := a \then
              \let bad: A := \Prop \then
              \return x",
            r"\let bad: A := \Prop \then",
        ),
        (
            r"\let bad: A := \block {
                  \let inner: A := \Prop \then
                  \return a
              } \then
              \return a",
            r"\let inner: A := \Prop \then",
        ),
        (
            r"\let bad: A := \block { \return \Prop } \then
              \return a",
            r"\let bad: A := \block { \return \Prop } \then",
        ),
    ];
    for (body, expected) in cases {
        let text = format!(
            "\\definition test: \\forall (A: \\Set) -> A -> A := \\block {{\n\\fun (A: \\Set) (a: A) \\then\n{body}\n}};"
        );
        let mut snapshot = SourceSnapshot::new("/virtual/root.ref");
        snapshot.insert("/virtual/root.ref", "\\module Test;");
        snapshot.insert("/virtual/Test.ref", text.clone());
        let result = Database::new().check(&snapshot);
        assert_eq!(result.diagnostics.len(), 1, "{result:?}");
        let diagnostic = &result.diagnostics[0];
        assert!(
            diagnostic.message.contains("Local definition"),
            "{diagnostic:?}"
        );
        let location = diagnostic.location.as_ref().unwrap();
        assert_eq!(location.file, PathBuf::from("/virtual/Test.ref"));
        assert_eq!(&text[location.range.clone()], expected);
    }
}

#[test]
fn block_result_errors_do_not_point_at_a_successful_let() {
    let text = r"\definition test: \forall (A: \Set) -> A -> A := \block {
        \fun (A: \Set) (a: A) \then
        \let x: A := a \then
        \return \Prop
    };";
    let mut snapshot = SourceSnapshot::new("/virtual/root.ref");
    snapshot.insert("/virtual/root.ref", "\\module Test;");
    snapshot.insert("/virtual/Test.ref", text);
    let result = Database::new().check(&snapshot);
    assert_eq!(result.diagnostics.len(), 1, "{result:?}");
    let location = result.diagnostics[0].location.as_ref().unwrap();
    assert_eq!(&text[location.range.clone()], text);
}

#[test]
fn inspection_and_named_inference_diagnostics_reach_editor_queries() {
    let mut snapshot = SourceSnapshot::new("/virtual/root.ref");
    let source = r"\module M(A: \VType) {
        \definition pending: A ~> \F(A) := \cfun (x: ?) => \return _12;
    }";
    snapshot.insert("/virtual/root.ref", source);
    let result = Database::new().check(&snapshot);
    assert!(!result.is_success());
    let goals: Vec<_> = result.goals().collect();
    assert_eq!(goals.len(), 2, "{goals:?}");
    let inspection = goals
        .iter()
        .find(|goal| goal.name.starts_with('?'))
        .unwrap();
    assert!(inspection.state.starts_with("solved"), "{inspection:?}");
    assert!(
        inspection
            .solution
            .as_ref()
            .is_some_and(|ty| ty.contains('A'))
    );
    assert_eq!(&source[inspection.location.range.clone()], "?");
    let inferred = goals.iter().find(|goal| goal.name == "_12").unwrap();
    assert!(inferred.context.contains("x:"), "{inferred:?}");
    assert!(inferred.context.contains("A:"), "{inferred:?}");
    assert!(
        inferred
            .judgement
            .as_ref()
            .is_some_and(|ty| ty.contains('A'))
    );
    assert_eq!(&source[inferred.occurrences[0].range.clone()], "_12");
}

#[test]
fn nested_child_edits_invalidate_parent_users_and_match_clean_checks() {
    let mut snapshot = SourceSnapshot::new("/virtual/root.ref");
    snapshot.insert("/virtual/root.ref", r"\module Parent; \module Consumer;");
    snapshot.insert(
        "/virtual/Parent.ref",
        r"
        \inductive Unit: \Set := | first: Unit | second: Unit;
        \definition Carrier: \Set := Unit;
        \module Math;
        \import \root.Parent[].Math[].Specification[].Def[] \as D;
        \definition result: Carrier := D.result;
    ",
    );
    snapshot.insert("/virtual/Parent/Math.ref", r"\module Specification;");
    snapshot.insert("/virtual/Parent/Math/Specification.ref", r"\module Def;");
    let file = "/virtual/Parent/Math/Specification/Def.ref";
    snapshot.insert(file, r"\definition result: Carrier := Unit::first;");
    snapshot.insert(
        "/virtual/Consumer.ref",
        r"
        \import \root.Parent[] \as P;
        \definition result: P.Carrier := P.result;
    ",
    );
    let cache = Cache::new();
    let mut database = Database::with_cache(&cache.0);
    let first = database.check(&snapshot);
    assert!(first.is_success(), "{first:?}");
    assert_eq!(first, Database::with_cache(&cache.0).check(&snapshot));
    let edited = snapshot.with_file(file, r"\definition result: Carrier := Unit::second;");
    let changed = database.check(&edited);
    assert!(changed.is_success(), "{changed:?}");
    assert_ne!(first, changed);
    assert_eq!(changed, Database::new().check(&edited));
    assert_eq!(changed, Database::with_cache(&cache.0).check(&edited));
}

#[test]
fn structure_members_preserve_source_identity_and_invalidate_users() {
    let cache = Cache::new();
    let mut snapshot = SourceSnapshot::new("/virtual/root.ref");
    snapshot.insert(
        "/virtual/root.ref",
        "\\module Shapes;\n\\module Use;\n\\module Other;\n",
    );
    snapshot.insert(
        "/virtual/Shapes.ref",
        r"\inductive Unit: \Set := | unit: Unit;
\structure Relation { A: \Set, R: A -> A -> \Prop, }
\definition Equality(A: \Set): Relation := Relation { A := A, R := \fun(x,y:A) => x = y, };",
    );
    snapshot.insert(
        "/virtual/Use.ref",
        r"\import \root.Shapes[] \as S;
\definition same: (S.Equality S.Unit).R S.Unit::unit S.Unit::unit := \refl(S.Unit::unit);",
    );
    snapshot.insert(
        "/virtual/Other.ref",
        r"\definition Truth: \Prop := \forall(P: \Prop) -> P -> P;",
    );
    let mut database = Database::with_cache(&cache.0);
    let first = database.check(&snapshot);
    assert!(first.is_success(), "{first:?}");
    let field = first
        .declarations()
        .find(|declaration| declaration.id.name == "Relation::R")
        .unwrap();
    assert_eq!(field.kind, "field");
    assert_eq!(field.location.file, PathBuf::from("/virtual/Shapes.ref"));
    assert_eq!(
        &snapshot.source(&field.location.file).unwrap().text[field.location.range.clone()],
        "R"
    );
    assert!(first.references_to(&field.id).count() > 0);
    assert!(
        first
            .declarations()
            .any(|declaration| declaration.id.name == "Equality" && declaration.ty.is_some())
    );
    let mut fresh = Database::with_cache(&cache.0);
    assert_eq!(first, fresh.check(&snapshot));
    assert_eq!(fresh.stats().checked_modules, 0);
    let edited = snapshot.with_file(
        "/virtual/Shapes.ref",
        snapshot
            .source("/virtual/Shapes.ref")
            .unwrap()
            .text
            .replace(
                "R: A -> A -> \\Prop",
                "R: A -> A -> \\Prop, copy: A -> A := \\fun(x: A) => x",
            ),
    );
    let changed = database.check(&edited);
    assert!(changed.is_success(), "{changed:?}");
    assert_eq!(database.stats().reused_modules, 1);
    assert_eq!(changed, Database::new().check(&edited));
}

#[test]
fn structure_namespace_contains_source_declarations() {
    let cache = Cache::new();
    let mut snapshot = SourceSnapshot::new("/virtual/root.ref");
    snapshot.insert("/virtual/root.ref", "\\module Shapes;\n");
    snapshot.insert(
        "/virtual/Shapes.ref",
        r"\inductive Unit: \Set := | unit: Unit;
\structure S: \Set { Raw: Unit, law: Raw = Raw, }
\definition s: S := S { Raw := Unit::unit, law := \refl(Unit::unit), };",
    );
    let result = Database::with_cache(&cache.0).check(&snapshot);
    assert!(result.is_success(), "{result:?}");
    let names = result
        .declarations()
        .map(|declaration| declaration.id.name.as_str())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        names,
        std::collections::BTreeSet::from(["S", "S::Raw", "S::law", "Unit", "Unit::unit", "s",])
    );
    let mut fresh = Database::with_cache(&cache.0);
    assert_eq!(result, fresh.check(&snapshot));
    assert_eq!(fresh.stats().checked_modules, 0);
}

#[test]
fn edited_user_restores_dependency_environment_in_memory_and_from_disk() {
    let snapshot = project();
    let cache = Cache::new();
    let mut database = Database::with_cache(&cache.0);
    assert!(database.check(&snapshot).is_success());
    assert!(database.stats().environment_writes > 0);
    assert_eq!(database.stats().cache_write_failures, 0);
    for (index, mut database) in [database, Database::with_cache(&cache.0)]
        .into_iter()
        .enumerate()
    {
        let edited = snapshot.with_file(
            "/virtual/Left.ref",
            format!(
                "\\import \\root.Base[] \\as B;\n\\definition changed{index}: \\Prop := B.P;\n"
            ),
        );
        let clean = Database::new().check(&edited);
        assert!(clean.is_success(), "{clean:?}");
        assert_eq!(database.check(&edited), clean);
        assert_eq!(
            database.stats().checked_modules,
            1,
            "{:?}",
            database.stats()
        );
        assert_eq!(database.stats().restored_modules, 1);
        assert_eq!(database.stats().environment_hits, 1);
    }
}

#[test]
fn restored_environment_preserves_instantiations_program_reflection_and_outputs() {
    let mut snapshot = SourceSnapshot::new("/virtual/root.ref");
    snapshot.insert(
        "/virtual/root.ref",
        r"\module Source; \module Library; \module Use;",
    );
    snapshot.insert(
        "/virtual/Source.ref",
        r"
\inductive Box[X: \VType]: \VType := | box: X -> Box;
\module Record(A: \Set, a: A) {
  \structure Box: \Set := { value: A, };
  \definition boxed: Box := Box { value := a };
}",
    );
    snapshot.insert(
        "/virtual/Library.ref",
        r"
\import \root.Source[] \as S;
\inductive Unit: \VType := | unit: Unit;
\definition boxed: S.Box[Unit] := S.Box[Unit]::box Unit::unit;
\definition package: \Box[\F(S.Box[Unit])] := \box[_](\return(boxed));
\import \root.Source[].Record[A := Unit^, a := Unit^::unit] \as R;
\check R.Box::value R.boxed: Unit^;
\normalize \squash[_](package);
",
    );
    let user = r"\import \root.Library[] \as L; \infer L.boxed^;";
    snapshot.insert("/virtual/Use.ref", user);
    let cache = Cache::new();
    let first = Database::with_cache(&cache.0).check(&snapshot);
    assert!(first.is_success(), "{first:?}");
    let edited = snapshot.with_file(
        "/virtual/Use.ref",
        format!("{user}\n\\normalize \\squash[_](L.package);"),
    );
    let mut database = Database::with_cache(&cache.0);
    let result = database.check(&edited);
    assert!(result.is_success(), "{result:?}");
    assert_eq!(
        database.stats().checked_modules,
        1,
        "{:?}",
        database.stats()
    );
    assert_eq!(database.stats().environment_hits, 1);
    assert_eq!(result, Database::new().check(&edited));
}

#[test]
fn damaged_environment_falls_back_and_restored_errors_match_full_checks() {
    let snapshot = project();
    let cache = Cache::new();
    assert!(Database::with_cache(&cache.0).check(&snapshot).is_success());
    let edited = snapshot.with_file(
        "/virtual/Left.ref",
        r"\import \root.Base[] \as B; \definition wrong: B.P := ?;",
    );
    let mut database = Database::with_cache(&cache.0);
    let failed = database.check(&edited);
    assert!(!failed.is_success());
    assert_eq!(database.stats().environment_hits, 1);
    assert_eq!(failed, Database::new().check(&edited));
    for entry in fs::read_dir(&cache.0).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|ext| ext == "env") {
            fs::write(path, b"damaged environment").unwrap();
        }
    }
    let mut database = Database::with_cache(&cache.0);
    assert_eq!(database.check(&edited), failed);
    assert_eq!(database.stats().environment_hits, 0);
}

#[test]
fn checking_disjoint_steps_does_not_publish_a_complete_prefix() {
    let mut snapshot = project();
    snapshot.insert(
        "/virtual/root.ref",
        r"\module Extra; \module Base; \module Left; \module Right;",
    );
    snapshot.insert(
        "/virtual/Extra.ref",
        r"\inductive Unit: \Set := | unit: Unit;",
    );
    snapshot.insert(
        "/virtual/Right.ref",
        r"\import \root.Extra[] \as E; \definition x: E.Unit := E.Unit::unit;",
    );
    let cache = Cache::new();
    assert!(Database::with_cache(&cache.0).check(&snapshot).is_success());
    for entry in fs::read_dir(&cache.0).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|ext| ext == "env") {
            fs::write(path, "damaged").unwrap();
        }
    }
    let edited = snapshot.with_file(
        "/virtual/Left.ref",
        r"\import \root.Base[] \as B; \definition q: \Prop := B.P;",
    );
    let mut database = Database::with_cache(&cache.0);
    assert_eq!(database.check(&edited), Database::new().check(&edited));
    assert_eq!(database.stats().checked_modules, 2);
    assert_eq!(database.stats().environment_writes, 0);
    let edited = edited.with_file(
        "/virtual/Right.ref",
        r"\import \root.Extra[] \as E; \definition y: E.Unit := E.Unit::unit;",
    );
    let result = Database::with_cache(&cache.0).check(&edited);
    assert!(result.is_success(), "{result:?}");
    assert_eq!(result, Database::new().check(&edited));
}

#[test]
fn user_body_edits_reuse_imports_scheduled_after_its_parameters() {
    let mut snapshot = project();
    snapshot.insert(
        "/virtual/root.ref",
        r"\module Left; \module Base; \module Right;",
    );
    let cache = Cache::new();
    assert!(Database::with_cache(&cache.0).check(&snapshot).is_success());
    let edited = snapshot.with_file(
        "/virtual/Left.ref",
        r"\import \root.Base[] \as B; \definition renamed: \Prop := B.P;",
    );
    let mut database = Database::with_cache(&cache.0);
    assert_eq!(database.check(&edited), Database::new().check(&edited));
    assert_eq!(database.stats().environment_hits, 1);
    assert_eq!(database.stats().checked_modules, 1);
    assert_eq!(database.stats().restored_modules, 1);
}

#[test]
fn diagnostic_mode_is_part_of_the_query_identity() {
    use sema::{CheckOptions, DiagnosticMode};
    let mut snapshot = SourceSnapshot::new("/virtual/root.ref");
    snapshot.insert(
        "/virtual/root.ref",
        r"\module M(A: \Set) { \definition pending: A := ?; }",
    );
    let mut database = Database::new();
    let compact = database.check_with_options(
        &snapshot,
        &CheckOptions {
            diagnostics: DiagnosticMode::Compact,
            ..Default::default()
        },
    );
    let detailed = database.check_with_options(
        &snapshot,
        &CheckOptions {
            diagnostics: DiagnosticMode::Detailed,
            ..Default::default()
        },
    );
    assert_eq!(
        compact.diagnostics[0].location,
        detailed.diagnostics[0].location
    );
    assert!(!compact.diagnostics[0].message.contains("constraints:"));
    assert!(detailed.diagnostics[0].message.contains("constraints:"));
    let cached = database.check_with_options(
        &snapshot,
        &CheckOptions {
            diagnostics: DiagnosticMode::Compact,
            ..Default::default()
        },
    );
    assert_eq!(compact, cached);
}

#[test]
fn recovery_reuses_verified_dependencies_without_retrying_failed_modules() {
    use sema::{CheckOptions, DiagnosticMode};
    let mut snapshot = SourceSnapshot::new("/virtual/root.ref");
    snapshot.insert(
        "/virtual/root.ref",
        "\\module Base; \\module First; \\module Second;",
    );
    snapshot.insert(
        "/virtual/Base.ref",
        r"\definition P: \Prop := \forall (X: \Prop) -> X -> X;",
    );
    for name in ["First", "Second"] {
        snapshot.insert(
            format!("/virtual/{name}.ref"),
            r"\import \root.Base[] \as B; \definition bad: B.P := \Set;",
        );
    }
    let mut database = Database::new();
    let detailed = database.check_with_options(
        &snapshot,
        &CheckOptions {
            force: true,
            diagnostics: DiagnosticMode::Detailed,
            ..Default::default()
        },
    );
    assert_eq!(detailed.diagnostics.len(), 2, "{detailed:?}");
    assert!(
        database.stats().recovery_environment_hits >= 1,
        "{:?}",
        database.stats()
    );
    assert!(
        database.stats().restored_modules >= 1,
        "{:?}",
        database.stats()
    );
    let compact = Database::new().check_with_options(
        &snapshot,
        &CheckOptions {
            force: true,
            diagnostics: DiagnosticMode::Compact,
            ..Default::default()
        },
    );
    assert_eq!(compact.diagnostics.len(), 1);
    assert_eq!(
        compact.diagnostics[0].location,
        detailed.diagnostics[0].location
    );
    assert_eq!(
        compact.diagnostics[0].message.lines().next(),
        detailed.diagnostics[0].message.lines().next()
    );
}

#[test]
fn module_timings_include_preparation_and_keep_generated_scopes_with_the_source() {
    use std::{cell::RefCell, time::Duration};
    thread_local! {
        static EVENTS: RefCell<Vec<sema::ModuleProgress>> = const { RefCell::new(Vec::new()) };
    }
    fn receive(event: &sema::ModuleProgress) {
        EVENTS.with_borrow_mut(|events| events.push(event.clone()));
    }
    let mut snapshot = SourceSnapshot::new("/virtual/root.ref");
    snapshot.insert(
        "/virtual/root.ref",
        r"\module Parent(C: \Set, x: C) {
        \structure Box[Carrier: \Set] { value: Carrier }
        \definition make[Carrier: \Set]: Carrier -> Box[Carrier] :=
            \fun (value: Carrier) => Box[Carrier] { value := value };
        \definition box: Box[C] := make[C] x;
        \module Child { \definition value: C := x; }
    }",
    );
    let session = sema::timing::Session::start(true);
    let result = Database::new().check_with_options(
        &snapshot,
        &sema::CheckOptions {
            force: true,
            progress: Some(receive),
            ..Default::default()
        },
    );
    assert!(result.is_success(), "{:?}", result.diagnostics);
    let measurements = session.finish().unwrap();
    EVENTS.with_borrow_mut(|events| {
        assert_eq!(events.len(), 2);
        assert_eq!(measurements.modules.len(), 2);
        for event in events.drain(..) {
            assert!(event.elapsed > Duration::ZERO);
            assert_eq!(event.elapsed, measurements.modules[&event.path]);
        }
    });
    assert!(measurements.modules.values().sum::<Duration>() <= measurements.total);
}

#[test]
fn named_module_options_recheck_dependencies_and_isolate_unrelated_errors() {
    let original = project();
    let mut database = Database::new();
    assert!(database.check(&original).is_success());
    let edited = original.with_file("/virtual/Right.ref", r"\definition Q: \Set := \Prop;");
    let checked = database.module_with_options(
        &edited,
        &["Left".into()],
        &sema::CheckOptions {
            force: true,
            diagnostics: sema::DiagnosticMode::Compact,
            ..Default::default()
        },
    );
    assert!(checked.is_success(), "{checked:?}");
    assert!(checked.modules.iter().any(|module| module.path == ["Left"]));
    assert!(checked.modules.iter().any(|module| module.path == ["Base"]));
    assert!(
        !checked
            .modules
            .iter()
            .any(|module| module.path == ["Right"])
    );
    assert!(database.stats().checked_modules >= 2);
    assert!(!database.check(&edited).is_success());
}

#[test]
fn named_module_options_include_children() {
    let snapshot = project().with_file(
        "/virtual/Right.ref",
        r"\module Child { \definition invalid: \Set := \Prop; }",
    );
    let result = Database::new().module_with_options(
        &snapshot,
        &["Right".into()],
        &sema::CheckOptions::default(),
    );
    assert!(!result.is_success());
    assert!(
        result
            .modules
            .iter()
            .any(|module| module.path == ["Right", "Child"])
    );
}

#[test]
fn namespace_imports_select_used_descendants_and_preserve_cache_dependencies() {
    let snapshot = project().with_file(
        "/virtual/Base.ref",
        r"\definition P: \Prop := \forall (A: \Prop) -> A -> A;
\module Used { \definition Q: \Prop := P; }
\module Unused { \definition invalid: \Set := \Prop; }",
    );
    let mut database = Database::new();
    let left = database.module(&snapshot, &["Left".into()]);
    assert!(left.is_success(), "{left:?}");
    assert!(!left.modules.iter().any(|m| m.path == ["Base", "Unused"]));
    let uses_child = snapshot.with_file(
        "/virtual/Left.ref",
        r"\import \root.Base[] \as B;
\import B.Used[] \as Child;
\definition p: \Prop := Child.Q;",
    );
    let left = database.module(&uses_child, &["Left".into()]);
    assert!(left.is_success(), "{left:?}");
    assert!(left.modules.iter().any(|m| m.path == ["Base", "Used"]));
    let broken_child = uses_child.with_file(
        "/virtual/Base.ref",
        r"\definition P: \Prop := \forall (A: \Prop) -> A -> A;
\module Used { \definition Q: \Set := P; }
\module Unused { \definition invalid: \Set := \Prop; }",
    );
    assert!(
        !database
            .module(&broken_child, &["Left".into()])
            .is_success()
    );
    assert!(!database.check(&snapshot).is_success());
}
