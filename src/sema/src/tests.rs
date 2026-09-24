use super::*;

fn host(text: &str) -> AnalysisHost {
    let mut host = AnalysisHost::new("/virtual/root.ref").unwrap();
    host.sources_mut()
        .set_disk("/virtual/root.ref", Some(text.into()));
    host
}

#[test]
fn incomplete_constructor_recovers_at_the_inductive_terminator() {
    let snapshot = host(
        r"\module M {
        \inductive Broken: \Set := | first: Broken | second: ;
        \definition Survives: \SetKind := \Set;
    }",
    )
    .snapshot();
    let survivor = snapshot
        .outline()
        .iter()
        .find(|item| item.key.name == "Survives")
        .unwrap();
    assert_eq!(snapshot.parse_diagnostics().diagnostics.len(), 1);
    assert_eq!(
        snapshot.check_item(survivor.id).unwrap().status,
        ItemCheckStatus::Checked
    );
}

#[test]
fn macro_captures_preserve_editable_holes_and_templates_mark_generated_holes() {
    let mut captured = host(
        r"\module M {
        \macro identity($x) := $x;
        \macro nested($x) := identity!{$x};
        \definition A: \SetKind := nested!{?};
    }",
    );
    let snapshot = captured.snapshot();
    let goal = &snapshot.check().goals[0];
    assert!(goal.editable);
    let proposal = captured.give(goal.id, r"\Set").unwrap();
    captured.apply_edits(&proposal).unwrap();
    assert_eq!(captured.snapshot().check().status, CheckStatus::Checked);

    let generated = host(
        r"\module M {
        \macro hole() := ?;
        \macro nested() := hole!{};
        \definition A: \SetKind := nested!{};
    }",
    );
    let snapshot = generated.snapshot();
    assert_eq!(snapshot.check().status, CheckStatus::Incomplete);
    let goal = &snapshot.check().goals[0];
    assert!(!goal.editable);
    assert!(goal.occurrences.is_empty());
    assert!(matches!(
        generated.give(goal.id, r"\Set"),
        Err(EditError::GeneratedGoal)
    ));
    let file = snapshot.sources().file_id("/virtual/root.ref").unwrap();
    assert_eq!(snapshot.goals(file).len(), 1);
}

#[test]
fn incomplete_declarations_keep_resolved_references_after_session_disposal() {
    let text = r"\module M { \definition A: \SetKind := \Set; \definition value: A := ?; }";
    let snapshot = host(text).snapshot();
    let file = snapshot.sources().file_id("/virtual/root.ref").unwrap();
    assert_eq!(snapshot.check().status, CheckStatus::Incomplete);
    let definition = snapshot
        .definition_at(file, text.find("value: A").unwrap() + 7)
        .unwrap();
    assert_eq!(definition.range.start, text.find("A:").unwrap());
    let target = snapshot
        .outline()
        .iter()
        .find(|item| item.key.name == "A")
        .unwrap();
    assert_eq!(snapshot.references(target.id).locations.len(), 1);
}

#[test]
fn snapshot_retains_text_and_file_identity_across_edits() {
    let mut host = host(r"\module M { \definition A: \SetKind := \Set; }");
    let id = host.sources().file_id("/virtual/root.ref").unwrap();
    let before = host.snapshot();
    host.sources_mut().set_overlay(
        "/virtual/root.ref",
        r"\module M { \definition A: \Set := ?; }".into(),
    );
    let after = host.snapshot();
    assert_ne!(before.revision(), after.revision());
    assert_eq!(host.sources().file_id("/virtual/root.ref"), Some(id));
    assert_eq!(before.check().status, CheckStatus::Checked);
    assert_eq!(after.check().status, CheckStatus::Incomplete);
    host.sources_mut().close_overlay("/virtual/root.ref");
    assert_eq!(host.snapshot().check().status, CheckStatus::Checked);
    assert_eq!(after.check().status, CheckStatus::Incomplete);
}

#[test]
fn file_existence_is_an_input_including_unsaved_external_files() {
    let mut host = host(r"\module M;");
    let absent = host.snapshot();
    let id = host
        .sources_mut()
        .set_overlay("/virtual/M.ref", r"\definition A: \SetKind := \Set;".into());
    let present = host.snapshot();
    assert_eq!(present.check().status, CheckStatus::Checked);
    assert_eq!(absent.check().status, CheckStatus::Failed);
    host.sources_mut().close_overlay("/virtual/M.ref");
    assert_eq!(host.snapshot().check().status, CheckStatus::Failed);
    assert!(present.sources().file(id).is_some());
}

#[test]
fn recovery_keeps_later_declarations_nested_modules_and_byte_ranges() {
    let source = "/* 日本語 */ \\module M { \\definition broken: \\Set := ; \\definition A: \\SetKind := \\Set; \\module N { \\definition B: \\SetKind := \\Set; } }";
    let host = host(source);
    let snapshot = host.snapshot();
    let outline = snapshot.outline();
    assert_eq!(
        outline
            .iter()
            .map(|item| item.key.name.as_str())
            .collect::<Vec<_>>(),
        ["M", "broken", "A", "N", "B"]
    );
    for item in outline {
        let name = item.name_location.unwrap().range;
        assert_eq!(&source[name.start..name.end], item.key.name);
    }
    let diagnostics = snapshot.parse_diagnostics();
    assert_eq!(diagnostics.diagnostics.len(), 1);
    let range = diagnostics.diagnostics[0].primary.unwrap().range;
    assert_eq!(&source[range.start..range.end], ";");
    assert_eq!(snapshot.check().status, CheckStatus::Failed);
}

#[test]
fn recovery_does_not_consume_next_declaration_when_semicolon_is_missing() {
    let snapshot = host(
        r"\module M { \definition broken: \SetKind := \Set \definition A: \SetKind := \Set; }",
    )
    .snapshot();
    assert!(snapshot.outline().iter().any(|item| item.key.name == "A"));
    assert_eq!(snapshot.parse_diagnostics().diagnostics.len(), 1);
}

#[test]
fn lexer_recovery_preserves_positions_and_reports_unterminated_comment() {
    let snapshot =
        host("\\module M { \\definition A: \\SetKind := \\Set; } \"\n /* unterminated").snapshot();
    assert_eq!(snapshot.parse_diagnostics().diagnostics.len(), 2);
    assert!(snapshot.outline().iter().any(|item| item.key.name == "A"));
}

#[test]
fn item_identity_survives_insertion_but_content_version_changes() {
    let mut host = host(r"\module M { \definition A: \SetKind := \Set; }");
    let before = host.snapshot();
    let a = before
        .outline()
        .iter()
        .find(|item| item.key.name == "A")
        .unwrap()
        .clone();
    host.sources_mut().set_overlay(
        "/virtual/root.ref",
        r"\module M { \definition B: \SetKind := \Set; \definition A: \SetKind := B; }".into(),
    );
    let after = host.snapshot();
    let changed = after
        .outline()
        .iter()
        .find(|item| item.key.name == "A")
        .unwrap();
    assert_eq!(a.id, changed.id);
    assert_ne!(a.version, changed.version);
    assert_ne!(a.location, changed.location);
    assert_eq!(after.check().status, CheckStatus::Checked);
}

#[test]
fn disk_changes_are_hidden_by_overlay_and_rename_preserves_identity() {
    let mut sources = SourceDatabase::new("/virtual").unwrap();
    let id = sources.set_disk("M.ref", Some("disk".into()));
    sources.set_overlay("M.ref", "buffer".into());
    let before = sources.clone();
    sources.set_disk("M.ref", Some("new disk".into()));
    assert_eq!(sources.file(id).unwrap().source.text, "buffer");
    sources.rename(id, "nested/M.ref").unwrap();
    assert_eq!(sources.file_id("nested/../nested/M.ref"), Some(id));
    assert!(sources.file_id("M.ref").is_none());
    sources.close_overlay("nested/M.ref");
    assert_eq!(sources.file(id).unwrap().source.text, "new disk");
    assert_eq!(before.file(id).unwrap().source.text, "buffer");
}

#[test]
fn unchanged_input_keeps_revision_and_queries_are_order_independent() {
    let text = r"\module M { \definition A: \SetKind := \Set; \check \Set: \SetKind; }";
    let mut host = host(text);
    let before = host.snapshot();
    host.sources_mut()
        .set_disk("/virtual/root.ref", Some(text.into()));
    let after = host.snapshot();
    assert_eq!(before.revision(), after.revision());
    let _ = before.outline();
    let first = before.check();
    let second = after.check();
    assert_eq!(first.status, second.status);
    assert_eq!(first.outputs, second.outputs);
    assert_eq!(before.outline(), after.outline());
    assert!(std::ptr::eq(first, before.check()));
}

#[test]
fn module_header_and_body_diagnostics_retain_their_files() {
    let mut host = host(r"\module M;");
    let file = host
        .sources_mut()
        .set_overlay("/virtual/M.ref", r"\definition A: \Set := missing;".into());
    let snapshot = host.snapshot();
    assert_eq!(snapshot.check().status, CheckStatus::Failed);
    assert_eq!(snapshot.diagnostics(file).diagnostics.len(), 1);
    let diagnostic = &snapshot.check().diagnostics[0];
    assert_eq!(diagnostic.primary.unwrap().file, file);
    assert!(
        snapshot
            .render_diagnostic(diagnostic)
            .contains("/virtual/M.ref:1:")
    );
}

#[test]
fn goal_snapshot_survives_checker_and_named_occurrences_are_edited_together() {
    let mut host = host(
        r"\module M { \definition identity: \forall (A: \Set) -> A -> A := \fun (A: \Set) => \fun (x: A) => ?7; }",
    );
    let before = host.snapshot();
    assert_eq!(
        before.check().status,
        CheckStatus::Incomplete,
        "{:?}",
        before.check().diagnostics
    );
    let goal = before.check().goals[0].clone();
    assert_eq!(goal.context.len(), 2);
    assert!(goal.target.is_some());
    assert!(matches!(
        host.give(goal.id, r"\Set"),
        Err(EditError::Rejected(_))
    ));
    let proposal = host.give(goal.id, "x").unwrap();
    assert!(proposal.goals.is_empty());
    assert!(proposal.diagnostics.is_empty());
    host.apply_edits(&proposal).unwrap();
    assert_eq!(host.snapshot().check().status, CheckStatus::Checked);
    assert_eq!(host.give(goal.id, "x").unwrap_err(), EditError::Stale);
    assert_eq!(before.check().goals[0].context, goal.context);
}

#[test]
fn refine_can_leave_goals_and_cancelled_queries_are_retryable() {
    let host = host(r"\module M { \definition identity: \forall (A: \Set) -> A -> A := ?; }");
    let snapshot = host.snapshot();
    let token = kernel::control::CancellationToken::default();
    token.cancel();
    assert_eq!(
        snapshot.check_with_control(token, None).unwrap_err(),
        kernel::control::Interrupted::Cancelled
    );
    assert_eq!(
        snapshot
            .check_with_control(Default::default(), Some(3))
            .unwrap_err(),
        kernel::control::Interrupted::ResourceLimit
    );
    let result = snapshot
        .check_with_control(Default::default(), None)
        .unwrap();
    assert_eq!(
        result.status,
        CheckStatus::Incomplete,
        "{:?}",
        result.diagnostics
    );
    let proposal = host
        .refine(result.goals[0].id, r"\fun (A: \Set) => \fun (x: A) => ?")
        .unwrap();
    assert_eq!(proposal.goals.len(), 1);
    assert_eq!(proposal.goals[0].context.len(), 2);
}

#[test]
fn a_named_goal_edit_replaces_every_occurrence() {
    let mut host = host(r"\module M(A: \Set, a: A) { \definition pending: \Prop := ?7 = ?7; }");
    let snapshot = host.snapshot();
    let goals = &snapshot.check().goals;
    assert_eq!(goals.len(), 1);
    assert_eq!(goals[0].occurrences.len(), 2);
    let proposal = host.give(goals[0].id, "a").unwrap();
    assert_eq!(proposal.edits.len(), 2);
    host.apply_edits(&proposal).unwrap();
    assert_eq!(host.snapshot().check().status, CheckStatus::Checked);
}

#[test]
fn raw_unit_storage_keeps_only_published_subtrees() {
    let modules = crate::parse::str_parse_modules(
        r"\module M {
        \definition identity: \forall (A: \Set) -> A -> A := \fun (A: \Set) => \fun (x: A) => x;
        \definition applied: \forall (A: \Set) -> A -> A := \fun (A: \Set) => identity A;
        \check applied: \forall (A: \Set) -> A -> A;
    }",
    )
    .unwrap();
    let mut global = GlobalEnvironment::default();
    global.add_modules_to_root(&modules).unwrap();
    let retained = global.arena().node_counts()[0].1;
    let allocated = global.arena().allocated_node_counts()[0].1;
    assert!(
        retained < allocated,
        "retained={retained}, allocated={allocated}"
    );
    assert!(
        global
            .crate_env()
            .cache_counts()
            .iter()
            .all(|(_, count)| *count == 0)
    );
}

#[test]
fn failed_declaration_shadows_outer_name_and_independent_work_continues() {
    let snapshot = host(
        r"\module Outer(A: \Set, a: A) {
        \definition pending: A := a;
        \module Inner {
            \definition pending: A := ?;
            \definition dependent: A := pending;
            \definition independent: A := a;
        }
    }",
    )
    .snapshot();
    let find = |name: &str| {
        snapshot
            .outline()
            .iter()
            .find(|item| item.key.module.len() == 2 && item.key.name == name)
            .unwrap()
            .id
    };
    let pending = find("pending");
    assert_eq!(
        snapshot.check_item(pending).unwrap().status,
        ItemCheckStatus::Incomplete
    );
    assert_eq!(
        snapshot.check_item(find("dependent")).unwrap().status,
        ItemCheckStatus::Blocked {
            dependencies: vec![pending]
        }
    );
    assert_eq!(
        snapshot.check_item(find("independent")).unwrap().status,
        ItemCheckStatus::Checked
    );
}

#[test]
fn syntax_errors_and_failed_imports_leave_independent_declarations_checked() {
    let snapshot = host(
        r"\module Missing; \module M {
        \definition broken: \Set := ;
        \import \root.Missing[] \as X;
        \definition A: \SetKind := \Set;
    }",
    )
    .snapshot();
    let item = |name: &str| {
        snapshot
            .outline()
            .iter()
            .find(|item| item.key.name == name)
            .unwrap()
            .id
    };
    assert_eq!(
        snapshot.check_item(item("A")).unwrap().status,
        ItemCheckStatus::Checked
    );
    assert_eq!(
        snapshot.check_item(item("X")).unwrap().status,
        ItemCheckStatus::Blocked {
            dependencies: vec![item("Missing")]
        }
    );
    assert_eq!(snapshot.check().status, CheckStatus::Failed);
}

#[test]
fn incomplete_items_in_module_instances_preserve_dependency_identity() {
    let snapshot = host(
        r"\module Source(A: \Set) { \definition value: A := ?; }
        \module Use(A: \Set, a: A) {
            \import \root.Source[A := A] \as X;
            \definition pending: A := X.value;
            \definition independent: A := a;
        }",
    )
    .snapshot();
    let item = |name: &str| {
        snapshot
            .outline()
            .iter()
            .find(|item| item.key.name == name)
            .unwrap()
            .id
    };
    assert_eq!(
        snapshot.check_item(item("pending")).unwrap().status,
        ItemCheckStatus::Blocked {
            dependencies: vec![item("value")]
        }
    );
    assert_eq!(
        snapshot.check_item(item("independent")).unwrap().status,
        ItemCheckStatus::Checked
    );
}

#[test]
fn definition_queries_record_selected_names_and_type_directed_fields() {
    let source = r"\module M(A: \Set, a: A) {
        \definition value: A := a;
        \record Pair: \Set := { first: A, second: A };
        \definition pair: Pair := Pair::# value a;
        \definition projected: A := #first{pair};
    }";
    let host = host(source);
    let snapshot = host.snapshot();
    assert_eq!(
        snapshot.check().status,
        CheckStatus::Checked,
        "{:?}",
        snapshot.check().diagnostics
    );
    let file = host.sources().file_id("/virtual/root.ref").unwrap();
    let position = source.find("value a").unwrap();
    let definition = snapshot.definition_at(file, position).unwrap();
    assert_eq!(
        &source[definition.range.start..definition.range.end],
        "value"
    );
    assert!(snapshot.type_at(file, position).is_some());
    let position = source.find("#first").unwrap() + 1;
    let definition = snapshot.definition_at(file, position).unwrap();
    assert_eq!(definition.range.start, source.find("first: A").unwrap());
}

#[test]
fn local_definition_query_tracks_shadowing() {
    let source = r"\module M { \definition identity: \forall (A: \Set) -> A -> A := \fun (A: \Set) => \fun (x: A) => x; }";
    let host = host(source);
    let snapshot = host.snapshot();
    let file = host.sources().file_id("/virtual/root.ref").unwrap();
    let location = snapshot
        .definition_at(file, source.rfind("x;").unwrap())
        .unwrap();
    assert_eq!(location.range.start, source.find("x: A").unwrap());
}
