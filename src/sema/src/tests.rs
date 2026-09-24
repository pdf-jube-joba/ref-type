use super::*;

fn host(text: &str) -> AnalysisHost {
    let mut host = AnalysisHost::new("/virtual/root.ref").unwrap();
    host.sources_mut()
        .set_disk("/virtual/root.ref", Some(text.into()));
    host
}

#[test]
fn indistinguishable_shared_terms_fall_back_to_the_common_ast_expression() {
    use elab::{environment::CrateEnv, exp::ExpNode};
    let source = Arc::new(syntax::SourceFile {
        id: syntax::SourceId("/virtual/shared.ref".into()),
        text: "f x x".into(),
    });
    let ast = parse::str_parse_exp(&source.text).unwrap();
    let syntax::SExpKind::App { func, arg: right } = &ast.kind else {
        panic!("application")
    };
    let syntax::SExpKind::App { arg: left, .. } = &func.kind else {
        panic!("application")
    };
    let mut raw = CrateEnv::new();
    raw.sources.insert(&ast, &source);
    let shared = raw.arena().alloc(ExpNode::Bound(0));
    let term = raw.arena().alloc(ExpNode::Equal {
        left: shared,
        right: shared,
    });
    let root = raw
        .provenance
        .enter(Some(ast.source.unwrap().id), &raw.sources);
    for child in [left, right] {
        let occurrence = raw
            .provenance
            .enter(Some(child.source.unwrap().id), &raw.sources);
        raw.provenance
            .leave(occurrence, Some(shared.into()), raw.arena(), &raw.sources);
    }
    raw.provenance
        .leave(root, Some(term.into()), raw.arena(), &raw.sources);
    raw.provenance.record_error(&[shared.into(), term.into()]);
    assert_eq!(
        raw.provenance.error_origin(&raw.sources, None),
        Some(ast.source.unwrap().id)
    );
}

#[test]
fn generated_raw_children_have_individual_origins() {
    use elab::{
        environment::CrateEnv,
        exp::{ExpNode, Prove},
    };
    let source = Arc::new(syntax::SourceFile {
        id: syntax::SourceId("/virtual/generated.ref".into()),
        text: "x".into(),
    });
    let ast = parse::str_parse_exp(&source.text).unwrap();
    let mut raw = CrateEnv::new();
    raw.sources.insert(&ast, &source);
    let generated = raw.arena().alloc(ExpNode::Bound(0));
    let term = raw
        .arena()
        .alloc(ExpNode::Prove(Prove::IdRefl { element: generated }));
    let root = raw
        .provenance
        .enter(Some(ast.source.unwrap().id), &raw.sources);
    raw.provenance
        .leave(root, Some(term.into()), raw.arena(), &raw.sources);
    raw.provenance
        .record_error(&[generated.into(), term.into()]);
    let origin = raw.provenance.error_origin(&raw.sources, None).unwrap();
    assert_ne!(origin, ast.source.unwrap().id);
    assert_eq!(
        raw.sources.origin(origin),
        Some(syntax::DerivedOrigin::Generated {
            source: Some(ast.source.unwrap().id),
            reason: syntax::GenerationReason::Elaboration
        })
    );
    assert_eq!(
        raw.sources.location(origin).unwrap().span,
        ast.source.unwrap().span
    );
    assert!(raw.sources.written_location(origin).is_none());
    assert!(!raw.sources.is_editable(origin));
}

#[test]
fn kernel_failure_trace_resolves_lowered_occurrences_and_clears_after_success() {
    use elab::{environment::CrateEnv, exp::ExpNode};
    use kernel::{
        check::Checker, construction, environment::Environment, sort::BaseSort, syntax::Stage,
    };
    let source = Arc::new(syntax::SourceFile {
        id: syntax::SourceId("/virtual/term.ref".into()),
        text: "x".into(),
    });
    let ast = parse::str_parse_exp(&source.text).unwrap();
    let mut raw = CrateEnv::new();
    raw.sources.insert(&ast, &source);
    let term = raw.arena().alloc(ExpNode::Bound(0));
    let occurrence = raw
        .provenance
        .enter(Some(ast.source.unwrap().id), &raw.sources);
    raw.provenance
        .leave(occurrence, Some(term.into()), raw.arena(), &raw.sources);
    let kernel = Environment::new();
    let lowered = construction::bound(kernel.arena(), BaseSort::Set(0), Stage::Term, 0).unwrap();
    raw.provenance.lowered(term, lowered, &raw.sources);
    let mut checker = Checker::new(&kernel, vec![]);
    assert!(checker.infer(lowered).is_err());
    assert_eq!(&*kernel.check_error.borrow(), &[lowered]);
    raw.provenance.record_error(
        &kernel
            .check_error
            .borrow()
            .iter()
            .copied()
            .map(Into::into)
            .collect::<Vec<_>>(),
    );
    let origin = raw.provenance.error_origin(&raw.sources, None).unwrap();
    assert!(matches!(
        raw.sources.origin(origin),
        Some(syntax::DerivedOrigin::Generated {
            reason: syntax::GenerationReason::KernelLowering,
            ..
        })
    ));
    assert_eq!(
        raw.sources.location(origin).unwrap().span,
        ast.source.unwrap().span
    );
    let kind = construction::base_kind(kernel.arena(), BaseSort::Set(0)).unwrap();
    assert!(checker.infer(kind).is_ok());
    assert!(kernel.check_error.borrow().is_empty());
}

#[test]
fn generated_goal_types_retain_the_hole_as_their_source() {
    let source = r"\module M { \infer ?; }";
    let snapshot = host(source).snapshot();
    let goals = &snapshot.check().goals;
    assert!(
        goals
            .iter()
            .any(|goal| goal.provenance.iter().any(|entry| matches!(
                entry.origin,
                Some(syntax::DerivedOrigin::Generated {
                    reason: syntax::GenerationReason::ImplicitType,
                    source: Some(_),
                    ..
                })
            ))),
        "{goals:?}"
    );
    for goal in goals {
        for origin in &goal.provenance {
            if let Some(location) = origin.location {
                assert_eq!(&source[location.range.start..location.range.end], "?");
            }
        }
    }
}

#[test]
fn checking_errors_distinguish_shared_argument_occurrences() {
    let source = r"\module M {
        \inductive Unit: \Set := | unit: Unit;
        \inductive Other: \Set := | other: Other;
        \definition pick(x: Unit, y: Other): Unit := x;
        \definition bad: Unit := pick Unit::unit Unit::unit;
        \definition good: Unit := Unit::unit;
    }";
    let snapshot = host(source).snapshot();
    let diagnostics = &snapshot.check().diagnostics;
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    let location = diagnostics[0].primary.unwrap();
    let expected = source.find("Unit::unit Unit::unit").unwrap() + "Unit::unit ".len();
    assert_eq!(location.range.start, expected, "{diagnostics:?}");
    assert_eq!(
        &source[location.range.start..location.range.end],
        "Unit::unit"
    );
}

#[test]
fn program_checking_errors_distinguish_shared_argument_occurrences() {
    let source = r"\module M {
        \inductive Unit: \VType := | unit: Unit;
        \inductive Other: \VType := | other: Other;
        \definition pick(x: Unit, y: Other): \F(Unit) := \return x;
        \definition bad: \F(Unit) := pick Unit::unit Unit::unit;
    }";
    let snapshot = host(source).snapshot();
    let diagnostics = &snapshot.check().diagnostics;
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    let expected = source.find("Unit::unit Unit::unit").unwrap() + "Unit::unit ".len();
    assert_eq!(
        diagnostics[0].primary.unwrap().range.start,
        expected,
        "{diagnostics:?}"
    );
}

#[test]
fn nested_macro_diagnostics_retain_call_definition_and_capture_edges() {
    let source = r"\module M {
        \macro identity($x) := $x;
        \macro nested($x) := identity!{$x};
        \definition bad: \Set := nested!{missing};
    }";
    let snapshot = host(source).snapshot();
    let diagnostic = &snapshot.check().diagnostics[0];
    let trace = &diagnostic.provenance;
    let expansions = trace
        .iter()
        .filter(|entry| matches!(entry.origin, Some(syntax::DerivedOrigin::Expansion { .. })))
        .collect::<Vec<_>>();
    assert_eq!(expansions.len(), 2, "{trace:?}");
    assert_ne!(expansions[0].id, expansions[1].id);
    assert_eq!(diagnostic.secondary.len(), 2);
    assert!(trace.iter().any(|entry| matches!(
        entry.origin,
        Some(syntax::DerivedOrigin::Capture {
            captured: Some(_),
            ..
        })
    )));
    for entry in expansions {
        let syntax::DerivedOrigin::Expansion {
            call: Some(call),
            definition: Some(definition),
        } = entry.origin.unwrap()
        else {
            panic!("expansion endpoints")
        };
        assert!(trace.iter().any(|entry| entry.id == call));
        assert!(trace.iter().any(|entry| entry.id == definition));
    }
}

#[test]
fn template_references_keep_each_expansion_and_the_definition_file() {
    let source = r"\module Library; \module Main {
        \import \root.Library[] \as L;
        \use L.make;
        \definition first: \Set := make!{};
        \definition second: \Set := make!{};
    }";
    let library = r"\inductive Unit: \Set := | unit: Unit; \macro make() := Unit;";
    let mut host = host(source);
    let file = host
        .sources_mut()
        .set_disk("/virtual/Library.ref", Some(library.into()));
    let snapshot = host.snapshot();
    assert_eq!(
        snapshot.check().status,
        CheckStatus::Checked,
        "{:?}",
        snapshot.check().diagnostics
    );
    let start = library.rfind("Unit").unwrap();
    let occurrence = snapshot
        .check()
        .occurrences
        .iter()
        .find(|entry| entry.location.file == file && entry.location.range.start == start)
        .unwrap();
    let expansions = occurrence
        .provenance
        .iter()
        .filter(|entry| matches!(entry.origin, Some(syntax::DerivedOrigin::Expansion { .. })))
        .collect::<Vec<_>>();
    assert_eq!(expansions.len(), 2, "{occurrence:?}");
    assert_ne!(expansions[0].id, expansions[1].id);
    assert_ne!(expansions[0].location, expansions[1].location);
    assert!(snapshot.definition_at(file, start).is_some());
}

#[test]
fn captured_parenthesized_holes_use_the_token_occurrence() {
    let source = r"\module M {
        \macro identity($x) := $x;
        \definition incomplete: \Set := identity!{{(?)}};
    }";
    let snapshot = host(source).snapshot();
    let goals = &snapshot.check().goals;
    assert_eq!(goals.len(), 1, "{:?}", snapshot.check().diagnostics);
    let goal = &goals[0];
    assert!(goal.editable);
    let location = goal.occurrences[0];
    assert_eq!(&source[location.range.start..location.range.end], "?");
    assert!(
        goal.provenance
            .iter()
            .any(|entry| matches!(entry.origin, Some(syntax::DerivedOrigin::Capture { .. })))
    );
}

#[test]
fn expression_diagnostics_locate_logical_and_program_subexpressions() {
    let source = r"/* 日本語 */ \module M {
        \inductive Bit: \VType := | zero: Bit;
        \definition logical: \Set := \refl(missingLogical);
        \definition program(x: Bit): \F(Bit) := \return missingProgram;
        \cinfer \return missingQuery;
        \definition good: \SetKind := \Set;
    }";
    let snapshot = host(source).snapshot();
    let check = snapshot.check();
    assert_eq!(check.status, CheckStatus::Failed);
    let fragments = check
        .diagnostics
        .iter()
        .map(|diagnostic| {
            let range = diagnostic.primary.unwrap().range;
            &source[range.start..range.end]
        })
        .collect::<Vec<_>>();
    assert_eq!(
        fragments,
        ["(missingLogical)", "missingProgram", "missingQuery"]
    );
    let good = snapshot
        .outline()
        .iter()
        .find(|item| item.key.name == "good")
        .unwrap();
    assert_eq!(
        snapshot.check_item(good.id).unwrap().status,
        ItemCheckStatus::Checked
    );
}

#[test]
fn macro_error_locations_preserve_captures_and_fall_back_to_calls() {
    let source = r"\module M {
        \macro identity($x) := $x;
        \macro nested($x) := identity!{$x};
        \macro broken() := #field{\Set};
        \definition captured: \Set := nested!{missingCapture};
        \definition generated: \Set := broken!{};
        \definition good: \SetKind := \Set;
    }";
    let snapshot = host(source).snapshot();
    let fragments = snapshot
        .check()
        .diagnostics
        .iter()
        .map(|diagnostic| {
            let range = diagnostic.primary.unwrap().range;
            &source[range.start..range.end]
        })
        .collect::<Vec<_>>();
    assert_eq!(fragments, ["missingCapture", "broken!{}"]);
}

#[test]
fn ast_locations_belong_to_their_input_snapshot() {
    let text = r"\module M { \definition value: \Set := missing; }";
    let mut host = host(text);
    let before = host.snapshot();
    let modules = before.modules().unwrap();
    let syntax::ModuleBody::Inline(items) = &modules[0].body else {
        panic!("module")
    };
    let syntax::ModuleItem::Definition { body, .. } = &items[0] else {
        panic!("definition")
    };
    let hir = hir::SExp::from(body.clone());
    let id = hir.origin.unwrap();
    let location = before.ast_location(id).unwrap();
    assert_eq!(&text[location.range.start..location.range.end], "missing");
    host.sources_mut()
        .set_overlay("/virtual/root.ref", format!("/* 編集 */ {text}"));
    let after = host.snapshot();
    assert!(after.ast_location(id).is_none());
    assert_eq!(before.ast_location(id), Some(location));
    assert_eq!(before.check().diagnostics[0].primary, Some(location));
    let new_location = after.check().diagnostics[0].primary.unwrap();
    assert_ne!(location.revision, new_location.revision);
    assert_eq!(
        new_location.range.start,
        location.range.start + "/* 編集 */ ".len()
    );
}

#[test]
fn parameter_classification_discards_locations_from_successful_fallbacks() {
    let source = r"\module M(A: \Set, x: A, y: missing) {}";
    let snapshot = host(source).snapshot();
    let diagnostics = &snapshot.check().diagnostics;
    assert_eq!(diagnostics.len(), 1);
    let location = diagnostics[0].primary.unwrap();
    assert_eq!(&source[location.range.start..location.range.end], "missing");
}

#[test]
fn expression_diagnostics_keep_external_header_and_body_files() {
    let root = r"\module Bad(A: missingHeader); \module Good;";
    let mut host = host(root);
    host.sources_mut().set_disk(
        "/virtual/Bad.ref",
        Some(r"\definition unused: \SetKind := \Set;".into()),
    );
    let body = r"\definition bad: \Set := missingBody;";
    let body_file = host
        .sources_mut()
        .set_disk("/virtual/Good.ref", Some(body.into()));
    let root_file = host.sources().file_id("/virtual/root.ref").unwrap();
    let snapshot = host.snapshot();
    let locations = snapshot
        .check()
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.primary.unwrap())
        .collect::<Vec<_>>();
    assert_eq!(locations.len(), 2);
    assert_eq!(locations[0].file, root_file);
    assert_eq!(
        &root[locations[0].range.start..locations[0].range.end],
        "missingHeader"
    );
    assert_eq!(locations[1].file, body_file);
    assert_eq!(
        &body[locations[1].range.start..locations[1].range.end],
        "missingBody"
    );
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

fn assert_local_references(source: &str, references: &[(&str, &str)]) {
    let snapshot = host(source).snapshot();
    assert_eq!(
        snapshot.check().status,
        CheckStatus::Checked,
        "{:?}",
        snapshot.check().diagnostics
    );
    let file = snapshot.sources().file_id("/virtual/root.ref").unwrap();
    for (usage, binder) in references {
        let position = source.find(usage).unwrap();
        let target = snapshot
            .definition_at(file, position)
            .unwrap_or_else(|| panic!("missing reference for {usage}"));
        assert_eq!(target.range.start, source.find(binder).unwrap(), "{usage}");
        let occurrences = snapshot
            .check()
            .occurrences
            .iter()
            .filter(|occurrence| occurrence.location.range.start == position)
            .collect::<Vec<_>>();
        assert_eq!(occurrences.len(), 1, "{usage}: {occurrences:?}");
        assert_eq!(occurrences[0].target, SemanticRef::Local(target));
        assert_eq!(
            &source[target.range.start..target.range.end],
            &source[position..position + target.range.end - target.range.start]
        );
    }
}

#[test]
fn program_local_references_follow_lambda_let_and_sequence_shadowing() {
    assert_local_references(
        r"\module M {
          \inductive Bit: \VType := | zero: Bit | one: Bit;
          \definition f: \U(Bit -> Bit) := \fun (z: Bit) => \return z;
          \definition apply(f: Bit -> Bit, x: Bit): \F(Bit) := (\force f) x;
          \definition block: Bit -> Bit := \fun (x: Bit) =>
            \program {
              \let x: _ := x /* lambda */ \then
              \bind x: Bit <- apply f x /* let */ \then
              \return x
            };
          \definition explicit: Bit ~> \F(Bit) :=
            \cfun (v: Bit) => \let w: Bit := v \in \return w;
        }",
        &[
            ("z;", "z: Bit"),
            ("f) x;", "f: Bit -> Bit, x"),
            ("x;", "x: Bit):"),
            ("x /* lambda */", "x: Bit) =>"),
            ("x /* let */", "x: _"),
            ("x\n", "x: Bit <-"),
            ("v \\in", "v: Bit"),
            ("w;", "w: Bit"),
        ],
    );
}

#[test]
fn program_case_references_restore_outer_scope_between_branches() {
    assert_local_references(
        r"\module M {
          \inductive Bit: \VType := | zero: Bit | one: Bit;
          \inductive Choice: \VType := | first: Bit -> Bit -> Choice | second: Choice;
          \definition choose(x: Bit, choice: Choice): \F(Bit) :=
            \bind result: Bit <- \match choice \in Choice \with {
              | first x y => \let saved: Bit := y \in \return x
              | second => \return x /* outer branch */
            } \in
            \let after: Bit := x /* after case */ \in \return result;
        }",
        &[
            (r"choice \in", "choice: Choice"),
            (r"y \in", "y =>"),
            ("x\n", "x y =>"),
            ("x /* outer branch */", "x: Bit"),
            ("x /* after case */", "x: Bit"),
            ("result;", "result: Bit"),
        ],
    );
}

#[test]
fn program_type_parameter_references_keep_declaration_origins() {
    assert_local_references(
        r"\module M {
          \inductive Holder[A: \VType]: \VType := | hold: A -> Holder[A];
          \record Pair[B: \VType]: \VType := { first: B, second: B };
          \definition Holder(T: \VType)::identity(x: T): \F(T) := \return x;
        }",
        &[
            ("A ->", "A: \\VType"),
            ("A];", "A: \\VType"),
            ("B,", "B: \\VType"),
            ("B }", "B: \\VType"),
            ("T):", "T: \\VType"),
            ("T) :=", "T: \\VType"),
            ("x;", "x: T"),
        ],
    );
}

#[test]
fn program_proof_references_keep_origins_in_reflected_contexts() {
    assert_local_references(
        r"\module M(A: \VType, step: A -> \RunStep[A, A],
          total: \forall (s: A^) -> \Acc[A^, A^](step^, s)) {
          \definition run(x: A): \F(A) := \run[A, A](step, x) \by { total x };
          \definition runCase(v: A): \F(A) :=
            \let y: A := v \in
            \runCase[A, A](step, y, (\force step) y) \by {
              accessibility: total y, equality: \refl(step^ y)
            };
        }",
        &[
            ("x) \\by", "x: A"),
            ("x };", "x: A"),
            ("v \\in", "v: A"),
            ("y, (\\force", "y: A"),
            ("y) \\by", "y: A"),
            ("y, equality", "y: A"),
            ("y)\n", "y: A"),
        ],
    );
}
