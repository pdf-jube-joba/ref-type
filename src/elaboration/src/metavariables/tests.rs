use crate::raw::ids::SymbolId;
use crate::{
    elaborator::GlobalEnvironment,
    metavariables::{ElaborationError, MetaFlavor, MetaState},
};
use syntax::parse;

fn error(source: &str) -> ElaborationError {
    let modules = parse::str_parse_modules(source).unwrap();
    GlobalEnvironment::default()
        .add_new_module_to_root(&modules[0])
        .unwrap_err()
}

#[test]
fn solved_inspection_hole_keeps_its_expected_type_and_solution() {
    let error = error(
        r"\module M(A: \Set, a: A) {
        \definition id: \forall (X: \Set) -> X -> X := \fun (X: \Set) => \fun (x: X) => x;
        \definition pending: A := id ? a;
    }",
    );
    let goals = error.goals();
    assert_eq!(goals.len(), 1, "{error}");
    assert_eq!(goals[0].flavor, MetaFlavor::Goal);
    assert_eq!(goals[0].state, MetaState::Solved);
    assert!(
        goals[0].principal.as_ref().unwrap().contains("\\Set"),
        "{error}"
    );
    assert!(goals[0].solution.as_ref().unwrap().contains('A'), "{error}");
}

#[test]
fn inspection_and_inference_failures_are_reported_together() {
    let error = error(
        r"\module M(A: \Set, a: A) {
        \definition choose: A -> A -> A := \fun (x: A) => \fun (y: A) => x;
        \definition pending: A := choose ? _7;
    }",
    );
    let goals = error.goals();
    assert_eq!(goals.len(), 2, "{error}");
    assert!(goals.iter().any(|g| g.flavor == MetaFlavor::Goal));
    assert!(goals.iter().any(|g| g.display_name() == "_7"));
    assert!(
        goals
            .iter()
            .all(|g| g.state == MetaState::InsufficientInformation),
        "{error}"
    );
}

#[test]
fn unresolved_type_dependency_is_reported_as_waiting() {
    let error = error(r"\module M { \definition pending: _1 := ?; }");
    assert!(
        error
            .goals()
            .iter()
            .any(|g| g.flavor == MetaFlavor::Goal && g.state == MetaState::Waiting),
        "{error}"
    );
}

#[test]
fn program_value_and_computation_holes_report_context_and_expected_type() {
    for body in ["?", "\\return ?"] {
        let ty = if body == "?" { "A" } else { "\\F(A)" };
        let source = format!(r"\module M(A: \VType) {{ \definition pending: {ty} := {body}; }}");
        let error = error(&source);
        let goals = error.goals();
        assert_eq!(goals.len(), 1, "{error}");
        assert!(
            goals[0].principal.as_ref().unwrap().contains('A'),
            "{error}"
        );
        assert!(!goals[0].constraints.is_empty(), "{error}");
    }
    let error =
        error(r"\module M(A: \VType) { \definition pending: A ~> \F(A) := \cfun (x: A) => ?; }");
    assert!(
        error
            .goals()
            .iter()
            .any(|g| g.context.contains("x:")
                && g.principal.as_ref().is_some_and(|p| p.contains("\\F"))),
        "{error}"
    );
}

#[test]
fn program_inspection_type_is_reported_after_solving() {
    let error = error(
        r"\module M {
        \inductive Unit: \VType := | unit: Unit;
        \definition pending: ? := Unit::unit;
    }",
    );
    assert!(
        error.goals().iter().any(|g| g.flavor == MetaFlavor::Goal
            && g.state == MetaState::Solved
            && g.solution.as_ref().is_some_and(|s| s.contains("Unit"))),
        "{error}"
    );
}

#[test]
fn named_program_type_is_shared_between_annotation_and_body() {
    let source = r"\module M {
        \inductive Unit: \VType := | unit: Unit;
        \definition f: _2 ~> \F(Unit) := \cfun (x: Unit) => \return Unit::unit;
        \definition g: Unit ~> \F(_2) := \cfun (x: _2) => \return x;
    }";
    let modules = parse::str_parse_modules(source).unwrap();
    GlobalEnvironment::default()
        .add_new_module_to_root(&modules[0])
        .unwrap();
}

#[test]
fn constraints_keep_named_occurrences_and_origins() {
    let source = r"\module M(A: \Set) { \definition pending: \Prop := _12 = _12; }";
    let error = error(source);
    let goal = &error.goals()[0];
    assert_eq!(goal.display_name(), "_12");
    assert_eq!(goal.occurrences.len(), 2);
    for span in &goal.occurrences {
        assert_eq!(&source[span.start..span.end], "_12");
    }
    assert!(
        goal.constraints
            .iter()
            .any(|c| c.original.contains("_12") && !c.origins.is_empty()),
        "{error}"
    );
}

#[test]
fn non_pattern_equations_are_distinguished_from_contradictions() {
    use super::*;
    let env = CrateEnv::default();
    let mut store = MetaStore::default();
    let variable = env.arena().exp_bound(0);
    let context = vec![ExpContextEntry {
        var: SymbolId::ANONYMOUS,
        ty: env.arena().sort(Sort::Set(0)),
    }];
    let meta = store
        .fresh(
            &env,
            SurfaceMeta::Named(3),
            SourceSpan::default(),
            &context,
            1,
        )
        .unwrap();
    let ExpNode::Meta { metavariable, .. } = env.arena().get(meta) else {
        unreachable!()
    };
    let non_pattern = env.arena().alloc(ExpNode::Meta {
        metavariable,
        spine: vec![env.arena().alloc(ExpNode::App {
            func: env.arena().alloc(ExpNode::Lam {
                var: SymbolId::ANONYMOUS,
                ty: context[0].ty,
                body: variable,
            }),
            arg: variable,
        })],
    });
    assert!(!store.unify(&env, non_pattern, variable).unwrap());
    let error = store.finish(&env).unwrap_err();
    assert_eq!(error.goals()[0].state, MetaState::Unsupported, "{error}");
    assert!(
        store
            .unify(
                &env,
                env.arena().sort(Sort::Prop),
                env.arena().sort(Sort::Set(0))
            )
            .is_err()
    );
    let error = store.constraint_error(&env, "incompatible sorts".into());
    assert_eq!(error.goals()[0].state, MetaState::Contradiction, "{error}");
}

#[test]
fn later_solution_discharges_a_previously_blocked_equation() {
    use super::*;
    let env = CrateEnv::default();
    let mut store = MetaStore::default();
    let set = env.arena().sort(Sort::Set(0));
    let context = vec![ExpContextEntry {
        var: SymbolId::ANONYMOUS,
        ty: set,
    }];
    let meta = store
        .fresh(
            &env,
            SurfaceMeta::Named(3),
            SourceSpan::default(),
            &context,
            1,
        )
        .unwrap();
    let ExpNode::Meta { metavariable, .. } = env.arena().get(meta) else {
        unreachable!()
    };
    let non_pattern = env.arena().alloc(ExpNode::Meta {
        metavariable,
        spine: vec![env.arena().alloc(ExpNode::App {
            func: env.arena().alloc(ExpNode::Lam {
                var: SymbolId::ANONYMOUS,
                ty: set,
                body: env.arena().exp_bound(0),
            }),
            arg: env.arena().exp_bound(0),
        })],
    });
    assert!(!store.unify(&env, non_pattern, set).unwrap());
    assert!(store.unify(&env, meta, set).unwrap());
    store.finish(&env).unwrap();
    assert!(
        store
            .constraints
            .iter()
            .all(|record| record.status == ConstraintStatus::Discharged)
    );
}

#[test]
fn solved_proof_hole_has_a_concrete_expected_type() {
    let error = error(r"\module M(A: \Set, a: A) { \definition pending: a = a := \refl(?); }");
    let goal = &error.goals()[0];
    assert_eq!(goal.state, MetaState::Solved);
    let principal = goal.principal.as_ref().unwrap();
    assert!(principal.contains('A'), "{error}");
    assert!(!principal.contains("<inferred"), "{error}");
}
