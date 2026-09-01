use crate::{
    elaborator::GlobalEnvironment,
    metavariables::ElaborationError,
    parse,
    syntax::{SExp, SurfaceMeta},
};

#[test]
fn parses_implicit_and_goal_metavariables_as_atoms() {
    assert!(matches!(
        parse::str_parse_exp("_").unwrap(),
        SExp::Meta {
            kind: SurfaceMeta::Implicit,
            ..
        }
    ));
    assert!(matches!(
        parse::str_parse_exp("?").unwrap(),
        SExp::Meta {
            kind: SurfaceMeta::Goal,
            ..
        }
    ));
    assert!(matches!(
        parse::str_parse_exp("?2").unwrap(),
        SExp::Meta {
            kind: SurfaceMeta::Named(2),
            ..
        }
    ));
    assert!(parse::str_parse_exp("?name").is_err());
}

#[test]
fn implicit_type_argument_is_solved_by_a_later_application() {
    let source = r#"
        \module Metas(A: \Set(0), x: A) {
            \definition id: (X: \Set(0)) -> X -> X :=
                (X: \Set(0)) => (value: X) => value;
            \definition inferred: A := id _ x;
            \definition named: A := id ?2 x;
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
}

#[test]
fn lambda_annotation_is_solved_bidirectionally() {
    let source = r#"
        \module LambdaMeta(A: \Set(0)) {
            \definition identity: A -> A := (x: _) => x;
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
}

#[test]
fn check_expected_type_meta_is_inferred_from_the_term() {
    let source = r#"
        \module CheckMeta(A: \Set(0), a: A) {
            \check a: _;
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
}

#[test]
fn unsolved_question_mark_returns_a_structured_goal() {
    let source = r#"
        \module Goal(A: \Set(0)) {
            \definition pending: A := ?;
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    let error = environment.add_new_module_to_root(&modules[0]).unwrap_err();
    let ElaborationError::UnsolvedGoals(goals) = error else {
        panic!("expected structured goals");
    };
    assert_eq!(goals.len(), 1);
    assert!(goals[0].principal.is_some());
    assert!(!goals[0].constraints.is_empty());
}

#[test]
fn unsolved_underscore_is_an_ambiguity_error() {
    let source = r#"
        \module Goal(A: \Set(0), only_candidate: A) {
            \definition pending: A := _;
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    assert!(matches!(
        environment.add_new_module_to_root(&modules[0]),
        Err(ElaborationError::AmbiguousImplicit(_))
    ));
}

#[test]
fn conflicting_named_meta_constraints_are_structured() {
    let source = r#"
        \module Conflict(A: \Set(0), B: \Set(0), a: A, b: B) {
            \definition choose:
                (X: \Set(0)) -> X -> X -> X :=
                (X: \Set(0)) => (left: X) => (right: X) => left;
            \definition impossible: A := choose ?2 a b;
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    let error = environment.add_new_module_to_root(&modules[0]).unwrap_err();
    let ElaborationError::ConstraintFailure { constraints, .. } = error else {
        panic!("expected a structured constraint failure");
    };
    assert!(!constraints.is_empty());
}

#[test]
fn contextual_goal_reports_the_local_binder_context() {
    let source = r#"
        \module Context(A: \Set(0)) {
            \definition pending: A -> A := (x: A) => ?;
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    let error = environment.add_new_module_to_root(&modules[0]).unwrap_err();
    let ElaborationError::UnsolvedGoals(goals) = error else {
        panic!("expected an unsolved contextual goal");
    };
    assert_eq!(goals.len(), 1);
    assert!(
        goals[0].context.len() >= 2,
        "module parameter and local binder"
    );
}

#[test]
fn implicit_solution_may_depend_on_its_local_binder_context() {
    let source = r#"
        \module Contextual {
            \definition apply:
                (A: \Set(0)) -> A -> A :=
                (A: \Set(0)) => (x: A) =>
                    ((X: \Set(0)) => (value: X) => value) _ x;
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
}

#[test]
fn program_annotation_meta_is_solved_from_the_declared_type() {
    let source = r#"
        \module ProgramMeta(A: \VType, x: A) {
            \definition finished: \RunStep(A, A) := \finish(_, A, x);
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
}

#[test]
fn program_terms_determine_top_level_type_metavariables() {
    let source = r#"
        \module ProgramTypeMeta(A: \VType, x: A) {
            \definition inferred_value_type: _ := x;
            \definition inferred_computation_type: _ := \return(x);
            \check x: _;
            \check \return(x): _;
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
}

#[test]
fn dependent_module_argument_solves_an_earlier_implicit() {
    let source = r#"
        \module Parameterized(X: \Set(0), x: X) {}
        \module Use(A: \Set(0), a: A) {
            \import \root.Parameterized(X := _, x := a) \as Instance;
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
    environment.add_new_module_to_root(&modules[1]).unwrap();
}

#[test]
fn module_parameter_hole_uses_the_same_structured_ambiguity() {
    let modules = parse::str_parse_modules(r#"\module Pending(A: _) {}"#).unwrap();
    let mut environment = GlobalEnvironment::default();
    assert!(matches!(
        environment.add_new_module_to_root(&modules[0]),
        Err(ElaborationError::AmbiguousImplicit(_))
    ));
}

#[test]
fn inductive_constructor_parameter_is_inferred_from_its_field() {
    let source = r#"
        \module InductiveMeta(A: \Set(0), a: A) {
            \inductive Box(X: \Set(0)): \Set(0) :=
                | box: X -> Box;
            ;
            \definition boxed: Box[A] := Box[_]#box a;
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
}

#[test]
fn rich_goal_format_contains_context_and_constraints() {
    let source = r#"
        \module Goal(A: \Set(0)) {
            \definition pending: A := ?2;
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    let error = environment.add_new_module_to_root(&modules[0]).unwrap_err();
    let rendered = crate::metavariables::format_elaboration_error(environment.crate_env(), &error);
    assert!(rendered.contains("?2"));
    assert!(rendered.contains("context:"));
    assert!(rendered.contains("constraints:"));
}

#[test]
fn goal_keeps_consumed_and_residual_related_constraints() {
    let source = r#"
        \module GoalHistory(A: \Set(0), a: A) {
            \definition pending: \Prop := ?2 = a;
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    let error = environment.add_new_module_to_root(&modules[0]).unwrap_err();
    let ElaborationError::UnsolvedGoals(goals) = error else {
        panic!("expected an unsolved goal");
    };
    assert_eq!(goals.len(), 1);
    assert!(goals[0].constraints.len() >= 2);
    assert!(goals[0].constraints.iter().any(|constraint| matches!(
        constraint.status,
        crate::metavariables::ConstraintStatus::Discharged
    )));
    assert!(goals[0].constraints.iter().any(|constraint| matches!(
        constraint.status,
        crate::metavariables::ConstraintStatus::Residual
    )));
}

#[test]
fn named_goals_share_but_bare_goals_are_fresh() {
    fn goal_count(source: &str) -> usize {
        let modules = parse::str_parse_modules(source).unwrap();
        let mut environment = GlobalEnvironment::default();
        match environment.add_new_module_to_root(&modules[0]).unwrap_err() {
            ElaborationError::UnsolvedGoals(goals) => goals.len(),
            error => panic!("expected goals, found {error:?}"),
        }
    }

    assert_eq!(
        goal_count(r#"\module Named { \definition pending: \Prop := ?2 = ?2; }"#),
        1
    );
    assert_eq!(
        goal_count(r#"\module Fresh { \definition pending: \Prop := ? = ?; }"#),
        2
    );
}

#[test]
fn subset_intro_construction_and_reuse() {
    let source = r#"
        \module NamedSubset(A: \Set(0)) {
            \definition XSet: \Power(A) := \Subset(x, A, x = x);
            \definition X: \Set(0) := \Ty(A, XSet);
            \definition make: (x: A) -> X :=
                (x: A) => \subsetinto(A, XSet, x, \refl(x));
            \definition reuse: (x: X) -> X := (x: X) => x;
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();

    environment.add_new_module_to_root(&modules[0]).unwrap();
}

#[test]
fn subset_intro_rejects_wrong_membership_proof() {
    let source = r#"
        \module NamedSubset(A: \Set(0)) {
            \definition XSet: \Power(A) := \Subset(x, A, x = x);
            \definition X: \Set(0) := \Ty(A, XSet);
            \definition bad: (x: A) -> X :=
                (x: A) => \subsetinto(A, XSet, x, x);
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();

    assert!(environment.add_new_module_to_root(&modules[0]).is_err());
}

#[test]
fn subset_intro_syntax_requires_an_explicit_proof() {
    let source = r#"
        \module NamedSubset(A: \Set(0)) {
            \definition XSet: \Power(A) := \Subset(x, A, x = x);
            \definition X: \Set(0) := \Ty(A, XSet);
            \definition bad: (x: A) -> X :=
                (x: A) => \subsetinto(A, XSet, x);
        }
    "#;
    assert!(parse::str_parse_modules(source).is_err());
}

#[test]
fn general_recursion_surface_typechecks_and_normalizes() {
    let source = r#"
        \module GeneralRecursion(
            A: \VType,
            B: \VType,
            f: \U(\CFun(A, \F(\RunStep(A, B)))),
            a: A,
            p: \Acc(A, B, f, \RfTerm(A, a))
        ) {
            \definition result: \F(B) := \run(A, B, f, a, p);
            \normalize \run(A, B, f, a, p);
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();

    environment.add_new_module_to_root(&modules[0]).unwrap();
}

#[test]
fn accessibility_proof_constructor_syntax_is_reserved_and_parsed() {
    let source = r#"
        \module AccSyntax(
            A: \VType,
            B: \VType,
            f: \U(\CFun(A, \F(\RunStep(A, B)))),
            a: \RfType(A),
            b: \RfType(A),
            p: \Prop,
            q: \Prop,
            e: \Prop
        ) {
            \infer \accintro(A, B, f, a, q);
            \infer \accdescent(A, B, f, a, b, p, e);
        }
    "#;

    parse::str_parse_modules(source).unwrap();
}

#[test]
fn accessibility_intro_and_descent_follow_the_system_premises() {
    let source = r#"
        \module AccProofs(
            A: \VType,
            B: \VType,
            f: \U(\CFun(A, \F(\RunStep(A, B)))),
            a: \RfType(A),
            b: \RfType(A),
            predecessors:
                (next: \RfType(A)) ->
                ((\RfTerm(\U(\CFun(A, \F(\RunStep(A, B)))), f)) a =
                 (\RfTerm(\U(\CFun(A, \F(\RunStep(A, B)))),
                     \thunk(\clam(x, A, \return(\continue(A, B, x)))))) next) ->
                \Acc(A, B, f, next),
            p: \Acc(A, B, f, a),
            edge:
                (\RfTerm(\U(\CFun(A, \F(\RunStep(A, B)))), f)) a =
                (\RfTerm(\U(\CFun(A, \F(\RunStep(A, B)))),
                    \thunk(\clam(x, A, \return(\continue(A, B, x)))))) b
        ) {
            \definition introduced: \Acc(A, B, f, a) :=
                \accintro(A, B, f, a, predecessors);
            \definition descended: \Acc(A, B, f, b) :=
                \accdescent(A, B, f, a, b, p, edge);
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();

    environment.add_new_module_to_root(&modules[0]).unwrap();
}
