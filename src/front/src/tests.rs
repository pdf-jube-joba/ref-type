use crate::{
    elaborator::GlobalEnvironment,
    metavariables::ElaborationError,
    parse,
    syntax::{SExp, SurfaceMeta},
};
use kernel::{
    environment::{DefinedConstant, ModuleItem},
    exp::ExpNode,
};

#[test]
fn record_fields_are_generated_as_eliminator_definitions() {
    let source = r#"
        \module Records {
            \structure Packed: \SetKind := {
                carrier: \Set,
                value: carrier,
            };
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();

    let env = environment.crate_env();
    let module = env.module(env.root_module()).children()[0];
    let ModuleItem::Record {
        associated_definitions,
        ..
    } = env.module(module).item("Packed").unwrap()
    else {
        panic!("Packed should be a record");
    };
    assert_eq!(
        associated_definitions
            .iter()
            .map(|(name, _)| name.as_str())
            .collect::<Vec<_>>(),
        ["carrier", "value"]
    );

    let carrier = associated_definitions[0].1;
    let DefinedConstant::Pts { body, .. } = env.definition(carrier) else {
        panic!("carrier projection should be a PTS definition");
    };
    assert!(matches!(
        env.arena().get(*body),
        ExpNode::Lam { body, .. } if matches!(env.arena().get(body), ExpNode::IndElim { .. })
    ));

    let DefinedConstant::Pts { ty, .. } = env.definition(associated_definitions[1].1) else {
        panic!("value projection should be a PTS definition");
    };
    let ExpNode::Prod { body, .. } = env.arena().get(*ty) else {
        panic!("value projection should accept the structure");
    };
    let (head, _) = kernel::utils::decompose_app(env.arena(), body);
    assert!(matches!(
        env.arena().get(head),
        ExpNode::DefinedConstant(definition) if definition == carrier
    ));
}

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
fn local_math_and_named_macros_expand_before_elaboration() {
    let source = r#"
        \module Macros(A: \Set(0), x: A, y: A) {
            \definition first: A -> A -> A := (left: A) => (right: A) => left;
            \math-macro plus($left, \+, $right) := first $left $right;
            \math-macro meet($left, \/\, $right) := first $left $right;
            \macro via_math($left, $right) := $($left + $right $);
            \macro tagged($term, "ok") := $term;
            \definition from_math: A := $(x + y $);
            \definition from_nested_math: A := $((x + y) + x $);
            \definition from_separate_operators: A := $((x + y) + (x /\ y) $);
            \definition from_named: A := tagged!{y "ok"};
            \definition from_nested_macro: A := via_math!{x y};
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
}

#[test]
fn only_the_documented_macro_surface_syntax_is_accepted() {
    assert!(parse::str_parse_exp("$value").is_err());
    assert!(parse::str_parse_exp("named !{value}").is_err());
    assert!(parse::str_parse_exp("$(value )$").is_err());
}

#[test]
fn math_macro_requires_the_complete_sequence() {
    let source = r#"
        \module Macros(A: \Set(0), x: A, y: A) {
            \definition first: A -> A -> A := (left: A) => (right: A) => left;
            \math-macro plus($left, \+, $right) := first $left $right;
            \definition chained: A := $(x + y + x $);
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    assert!(environment.add_new_module_to_root(&modules[0]).is_err());
}

#[test]
fn earlier_math_macro_wins_when_patterns_are_equally_applicable() {
    let source = r#"
        \module Priority(A: \Set(0), B: \Set(0), a: A, b: B) {
            \definition keep_a: A -> A -> A := (left: A) => (right: A) => left;
            \definition keep_b: A -> A -> B := (left: A) => (right: A) => b;
            \math-macro earlier($left, \+, $right) := keep_a $left $right;
            \math-macro later($left, \+, $right) := keep_b $left $right;
            \definition selected: A := $(a + a $);
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
}

#[test]
fn macro_templates_cannot_see_later_macro_declarations() {
    let source = r#"
        \module Ordered(A: \Set(0), x: A, y: A) {
            \definition first: A -> A -> A := (left: A) => (right: A) => left;
            \macro too_early($left, $right) := $($left + $right $);
            \math-macro plus($left, \+, $right) := first $left $right;
            \definition result: A := too_early!{x y};
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    assert!(environment.add_new_module_to_root(&modules[0]).is_err());
}

#[test]
fn imported_macro_uses_the_materialized_module_arguments() {
    let source = r#"
        \module Provider(A: \Set(0), value: A) {
            \definition stored: A := value;
            \macro supplied() := stored;
            \math-macro imported_plus($left, \+, $right) := stored;
        }
        \module Consumer(A: \Set(0), value: A) {
            \import \root.Provider(A := A, value := value) \as provider;
            \use provider.supplied;
            \use provider.imported_plus;
            \definition result: A := supplied!{};
            \definition math_result: A := $(value + value $);
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
    environment.add_new_module_to_root(&modules[1]).unwrap();
}

#[test]
fn child_modules_see_macros_already_declared_by_their_parent() {
    let source = r#"
        \module Parent(A: \Set(0), value: A) {
            \macro parent_value() := value;
            \module Child {
                \definition result: A := parent_value!{};
            }
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
}

#[test]
fn instantiated_macro_keeps_macros_used_by_its_definition_module() {
    let source = r#"
        \module Base(A: \Set(0), value: A) {
            \macro base_value() := value;
        }
        \module Wrapper(A: \Set(0), value: A) {
            \import \root.Base(A := A, value := value) \as base;
            \use base.base_value;
            \macro wrapped() := base_value!{};
        }
        \module Consumer(A: \Set(0), value: A) {
            \import \root.Wrapper(A := A, value := value) \as wrapper;
            \use wrapper.wrapped;
            \definition result: A := wrapped!{};
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    for module in &modules {
        environment.add_new_module_to_root(module).unwrap();
    }
}

#[test]
fn macro_binders_do_not_capture_call_site_expressions() {
    let source = r#"
        \module Hygiene(A: \Set(0)) {
            \macro constant($body) := (x: A) => $body;
            \definition keep_outer: A -> A -> A :=
                (x: A) => constant!{x};
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
}

#[test]
fn macro_hygiene_does_not_rename_a_same_named_free_identifier() {
    let source = r#"
        \module Hygiene(A: \Set(0), x: A) {
            \macro mixed() := ((x: A) => x) x;
            \definition result: A := mixed!{};
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
}

#[test]
fn imported_macro_resolves_free_names_at_its_definition_site() {
    let source = r#"
        \module Provider(A: \Set(0), provided: A) {
            \macro supplied() := provided;
        }
        \module Consumer(A: \Set(0), B: \Set(0), a: A, provided: B) {
            \import \root.Provider(A := A, provided := a) \as provider;
            \use provider.supplied;
            \definition result: A := supplied!{};
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
    environment.add_new_module_to_root(&modules[1]).unwrap();
}

#[test]
fn macro_names_must_remain_unambiguous() {
    let source = r#"
        \module Collision(A: \Set(0), value: A) {
            \macro same() := value;
            \macro same($value) := $value;
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    assert!(environment.add_new_module_to_root(&modules[0]).is_err());
}

#[test]
fn invalid_macro_patterns_fail_at_declaration() {
    for source in [
        r#"\module Duplicate { \macro bad($value, $value) := $value; }"#,
        r#"\module Reserved { \math-macro bad($left, \:, $right) := $left; }"#,
        r#"\module NoToken { \math-macro bad($value) := $value; }"#,
        r#"\module UnknownCapture { \macro bad($value) := $other; }"#,
    ] {
        let modules = parse::str_parse_modules(source).unwrap();
        let mut environment = GlobalEnvironment::default();
        assert!(environment.add_new_module_to_root(&modules[0]).is_err());
    }
}

#[test]
fn macro_expansion_has_a_finite_depth_limit() {
    let mut source = String::from("\\module Deep(A: \\Set(0), value: A) {");
    source.push_str("\\macro m0() := value;");
    for index in 1..=129 {
        source.push_str(&format!("\\macro m{index}() := m{}!{{}};", index - 1));
    }
    source.push_str("\\definition result: A := m129!{}; }");
    let modules = parse::str_parse_modules(&source).unwrap();
    let mut environment = GlobalEnvironment::default();
    assert!(environment.add_new_module_to_root(&modules[0]).is_err());
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
fn program_value_definition_uses_the_value_judgement() {
    let source = r#"
        \module ProgramMeta(A: \VType, x: A) {
            \vdefinition finished: \PRunStep(A, A) := \Pfinish(A, A, x);
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
}

#[test]
fn program_value_and_computation_commands_are_separate() {
    let source = r#"
            \module ProgramTypeMeta(A: \VType, x: A) {
                \vdefinition value: A := x;
                \cdefinition computation: \F(A) := \return(x);
                \ceval computation;
            \vinfer value;
            \cinfer computation;
            \vcheck value: A;
            \ccheck computation: \F(A);
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
            \definition boxed: Box[A] := Box[_]::box a;
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
            f: \U(\CFun(A, \F(\PRunStep(A, B)))),
            a: A
        ) {
            \cdefinition result: \F(B) := \Prun(A, B, f, a);
            \cnormalize \Prun(A, B, f, a);
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
            A: \Set(0),
            B: \Set(0),
            f: A -> \RunStep(A, B),
            a: A,
            b: A,
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
            A: \Set(0),
            B: \Set(0),
            f: A -> \RunStep(A, B),
            a: A,
            b: A,
            predecessors:
                (next: A) ->
                (f a = \continue(A, B, next)) ->
                \Acc(A, B, f, next),
            p: \Acc(A, B, f, a),
            edge: f a = \continue(A, B, b)
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

#[test]
fn program_value_let_requires_an_annotation() {
    let parsed = parse::str_parse_exp(r"\vlet(x, A, a, \return(x))").unwrap();
    assert!(matches!(parsed, SExp::ValueLet { .. }));
    assert!(parse::str_parse_exp(r"\vlet(x, a, \return(x))").is_err());
}

#[test]
fn program_value_let_solves_and_zonks_type_annotations() {
    use kernel::program::{ComputationNode, ValueTypeNode};
    let modules = parse::str_parse_modules(
        r#"
        \module AnnotatedLet(A: \VType, a: A) {
            \cdefinition identity: \F(A) := \vlet(x, _, a, \return(x));
            \cdefinition nested: \F(A) := \vlet(x, A, a, \vlet(y, _, x, \return(y)));
            \cinfer \vlet(x, _, a, \return(x));
        }
    "#,
    )
    .unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
    let env = environment.crate_env();
    let module = env.module(env.root_module()).children()[0];
    let ModuleItem::Definition { definition, .. } = env.module(module).item("identity").unwrap()
    else {
        panic!()
    };
    let DefinedConstant::ProgramComputation {
        body,
        certified_reflection,
        ..
    } = env.definition(*definition)
    else {
        panic!()
    };
    let ComputationNode::ValueLet { value_ty, .. } = env.arena().get(*body) else {
        panic!()
    };
    assert!(matches!(
        env.arena().get(value_ty),
        ValueTypeNode::ModuleParam(_)
    ));
    assert!(certified_reflection.is_some());
}

#[test]
fn program_value_let_rejects_invalid_annotations_and_unsolved_metas() {
    for term in [
        r"\vlet(x, B, a, \return(a))",
        r"\vlet(x, a, a, \return(a))",
        r"\vlet(x, _, ?, \return(a))",
    ] {
        let source = format!(
            r"\module InvalidLet(A: \VType, B: \VType, a: A) {{ \cdefinition result: \F(A) := {term}; }}"
        );
        let modules = parse::str_parse_modules(&source).unwrap();
        let mut environment = GlobalEnvironment::default();
        assert!(
            environment.add_new_module_to_root(&modules[0]).is_err(),
            "accepted {term}"
        );
    }
}

#[test]
fn program_value_let_macro_annotations_use_the_outer_scope() {
    use crate::{elaborator::module_manager::ModuleManager, macros::MacroKind, syntax::ModuleBody};
    let modules = parse::str_parse_modules(
        r#"
        \module LetMacros {
            \macro local($type, $value) := \vlet(A, $type, $value, \return(A));
        }
    "#,
    )
    .unwrap();
    let ModuleBody::Inline(items) = &modules[0].body else {
        panic!()
    };
    let crate::syntax::ModuleItem::UserMacro {
        name,
        before,
        after,
    } = &items[0]
    else {
        panic!()
    };
    let env = kernel::environment::CrateEnv::new();
    let mut manager = ModuleManager::new();
    manager
        .register_macro(
            &env,
            name.clone(),
            MacroKind::Named,
            before.clone(),
            after.clone(),
        )
        .unwrap();
    let SExp::NamedMacro { name, tokens, .. } = parse::str_parse_exp("local!{A a}").unwrap() else {
        panic!()
    };
    let expanded = manager
        .expand_named_macro(&env, env.root_module(), &name, &tokens, 0, None)
        .unwrap();
    let SExp::ValueLet {
        var,
        value_ty,
        value,
        body,
    } = expanded
    else {
        panic!()
    };
    assert_ne!(var.as_str(), "A");
    assert!(
        matches!(*value_ty, SExp::AccessPath { access: crate::syntax::LocalAccess::Current { access }, .. } if access.as_str() == "A")
    );
    assert!(
        matches!(*value, SExp::AccessPath { access: crate::syntax::LocalAccess::Current { access }, .. } if access.as_str() == "a")
    );
    let SExp::Return { value } = *body else {
        panic!()
    };
    assert!(
        matches!(*value, SExp::AccessPath { access: crate::syntax::LocalAccess::Current { access }, .. } if access == var)
    );
}

#[test]
fn program_case_reflects_value_let_in_parameterized_branches() {
    use kernel::program::ComputationNode;
    let modules = parse::str_parse_modules(
        r#"
        \module LetCase(A: \VType) {
            \inductive Pair(X: \VType): \VType :=
            | pair: X -> X -> Pair;
            ;
            \cdefinition first: \CFun(Pair[A], \F(A)) :=
                \clam(p, Pair[A], \vcase(Pair, p) {
                | pair(left, right) => \vlet(x, A, left, \return(x));
                });
        }
    "#,
    )
    .unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
    let env = environment.crate_env();
    let module = env.module(env.root_module()).children()[0];
    let ModuleItem::Definition { definition, .. } = env.module(module).item("first").unwrap()
    else {
        panic!()
    };
    let DefinedConstant::ProgramComputation {
        body,
        certified_reflection,
        ..
    } = env.definition(*definition)
    else {
        panic!()
    };
    assert!(certified_reflection.is_some());
    let ComputationNode::Lambda { body, .. } = env.arena().get(*body) else {
        panic!()
    };
    // Reflect the open case directly, without the enclosing lambda's context.
    let reflected = kernel::reflection::reflect_computation(env, body).unwrap();
    let ExpNode::ReflectedProgramCase {
        scrutinee,
        branches,
        ..
    } = env.arena().get(reflected)
    else {
        panic!()
    };
    assert_eq!(env.arena().get(scrutinee), ExpNode::Bound(0));
    assert_eq!(branches[0].binders.len(), 2);
    assert!(matches!(
        env.arena().get(branches[0].body),
        ExpNode::App { .. }
    ));
}
