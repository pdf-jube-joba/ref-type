use crate::raw::{
    environment::{DefinedConstant, ModuleItem},
    exp::ExpNode,
};
use crate::{
    elaborator::GlobalEnvironment,
    metavariables::ElaborationError,
    parse,
    syntax::{SExp, SurfaceMeta},
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
    let (head, _) = crate::raw::utils::decompose_app(env.arena(), body);
    assert!(matches!(
        env.arena().get(head),
        ExpNode::DefinedConstant(definition) if definition == carrier
    ));
}

#[test]
fn deeply_nested_expressions_and_arrow_precedence() {
    // Re-parsing a non-arrow expression at every level makes these inputs
    // exponential, although their syntax trees are small.
    let nested = format!("{}x{}", "(".repeat(48), ")".repeat(48));
    assert!(matches!(
        parse::str_parse_exp(&nested).unwrap(),
        SExp::AccessPath { .. }
    ));
    let nested = format!("{}x{}", r"\return(".repeat(48), ")".repeat(48));
    let mut term = parse::str_parse_exp(&nested).unwrap();
    for _ in 0..48 {
        let SExp::Return { value } = term else {
            panic!("missing nested return");
        };
        term = *value;
    }
    assert!(matches!(term, SExp::AccessPath { .. }));

    let SExp::Prod { bind, body } = parse::str_parse_exp(r"f x -> \fun (_: Y) => z").unwrap()
    else {
        panic!("expected outer product");
    };
    let crate::syntax::Bind::Named(bind) = bind else {
        panic!("expected unnamed domain");
    };
    assert!(bind.vars.is_empty());
    assert!(matches!(*bind.ty, SExp::App { .. }));
    assert!(matches!(*body, SExp::Lam { .. }));

    for invalid in ["(x: X)", "((x: X) | P)", "x ->", "x =>", "(x"] {
        assert!(parse::str_parse_exp(invalid).is_err(), "accepted {invalid}");
    }
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
            \definition id: \forall (X: \Set(0)) -> X -> X :=
                \fun (X: \Set(0)) => \fun (value: X) => value;
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
            \definition first: A -> A -> A := \fun (left: A) => \fun (right: A) => left;
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
            \definition first: A -> A -> A := \fun (left: A) => \fun (right: A) => left;
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
            \definition keep_a: A -> A -> A := \fun (left: A) => \fun (right: A) => left;
            \definition keep_b: A -> A -> B := \fun (left: A) => \fun (right: A) => b;
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
            \definition first: A -> A -> A := \fun (left: A) => \fun (right: A) => left;
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
            \macro constant($body) := \fun (x: A) => $body;
            \definition keep_outer: A -> A -> A :=
                \fun (x: A) => constant!{x};
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
            \macro mixed() := (\fun (x: A) => x) x;
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
        r#"\module ReservedTypeArrow { \math-macro bad($left, \~>, $right) := $left; }"#,
        r#"\module ReservedBindArrow { \math-macro bad($left, \<-, $right) := $left; }"#,
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
            \definition identity: A -> A := \fun (x: _) => x;
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
                \forall (X: \Set(0)) -> X -> X -> X :=
                \fun (X: \Set(0)) => \fun (left: X) => \fun (right: X) => left;
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
            \definition pending: A -> A := \fun (x: A) => ?;
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
                \forall (A: \Set(0)) -> A -> A :=
                \fun (A: \Set(0)) => \fun (x: A) =>
                    (\fun (X: \Set(0)) => \fun (value: X) => value) _ x;
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
            \definition make: \forall (x: A) -> X :=
                \fun (x: A) => \subsetinto(A, XSet, x, \refl(x));
            \definition reuse: \forall (x: X) -> X := \fun (x: X) => x;
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
            \definition bad: \forall (x: A) -> X :=
                \fun (x: A) => \subsetinto(A, XSet, x, x);
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
            \definition bad: \forall (x: A) -> X :=
                \fun (x: A) => \subsetinto(A, XSet, x);
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
            f: \U((A ~> \F(\PRunStep(A, B)))),
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
                \forall (next: A) ->
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
    let parsed = parse::str_parse_exp(r"(\let x: A := a \in \return(x))").unwrap();
    assert!(matches!(parsed, SExp::ValueLet { .. }));
    assert!(parse::str_parse_exp(r"(\let x := a \in \return x)").is_err());
}

#[test]
fn program_value_let_solves_and_zonks_type_annotations() {
    use crate::raw::program::{ComputationTermNode, ValueTypeNode};
    let modules = parse::str_parse_modules(
        r#"
        \module AnnotatedLet(A: \VType, a: A) {
            \cdefinition identity: \F(A) := (\let x: _ := a \in \return(x));
            \cdefinition nested: \F(A) := (\let x: A := a \in (\let y: _ := x \in \return(y)));
            \cinfer (\let x: _ := a \in \return(x));
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
    let ComputationTermNode::ValueLet { value_ty, .. } = env.arena().get(*body) else {
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
        r"(\let x: B := a \in \return(a))",
        r"(\let x: a := a \in \return(a))",
        r"(\let x: _ := ? \in \return(a))",
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
            \macro local($type, $value) := (\let A: $type := $value \in \return(A));
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
    let env = crate::raw::environment::CrateEnv::new();
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
    use crate::raw::program::ComputationTermNode;
    let modules = parse::str_parse_modules(
        r#"
        \module LetCase(A: \VType) {
            \inductive Pair(X: \VType): \VType :=
            | pair: X -> X -> Pair;
            ;
            \cdefinition first: (Pair[A] ~> \F(A)) :=
                (\cfun (p: Pair[A]) => \match (p) \in Pair \with {
                | pair left right => (\let x: A := left \in \return(x));
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
    let ComputationTermNode::Lambda { body, .. } = env.arena().get(*body) else {
        panic!()
    };
    // Reflect the open case directly, without the enclosing lambda's context.
    let reflected = crate::raw::reflection::reflect_computation(env, body).unwrap();
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

#[test]
fn set_recursion_preserves_a_shared_universe() {
    for level in [0, 2] {
        let source = r#"
            \module SharedUniverse(
                A: \Set(LEVEL), B: \Set(LEVEL), a: A, b: B,
                f: A -> \RunStep(A, B),
                p: \Acc(A, B, f, a),
                predecessors: \forall (next: A) ->
                    (f a = \continue(A, B, next)) -> \Acc(A, B, f, next),
                edge: f a = \continue(A, B, a),
                P: \Prop, proof: P
            ) {
                \definition step_type: \Set(LEVEL) := \RunStep(A, B);
                \definition continued: step_type := \continue(A, B, a);
                \definition finished: step_type := \finish(A, B, b);
                \definition inferred_continue: step_type := \continue(_, B, a);
                \definition inferred_finish: step_type := \finish(A, _, b);
                \definition inferred_run: B := \run(_, B, f, a) \by p;
                \definition introduced: \Acc(A, B, f, a) :=
                    \accintro(A, B, f, a, predecessors);
                \definition descended: \Acc(A, B, f, a) :=
                    \accdescent(A, B, f, a, a, p, edge);
                \definition result: B := \run(A, B, f, a) \by p;
                \definition case_result: B :=
                    \runCase(A, B, f, a, \continue(A, B, a)) \by (p, edge);
                \definition recursed: B := \runStepRec(A, B,
                    \fun (r: step_type) => B, \fun (x: A) => b, \fun (y: B) => y, finished);
                \definition recursed_proof: P := \runStepRec(A, B,
                    \fun (r: step_type) => P, \fun (x: A) => proof, \fun (y: B) => proof, continued);
            }
        "#
        .replace("LEVEL", &level.to_string());
        let modules = parse::str_parse_modules(&source).unwrap();
        let mut environment = GlobalEnvironment::default();
        environment.add_new_module_to_root(&modules[0]).unwrap();
    }
}

#[test]
fn run_step_recursor_distinguishes_branch_and_result_sorts() {
    let source = r#"
        \module InvalidMotive(A: \Set(2), a: A, B: \Set(0), b: B) {
            \definition bad: B := \runStepRec(A, A,
                \fun (r: \RunStep(A, A)) => B,
                \fun (x: A) => b, \fun (x: A) => b, \finish(A, A, a));
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
}

#[test]
fn run_step_inference_with_metavariables_preserves_the_universe() {
    use crate::raw::{environment::CrateEnv, exp::ExpContextEntry, ids::SymbolId, sort::Sort};
    use crate::{metavariables::MetaStore, syntax::SourceSpan};

    for level in [0, 2] {
        let env = CrateEnv::new();
        let arena = env.arena();
        let mut context = vec![ExpContextEntry {
            var: SymbolId(0),
            ty: arena.sort(Sort::Set(level)),
        }];
        let state_ty = arena.exp_bound(0);
        let mut metas = MetaStore::default();
        let hole = metas.fresh(
            &env,
            SurfaceMeta::Goal,
            SourceSpan { start: 0, end: 1 },
            &context,
            context.len(),
        );
        // ((x: A) => A) ? still contains a goal, so inference must use
        // the elaborator path while retaining A's universe level.
        let family = arena.alloc(ExpNode::Lam {
            var: SymbolId(1),
            ty: state_ty,
            body: arena.exp_bound(1),
        });
        let state_with_hole = arena.alloc(ExpNode::App {
            func: family,
            arg: hole,
        });
        let run_step = arena.alloc(ExpNode::RunStep {
            state_ty: state_with_hole,
            result_ty: state_ty,
        });
        let inferred = metas
            .infer_sort(&env, env.root_module(), &mut context, run_step)
            .unwrap();
        assert_eq!(inferred, Sort::Set(level));
        assert!(metas.contains_unsolved(&env, run_step));
    }
}

#[test]
fn inferred_recursion_annotations_still_reject_mixed_universes() {
    for term in [r"\continue(_, B, a)", r"\finish(A, _, b)"] {
        let source = format!(
            r"\module Mixed(A: \Set(0), B: \Set(2), a: A, b: B) {{
            \definition bad: _ := {term};
        }}"
        );
        let modules = parse::str_parse_modules(&source).unwrap();
        let mut environment = GlobalEnvironment::default();
        let error = environment.add_new_module_to_root(&modules[0]).unwrap_err();
        assert!(
            format!("{error:?}").contains("must inhabit the same Set(i)"),
            "{error:?}"
        );
    }
}

#[test]
fn indexed_box_steps_preserve_accessibility_certificates() {
    let source = r#"
        \module CertifiedSteps {
          \inductive Unit: \VType := | unit: Unit; | other: Unit; ;
          \vdefinition step: \U((Unit ~> \F(\PRunStep(Unit, Unit)))) :=
            \thunk((\cfun (s: Unit) => \return(\Pfinish(Unit, Unit, Unit::unit))));
          \definition stepSet: Unit -> \RunStep(Unit, Unit) :=
            \Force(\U((Unit ~> \F(\PRunStep(Unit, Unit)))),
              \box(\U((Unit ~> \F(\PRunStep(Unit, Unit)))), step));
          \definition ready: \RunStep(Unit, Unit) -> \Prop :=
            \fun (r: \RunStep(Unit, Unit)) => \Pred(Unit,
              \runStepRec(Unit, Unit, \fun (r: \RunStep(Unit, Unit)) => \Power(Unit),
                \fun (s: Unit) => \Subset(x, Unit, \Acc(Unit, Unit, stepSet, s)),
                \fun (o: Unit) => \Subset(x, Unit, Unit::unit = Unit::unit), r), Unit::unit);
          \definition terminates: \forall (s: Unit) -> \Acc(Unit, Unit, stepSet, s) :=
            \fun (s: Unit) => \accintro(Unit, Unit, stepSet, s,
              \fun (next: Unit) => \fun (edge: stepSet s = \continue(Unit, Unit, next)) =>
                \idelim(stepSet s = \continue(Unit, Unit, next)
                  \with r: \RunStep(Unit, Unit) => ready r) \by (\refl(Unit::unit), edge));
          \cdefinition result: \F(Unit) :=
            \Prun(Unit, Unit, step, Unit::unit) \by terminates Unit::unit;
          \cdefinition otherResult: \F(Unit) :=
            \Prun(Unit, Unit, step, Unit::other) \by terminates Unit::other;
          \definition boxed: \Box(\F(Unit)) := \box(\F(Unit), result);
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut global = GlobalEnvironment::default();
    global.add_new_module_to_root(&modules[0]).unwrap();
    let raw = global.crate_env();
    let module = raw.module(raw.root_module()).children()[0];
    let computation = |name| {
        let crate::raw::environment::ModuleItem::Definition { definition, .. } =
            raw.module(module).item(name).unwrap()
        else {
            panic!("computation definition")
        };
        let crate::raw::environment::DefinedConstant::ProgramComputation {
            certified_reflection: Some(certificate),
            ..
        } = raw.definition(*definition)
        else {
            panic!("certified computation")
        };
        let term = raw
            .arena()
            .alloc(crate::raw::program::ComputationTermNode::DefinedConstant(
                *definition,
            ));
        (
            crate::raw::program::ProgramTerm::ComputationTerm(term),
            *certificate,
        )
    };
    let (result, certificate) = computation("result");
    let (_, unrelated_certificate) = computation("otherResult");
    assert!(crate::raw::reflection::certificate_matches_program(
        raw,
        result,
        certificate
    ));
    assert!(!crate::raw::reflection::certificate_matches_program(
        raw,
        result,
        unrelated_certificate,
    ));
    let crate::raw::environment::ModuleItem::Definition { definition, .. } =
        raw.module(module).item("boxed").unwrap()
    else {
        panic!("boxed definition")
    };
    let env = global.kernel_env();
    let def = env.definition(*definition).unwrap();
    let mut term = def.body;
    let mut steps = 0;
    while let Some(next) = kernel::calculus::reduce_once(env, term).unwrap() {
        kernel::check::Checker::new(env, vec![])
            .check(next, def.classifier)
            .unwrap();
        term = next;
        steps += 1;
        assert!(steps < 20);
    }
    assert!(steps >= 3);
}

#[test]
fn program_bindings_preserve_shadowing_and_evaluate_the_selected_branch() {
    use crate::raw::{
        program::{ComputationTermNode, ValueTermNode},
        program_calculus::{Evaluation, evaluate_computation},
    };
    let modules = parse::str_parse_modules(include_str!(
        "../../../tests/ok/general-recursion/block-syntax.ref"
    ))
    .unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
    let env = environment.crate_env();
    let module = env.module(env.root_module()).children()[0];
    let ModuleItem::Definition { definition, .. } = env.module(module).item("result").unwrap()
    else {
        panic!("missing result definition");
    };
    let DefinedConstant::ProgramComputation {
        body,
        certified_reflection,
        ..
    } = env.definition(*definition)
    else {
        panic!("result should be a computation");
    };
    assert!(certified_reflection.is_some());
    let Evaluation::Normal(result) = evaluate_computation(env, *body) else {
        panic!("block did not finish");
    };
    let ComputationTermNode::Return { value } = env.arena().get(result) else {
        panic!("block did not return a value");
    };
    assert!(
        matches!(env.arena().get(value), ValueTermNode::InductiveConstructor { idx: 1, fields, .. } if fields.is_empty())
    );
}

#[test]
fn program_application_classification_preserves_cbpv_boundaries() {
    use crate::syntax::{ComputationTermExp as C, ValueTermExp as V};
    let C::Application { computation, value } =
        C::try_from(parse::str_parse_exp(r"\force f x y").unwrap()).unwrap()
    else {
        panic!("outer application")
    };
    assert!(matches!(*value, V::Access(_)));
    let C::Application { computation, .. } = *computation else {
        panic!("inner application")
    };
    assert!(matches!(*computation, C::Force(_)));

    let V::Constructor { fields, .. } =
        V::try_from(parse::str_parse_exp("Pair::pair x y").unwrap()).unwrap()
    else {
        panic!("constructor application")
    };
    assert_eq!(fields.len(), 2);
    for term in [r"f (g x)", r"f (\return x)", r"f (\force suspended)"] {
        assert!(
            C::try_from(parse::str_parse_exp(term).unwrap()).is_err(),
            "accepted {term}"
        );
    }
    for term in [
        r"f x",
        r"(\thunk c) x",
        r"\Pcontinue(A, B, x) y",
        r"\Pfinish(A, B, x) y",
    ] {
        assert!(
            V::try_from(parse::str_parse_exp(term).unwrap()).is_err(),
            "accepted {term}"
        );
    }
    C::try_from(parse::str_parse_exp(r"f (\thunk (g x))").unwrap()).unwrap();
}

#[test]
fn computation_definition_headers_expand_to_explicit_lambdas() {
    let modules = parse::str_parse_modules(
        r"
        \module Headers(A: \VType, B: \VType) {
            \cdefinition f(x, y: A)(z: B): \F(A) := \return x;
            \cdefinition explicit: A ~> A ~> B ~> \F(A) :=
                \cfun (x, y: A) (z: B) => \return x;
        }
    ",
    )
    .unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_new_module_to_root(&modules[0]).unwrap();
    let env = environment.crate_env();
    let module = env.module(env.root_module()).children()[0];
    let checked_definition = |name| {
        let ModuleItem::Definition { definition, .. } = env.module(module).item(name).unwrap()
        else {
            panic!("missing definition")
        };
        let DefinedConstant::ProgramComputation {
            ty,
            body,
            certified_reflection,
        } = env.definition(*definition)
        else {
            panic!("expected computation")
        };
        assert!(certified_reflection.is_some());
        (*ty, *body, *certified_reflection)
    };
    let (ty, body, reflection) = checked_definition("f");
    let (explicit_ty, explicit_body, explicit_reflection) = checked_definition("explicit");
    assert!(crate::raw::program_calculus::computation_type_is_alpha_eq(
        env.arena(),
        ty,
        explicit_ty
    ));
    assert!(crate::raw::program_calculus::computation_is_alpha_eq(
        env.arena(),
        body,
        explicit_body
    ));
    assert!(crate::raw::calculus::exp_is_alpha_eq(
        env,
        reflection.unwrap(),
        explicit_reflection.unwrap()
    ));
    for declaration in [
        r"\vdefinition f(x: A): \U(A ~> \F(A)) := \thunk c;",
        r"\cdefinition f(x): \F(A) := \return x;",
        r"\cdefinition f(x: A \where P x): \F(A) := \return x;",
    ] {
        assert!(parse::str_parse_modules(&format!(r"\module Bad {{ {declaration} }}")).is_err());
    }
}

#[test]
fn program_records_generate_checked_projections_and_swap_fields() {
    use crate::raw::{
        program::{ComputationTermNode as C, ValueTermNode as V},
        program_calculus::{Evaluation, evaluate_computation},
    };
    let modules =
        parse::str_parse_modules(include_str!("../../../tests/ok/program-items/records.ref"))
            .unwrap();
    let mut global = GlobalEnvironment::default();
    global.add_new_module_to_root(&modules[0]).unwrap();
    let env = global.crate_env();
    let module = env.module(env.root_module()).children()[0];
    let ModuleItem::ProgramInductive {
        record_fields: Some(fields),
        associated_definitions,
        ..
    } = env.module(module).item("Pair").unwrap()
    else {
        panic!("Program record metadata");
    };
    assert_eq!(fields, &["first", "second"]);
    for (_, definition) in &associated_definitions[..2] {
        assert_eq!(env.definition_parameters(*definition).len(), 1);
        let DefinedConstant::ProgramComputation { body, .. } = env.definition(*definition) else {
            panic!("projection computation");
        };
        assert!(
            matches!(env.arena().get(*body), C::Lambda { body, .. } if matches!(env.arena().get(body), C::Case { .. }))
        );
    }
    let returned = |name| {
        let ModuleItem::Definition { definition, .. } = env.module(module).item(name).unwrap()
        else {
            panic!("named result");
        };
        let DefinedConstant::ProgramComputation { body, .. } = env.definition(*definition) else {
            panic!("computation result");
        };
        let Evaluation::Normal(term) = evaluate_computation(env, *body) else {
            panic!("evaluation must finish");
        };
        let C::Return { value } = env.arena().get(term) else {
            panic!("expected return");
        };
        env.arena().get(value)
    };
    assert!(
        matches!(returned("first"), V::InductiveConstructor { idx: 0, fields, .. } if fields.is_empty())
    );
    let V::InductiveConstructor { fields, .. } = returned("swapped") else {
        panic!("swapped record");
    };
    assert_eq!(fields.len(), 2);
    assert!(matches!(
        env.arena().get(fields[0]),
        V::InductiveConstructor { idx: 1, .. }
    ));
    assert!(matches!(
        env.arena().get(fields[1]),
        V::InductiveConstructor { idx: 0, .. }
    ));
}

#[test]
fn program_associated_imports_remap_later_declarations() {
    use crate::raw::program::{ValueTermNode, ValueTypeNode};
    let modules = parse::str_parse_modules(include_str!(
        "../../../tests/ok/program-items/associated-order.ref"
    ))
    .unwrap();
    let mut global = GlobalEnvironment::default();
    for module in &modules {
        global.add_new_module_to_root(module).unwrap();
    }
    let env = global.crate_env();
    let consumer = env.module(env.root_module()).children()[1];
    let instance = &env.module(consumer).instances()[0];
    let module = instance.materialized;
    let ModuleItem::ProgramInductive {
        associated_definitions,
        ..
    } = env.module(module).item("First").unwrap()
    else {
        panic!("owner");
    };
    let DefinedConstant::ProgramValue { ty, body, .. } =
        env.definition(associated_definitions[0].1)
    else {
        panic!("associated value");
    };
    assert!(
        matches!(env.arena().get(*ty), ValueTypeNode::Inductive { indspec, .. } if indspec.module == module)
    );
    assert!(
        matches!(env.arena().get(*body), ValueTermNode::DefinedConstant(id) if id.module == module)
    );
}

#[test]
fn program_definition_parameters_are_substituted_simultaneously_under_binders() {
    use crate::raw::{
        program::{ComputationTermNode as C, ValueTypeNode as T},
        program_definitions::instantiate_computation,
    };
    let env = crate::raw::environment::CrateEnv::new();
    let arena = env.arena();
    // Under A, B, the function takes A and then B. The instantiation arguments themselves are open types.
    let body = arena.alloc(C::Lambda {
        var: crate::raw::ids::SymbolId::ANONYMOUS,
        value_ty: arena.value_type_bound(1),
        body: arena.alloc(C::Lambda {
            var: crate::raw::ids::SymbolId::ANONYMOUS,
            value_ty: arena.value_type_bound(1),
            body: arena.alloc(C::Return {
                value: arena.value_bound(0),
            }),
        }),
    });
    let instantiated = instantiate_computation(
        arena,
        body,
        &[arena.value_type_bound(0), arena.value_type_bound(1)],
        0,
    );
    let C::Lambda { value_ty, body, .. } = arena.get(instantiated) else {
        panic!("outer lambda");
    };
    assert_eq!(arena.get(value_ty), T::Bound(0));
    let C::Lambda { value_ty, body, .. } = arena.get(body) else {
        panic!("inner lambda");
    };
    assert_eq!(arena.get(value_ty), T::Bound(2));
    let C::Return { value } = arena.get(body) else {
        panic!("return");
    };
    assert_eq!(
        arena.get(value),
        crate::raw::program::ValueTermNode::Bound(0)
    );
}

#[test]
fn variadic_macros_match_tokens_and_sequences() {
    for source in [
        include_str!("../../../tests/ok/macros/variadic_token_match.ref"),
        include_str!("../../../tests/ok/macros/recursive_hygiene.ref"),
    ] {
        let modules = parse::str_parse_modules(source).unwrap();
        let mut environment = GlobalEnvironment::default();
        for module in &modules {
            environment.add_new_module_to_root(module).unwrap();
        }
    }
}

#[test]
fn invalid_variadic_macro_templates_fail_at_declaration() {
    let cases = [
        (
            r"\macro bad(..r, $x) := $x;",
            "Rest capture must be the last",
        ),
        (
            r"\macro bad(($x, ..r, tk)) := $x;",
            "Rest capture must be the last",
        ),
        (r"\macro bad($x, x) := $x;", "declared more than once"),
        (r"\macro bad($x, ..x) := $x;", "declared more than once"),
        (
            r"\macro bad(..r) := last!{..missing};",
            "undeclared capture",
        ),
        (r"\macro bad($x) := last!{..x};", "expected Sequence"),
        (r"\macro bad(tk) := $tk;", "expected Expression"),
        (r"\macro bad(..r) := $r;", "expected Expression"),
        (
            r"\macro bad($x) := \tmatch x {};",
            "requires a token or sequence",
        ),
        (r"\macro bad() := \tmatch missing {};", "undeclared capture"),
        (
            r"\macro bad(tk) := \tmatch tk { | () => value; };",
            "expected Sequence",
        ),
        (
            r"\macro bad(..r) := \tmatch r { | \+ => value; };",
            "expected Token",
        ),
        (
            r"\macro bad(..r) := \tmatch r { | ($x, $x) => $x; };",
            "declared more than once",
        ),
        (
            r"\macro bad($x, ..r) := \tmatch r { | ($x) => $x; };",
            "declared more than once",
        ),
        (
            r"\macro bad(..r) := \tmatch r { | ($x) => $x; | () => $x; };",
            "undeclared capture",
        ),
        (
            r"\macro bad(..r) := \tmatch r { | ($x) => $x; } $x;",
            "undeclared capture",
        ),
        (
            r"\math-macro bad(..r, \+) := value;",
            "only valid in named macros",
        ),
        (
            r"\math-macro bad(tk, \+) := value;",
            "only valid in named macros",
        ),
        (
            r"\math-macro bad(\+) := \tmatch missing {};",
            "only valid in named macros",
        ),
        (
            r"\macro bad() := later!{}; \macro later() := value;",
            "not visible at template declaration",
        ),
    ];
    for (declaration, expected) in cases {
        let source = format!(r"\module Invalid(A: \Set(0), value: A) {{ {declaration} }}");
        let modules = parse::str_parse_modules(&source).unwrap();
        let mut environment = GlobalEnvironment::default();
        let error = environment.add_new_module_to_root(&modules[0]).unwrap_err();
        assert!(
            format!("{error:?}").contains(expected),
            "{declaration}: {error:?}"
        );
    }
    for source in [r"\tmatch tk {}", r"m!{..r}", r"$r"] {
        assert!(parse::str_parse_exp(source).is_err(), "{source}");
    }
}

#[test]
fn non_exhaustive_macro_matches_fail_only_when_selected() {
    for (declaration, call, expected) in [
        (
            r#"\macro m(tk) := \tmatch tk { | "+" => value; };"#,
            "m!{+}",
            "No token match branch",
        ),
        (
            r#"\macro m(tk) := \tmatch tk { | \+ => value; };"#,
            r#"m!{"+"}"#,
            "No token match branch",
        ),
        (
            r"\macro m(..r) := \tmatch r {};",
            "m!{}",
            "No token match branch",
        ),
        (
            r"\macro m(tk) := value;",
            "m!{value}",
            "Input does not match",
        ),
        (r"\macro m(tk) := value;", "m!{(+)}", "Input does not match"),
        (r"\macro m($x) := $x;", "m!{+}", "Input does not match"),
    ] {
        let source = format!(
            r"\module Invalid(A: \Set(0), value: A) {{ {declaration} \definition result: A := {call}; }}"
        );
        let modules = parse::str_parse_modules(&source).unwrap();
        let mut environment = GlobalEnvironment::default();
        let error = environment.add_new_module_to_root(&modules[0]).unwrap_err();
        assert!(format!("{error:?}").contains(expected), "{call}: {error:?}");
    }
}

#[test]
fn self_recursive_macro_expansion_respects_depth_limit() {
    for source in [
        include_str!("../../../tests/ng/macros/self_recursion_depth.ref"),
        include_str!("../../../tests/ng/macros/non_tail_recursion_depth.ref"),
    ] {
        let modules = parse::str_parse_modules(source).unwrap();
        let mut environment = GlobalEnvironment::default();
        let error = environment.add_new_module_to_root(&modules[0]).unwrap_err();
        assert!(
            format!("{error:?}").contains("Macro expansion exceeded depth 128"),
            "{error:?}"
        );
    }
}
