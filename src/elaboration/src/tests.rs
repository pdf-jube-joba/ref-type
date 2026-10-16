use crate::{
    elaborator::GlobalEnvironment,
    metavariables::ElaborationError,
    raw::{
        environment::{DefinedConstant, ModuleItem},
        exp::ExpNode,
    },
};
use ::syntax::{parse, syntax::SurfaceMeta};

#[test]
fn diamond_import_chains_keep_namespace_growth_linear() {
    let mut source = String::from(
        r"\module Base { \inductive Unit: \Set := | unit: Unit; }
          \module Layer0 { \import \root.Base[] \as B;
            \definition value: B.Unit := B.Unit::unit; }",
    );
    for level in 1..10 {
        let previous = level - 1;
        source.push_str(&format!(
            r"\module Layer{level} {{
                \import \root.Layer{previous}[] \as Left;
                \import \root.Layer{previous}[] \as Right;
                \definition agree: Left.value = Right.value := \refl(Left.value);
                \import \root.Base[] \as B;
                \definition value: B.Unit := Left.value;
            }}"
        ));
    }
    let modules = parse::str_parse_modules(&source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_modules_to_root(&modules).unwrap();
    let env = environment.crate_env();
    let layers = &env.module(env.root_module()).children()[1..];
    for (level, &layer) in layers.iter().enumerate() {
        assert!(
            env.module(layer).bindings().len() <= 2 * (level + 1) + 1,
            "Layer{level} duplicated its inherited namespaces"
        );
    }
}

#[test]
fn final_lowering_does_not_force_unused_instance_items() {
    let source = r#"
        \module Source(A: \Set(0)) {
            \definition first: \Set(0) := A;
            \definition second: \Set(0) := A;
        }
        \module Consumer(A: \Set(0)) {
            \import \root.Source[A := A] \as source;
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    for module in &modules {
        environment.add_new_module_to_root(module).unwrap();
    }
    assert_eq!(
        environment.crate_env().materialization_stats().definitions,
        0
    );
}

#[test]
fn direct_definition_specialization_preserves_dependent_carriers_and_scopes() {
    let source = r"
        \module Family(A: \Set) {
            \module At(x: A) {
                \structure Pair: \Set { value: A, equality: value = x }
                \definition Carrier: \Set := Pair;
                \definition point: Carrier := Pair { value := x, equality := \refl(x) };
                \definition value: A := x;
                \definition withValue(y: A)(proof: y = x): Pair := Pair { value := y, equality := proof };
            }
            \definition Carrier(x: A): \Set := At[x := x].Carrier;
            \definition point(x: A): Carrier x := At[x := x].point;
            \definition first(x, y: A): A := At[x := x].value;
            \definition second(x, y: A): A := At[x := y].value;
            \definition firstLaw(x, y: A): first x y = x := \refl(x);
            \definition secondLaw(x, y: A): second x y = y := \refl(y);
            \definition projection(x: A): (point x).value = x := \refl(x);
            \definition explicit(x: A): Carrier x := At[x := x].withValue x (\refl(x));
            \definition explicitProjection(x: A): (explicit x).value = x := \refl(x);
        }
    ";
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    environment.add_modules_to_root(&modules).unwrap();
    let raw = environment.crate_env();
    let family = raw.module(raw.root_module()).children()[0];
    assert!(raw.module(family).bindings().is_empty());
    assert_eq!(raw.materialization_stats().definitions, 0);
}

#[test]
fn structure_parameter_type_errors_preserve_source_context() {
    use ::syntax::syntax::{SourceFile, SourceId};

    for (declaration, parameter, reason) in [
        (
            r"\structure Packed[F: \Set -> \SetKind] {
    Cr: \Set,
    data: F Cr,
  }",
            "Packed.F",
            "upper sort has no classifier",
        ),
        (
            r"\structure Packed[A: \Set, a: A, bad: a] {}",
            "Packed.bad",
            "expected a sort",
        ),
    ] {
        let source = std::sync::Arc::new(SourceFile {
            id: SourceId("structure-parameter-error.ref".into()),
            text: format!("\\module Playground {{\n  {declaration}\n}}"),
        });
        let mut modules = parse::parse_modules_from_source(&source).unwrap();
        for module in &mut modules {
            module.source = Some(source.clone());
            module.header_source = Some(source.clone());
        }
        let mut environment = GlobalEnvironment::default();
        let error = environment.add_modules_to_root(&modules).unwrap_err();
        let rendered =
            crate::metavariables::format_elaboration_error(environment.crate_env(), &error);
        assert!(
            rendered.contains(&format!(
                "Structure parameter '{parameter}' must have a type or proposition"
            )),
            "{rendered}"
        );
        assert!(rendered.contains(reason), "{rendered}");
        assert!(
            rendered.contains("structure-parameter-error.ref:2:3"),
            "{rendered}"
        );
        let ElaborationError::Located { location, .. } = error else {
            panic!("expected a structure location");
        };
        assert_eq!(
            &source.text[location.span.start..location.span.end],
            declaration
        );
    }
}

#[test]
fn goal_keeps_consumed_and_residual_related_constraints() {
    let source = r#"
        \module GoalHistory(A: \Set(0), a: A) {
            \definition pending: \Prop := _2 = a;
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();
    let error = environment.add_new_module_to_root(&modules[0]).unwrap_err();
    let ElaborationError::Metavariables(goals) = error else {
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
fn program_case_reflects_value_let_in_parameterized_branches() {
    use crate::raw::program::ComputationTermNode;
    let modules = parse::str_parse_modules(
        r#"
        \module LetCase(A: \VType) {
          \inductive Pair[X: \VType]: \VType :=
            | pair: X -> X -> Pair
            ;
            \definition first: (Pair[A] ~> \F(A)) :=
                (\cfun (p: Pair[A]) => \match (p) \in Pair \with {
                | pair left right : (\let x: A := left \in \return(x))
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
    let DefinedConstant::ProgramComputation { body, .. } = env.definition(*definition) else {
        panic!()
    };
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
fn run_step_inference_with_metavariables_preserves_the_universe() {
    use crate::{
        metavariables::MetaStore,
        raw::{environment::CrateEnv, exp::ExpContextEntry, ids::SymbolId, sort::Sort},
    };
    use ::syntax::syntax::SourceSpan;

    for level in [0, 2] {
        let env = CrateEnv::new();
        let arena = env.arena();
        let mut context = vec![ExpContextEntry {
            var: SymbolId(0),
            ty: arena.sort(Sort::Set(level)),
        }];
        let state_ty = arena.exp_bound(0);
        let mut metas = MetaStore::default();
        let hole = metas
            .fresh(
                &env,
                SurfaceMeta::Goal,
                SourceSpan { start: 0, end: 1 },
                &context,
                context.len(),
            )
            .unwrap();
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
fn program_run_proofs_remain_valid_after_every_reduction() {
    use crate::{
        kernel_bridge::reduce_computation_once,
        raw::{
            environment::{DefinedConstant, ModuleItem},
            program_derivation::ProgramCheckSession,
        },
    };
    for source in [
        include_str!("../tests/fixtures/ok-general-recursion-finish.ref"),
        include_str!("../tests/fixtures/ok-general-recursion-continue.ref"),
        include_str!("../tests/fixtures/ok-general-recursion-run-case.ref"),
    ] {
        let modules = parse::str_parse_modules(source).unwrap();
        let mut global = GlobalEnvironment::default();
        global.add_new_module_to_root(&modules[0]).unwrap();
        let raw = global.crate_env();
        let module = raw.module(raw.root_module()).children()[0];
        let ModuleItem::Definition { definition, .. } = raw.module(module).item("result").unwrap()
        else {
            panic!()
        };
        let DefinedConstant::ProgramComputation { body, ty, .. } = raw.definition(*definition)
        else {
            panic!()
        };
        let mut term = *body;
        let mut count = 0;
        while let Some(next) = reduce_computation_once(raw, term) {
            ProgramCheckSession::new(raw, &mut vec![])
                .check_computation_term(next, *ty)
                .unwrap();
            term = next;
            count += 1;
            assert!(count < 30);
        }
        let env = global.kernel_env();
        let def = env
            .definition(raw.kernel_definitions.borrow()[definition])
            .unwrap();
        let mut term = def.body;
        let mut count = 0;
        while let Some(next) = kernel::reduction::reduce_once(&env, term).unwrap() {
            kernel::check::Checker::new(
                &env,
                &mut kernel::metavariables::MetaContext::new(),
                def.context.clone(),
            )
            .check(next, def.ty)
            .unwrap();
            term = next;
            count += 1;
            assert!(count < 30);
        }
    }
}

#[test]
fn program_definition_parameters_are_substituted_simultaneously_under_binders() {
    use crate::{
        kernel_bridge::instantiate_computation_parameters,
        raw::program::{ComputationTermNode as C, ValueTypeNode as T},
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
    let instantiated = instantiate_computation_parameters(
        &env,
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
fn program_query_parameters_are_scoped_outside_local_variables() {
    use crate::raw::{ids::ModuleParamId, program::*};
    let modules = parse::str_parse_modules(r#"\module Generic(A: \VType) {}"#).unwrap();
    let mut global = GlobalEnvironment::default();
    global.add_new_module_to_root(&modules[0]).unwrap();
    let raw = global.crate_env();
    let module = raw.module(raw.root_module()).children()[0];
    let ty = raw.arena().alloc(ValueTypeNode::ModuleParam(ModuleParamId {
        module,
        position: 0,
    }));
    let term = raw.arena().alloc(ValueTermNode::Bound(0));
    let context = vec![ProgramContextEntry::ValueTerm {
        var: crate::raw::ids::SymbolId::ANONYMOUS,
        ty,
    }];
    let mut env = kernel::environment::Environment::new();
    crate::lowering::Lowerer::new(raw, &mut env)
        .check_program_query(
            &context,
            ProgramTerm::ValueTerm(term),
            ProgramType::ValueType(ty),
        )
        .unwrap();
}

#[test]
fn definition_parameters_form_contexts_and_calls_share_the_checked_body() {
    let modules = parse::str_parse_modules(
        r"\module Contexts(A: \Set, P: \Prop, p: P, Unused: \Set) {
            \definition choose(h: P)(x: A): A := x;
            \definition selected(x: A): A := choose p x;
        }",
    )
    .unwrap();
    let mut global = GlobalEnvironment::default();
    global.add_new_module_to_root(&modules[0]).unwrap();
    let raw = global.crate_env();
    let module = raw.module(raw.module(raw.root_module()).children()[0]);
    let definition = |name| match module.item(name).unwrap() {
        ModuleItem::Definition { definition, .. } => *definition,
        _ => panic!("expected definition"),
    };
    let choose = definition("choose");
    let DefinedConstant::Contextual { parameters, .. } = raw.definition(choose) else {
        panic!("expected a contextual definition")
    };
    assert_eq!(parameters.len(), 2);
    let env = global.kernel_env();
    let choose = raw.kernel_definitions.borrow()[&choose];
    assert_eq!(env.definition(choose).unwrap().context.len(), 4);
    let selected = raw.kernel_definitions.borrow()[&definition("selected")];
    assert_eq!(env.definition(selected).unwrap().context.len(), 4);
    assert_eq!(
        env.referenced_definition(env.definition(selected).unwrap().body),
        Some(choose)
    );
}

#[test]
fn debug_printing_bounds_shared_expression_expansion() {
    let env = crate::raw::environment::CrateEnv::new();
    let mut expression = env.arena().sort(crate::raw::sort::Sort::Set(0));
    for _ in 0..30 {
        expression = env.arena().alloc(crate::raw::exp::ExpNode::App {
            func: expression,
            arg: expression,
        });
    }
    let rendered = crate::raw::printing::format_exp(&env, expression);
    assert!(rendered.len() <= crate::diagnostics::EXPRESSION_BYTES);
    assert!(rendered.contains("@expr") || rendered.contains('…'));
}
