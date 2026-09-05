use crate::{
    calculus::{
        convertible, erased_convertible, erased_normal, exp_is_alpha_eq, exp_subst_module_param,
        instantiate, instantiate_outer_telescope, instantiate_telescope, normalize, reduce_one,
        whnf,
    },
    derivation::CheckSession,
    environment::{
        CrateEnv, DefinedConstant, DefinitionKind, ModuleParameter, ModuleParameterKind,
    },
    exp::{Context, ContextEntry, Exp, Node, ProgramCaseBranch},
    ids::{MetaVarId, ModuleId, ModuleParamId, SymbolId},
    inductive::{CtorBinder, CtorType, InductiveTypeSpecs},
    printing::format_exp,
    program_inductive::{ProgramConstructorSpec, ProgramInductiveTypeSpecs},
    sort::Sort,
};
use std::cell::RefCell;

#[test]
fn strict_kernel_rejects_elaboration_metavariables() {
    let mut fixture = Fixture::new();
    let meta = fixture.env.arena().alloc(Node::Meta {
        metavariable: MetaVarId(0),
        spine: Vec::new(),
    });
    assert!(
        CheckSession::new(&fixture.env, ModuleId(0), &mut fixture.context)
            .infer_pts(meta)
            .is_err()
    );
}

struct Fixture {
    env: CrateEnv,
    context: Context,
}

impl Fixture {
    fn new() -> Self {
        Self {
            env: CrateEnv::new(),
            context: vec![],
        }
    }

    fn var(&self, name: &str) -> (SymbolId, Exp) {
        let position = match name {
            "target" => 10,
            "stable" => 11,
            _ => 12,
        };
        let var = SymbolId(position);
        let exp = self.env.arena().module_param(ModuleParamId {
            module: ModuleId(0),
            position,
        });
        (var, exp)
    }

    fn app(&self, func: Exp, arg: Exp) -> Exp {
        self.env.arena().alloc(Node::App { func, arg })
    }

    fn prod(&self, var: SymbolId, ty: Exp, body: Exp) -> Exp {
        self.env.arena().alloc(Node::Prod { var, ty, body })
    }

    fn lam(&self, var: SymbolId, ty: Exp, body: Exp) -> Exp {
        self.env.arena().alloc(Node::Lam { var, ty, body })
    }

    fn push(&mut self, name: &str, ty: Exp) -> Exp {
        let var = self.env.intern(name);
        let position = self.context.len() as u32;
        self.env.add_module_parameter(
            ModuleId(0),
            ModuleParameter {
                name: var,
                kind: ModuleParameterKind::Pts { ty },
            },
        );
        let exp = self.env.arena().module_param(ModuleParamId {
            module: ModuleId(0),
            position,
        });
        self.context.push(ContextEntry::Pts { var, ty });
        exp
    }
}

#[test]
fn kernel_expression_formatter_resolves_node_ids() {
    let fixture = Fixture::new();
    let arena = fixture.env.arena();
    let state_ty = arena.bound(0);
    let result_ty = arena.bound(1);
    let step = arena.bound(2);
    let run = arena.alloc(Node::Run {
        state_ty,
        result_ty,
        step,
        initial: arena.bound(0),
    });

    let formatted = format_exp(&fixture.env, run);
    assert!(formatted.starts_with("\\run(#0, #1, #2, "));
    assert!(!formatted.contains("NodeId"));
}

#[test]
fn sort_and_identity_lambda_infer() {
    let mut fixture = Fixture::new();
    let set = fixture.env.arena().sort(Sort::Set(0));
    let set_kind = fixture.env.arena().sort(Sort::SetKind(0));
    assert!(exp_is_alpha_eq(
        &fixture.env,
        CheckSession::new(
            &fixture.env,
            fixture.env.root_module(),
            &mut fixture.context
        )
        .infer(set)
        .unwrap(),
        set_kind,
    ));

    let binder = fixture.env.intern("x");
    let body = fixture.env.arena().bound(0);
    let identity = fixture.lam(binder, set, body);
    let inferred = CheckSession::new(
        &fixture.env,
        fixture.env.root_module(),
        &mut fixture.context,
    )
    .infer(identity)
    .unwrap();
    let expected = fixture.prod(binder, set, set);
    assert!(exp_is_alpha_eq(&fixture.env, inferred, expected));
}

#[test]
fn beta_reduction_stops_at_whnf() {
    let fixture = Fixture::new();
    let set = fixture.env.arena().sort(Sort::Set(0));
    let identity = fixture.lam(SymbolId::ANONYMOUS, set, fixture.env.arena().bound(0));
    let redex = fixture.app(identity, set);
    assert_eq!(whnf(&fixture.env, redex), set);
    assert_eq!(normalize(&fixture.env, redex), set);
    assert!(convertible(&fixture.env, redex, set));
}

#[test]
fn pts_beta_does_not_evaluate_an_unused_argument() {
    let fixture = Fixture::new();
    let arena = fixture.env.arena();
    let set = arena.sort(Sort::Set(0));
    let identity = fixture.lam(SymbolId::ANONYMOUS, set, arena.bound(0));
    let reducible_argument = fixture.app(identity, set);
    let constant = fixture.lam(SymbolId::ANONYMOUS, set, set);
    let application = fixture.app(constant, reducible_argument);

    assert_eq!(reduce_one(&fixture.env, application), Some(set));
}

#[test]
fn pts_beta_substitutes_without_evaluating_the_argument() {
    let fixture = Fixture::new();
    let arena = fixture.env.arena();
    let set = arena.sort(Sort::Set(0));
    let identity = fixture.lam(SymbolId::ANONYMOUS, set, arena.bound(0));
    let reducible_argument = fixture.app(identity, set);
    let duplicated = arena.alloc(Node::RunStep {
        state_ty: arena.bound(0),
        result_ty: arena.bound(0),
    });
    let function = fixture.lam(SymbolId::ANONYMOUS, set, duplicated);

    let result = whnf(&fixture.env, fixture.app(function, reducible_argument));
    let Node::RunStep {
        state_ty,
        result_ty,
    } = arena.get(result)
    else {
        panic!("expected the lambda body");
    };
    assert_eq!(state_ty, reducible_argument);
    assert_eq!(result_ty, reducible_argument);
    assert!(convertible(&fixture.env, state_ty, set));
    assert!(convertible(&fixture.env, result_ty, set));
}

#[test]
fn call_by_value_evaluates_run_step_payloads() {
    let fixture = Fixture::new();
    let arena = fixture.env.arena();
    let set = arena.sort(Sort::Set(0));
    let identity = fixture.lam(SymbolId::ANONYMOUS, set, arena.bound(0));
    let reducible_output = fixture.app(identity, set);
    let finish = arena.alloc(Node::Finish {
        state_ty: set,
        result_ty: set,
        output: reducible_output,
    });

    let result = whnf(&fixture.env, finish);
    let Node::Finish { output, .. } = arena.get(result) else {
        panic!("expected a finish value");
    };
    assert_eq!(output, set);
}

#[test]
fn normalize_reuses_shared_subterm_results_within_one_call() {
    let fixture = Fixture::new();
    let arena = fixture.env.arena();
    let set = arena.sort(Sort::Set(0));
    let identity = fixture.lam(SymbolId::ANONYMOUS, set, arena.bound(0));
    let reducible = fixture.app(identity, set);
    let shared = reducible;
    let root = arena.alloc(Node::RunStep {
        state_ty: shared,
        result_ty: shared,
    });

    let result = normalize(&fixture.env, root);
    let Node::RunStep {
        state_ty,
        result_ty,
    } = arena.get(result)
    else {
        panic!("expected the normalized root");
    };
    assert_eq!(state_ty, set);
    assert_eq!(state_ty, result_ty);
}

#[test]
fn de_bruijn_instantiation_shifts_an_open_argument() {
    let fixture = Fixture::new();
    let set = fixture.env.arena().sort(Sort::Set(0));
    let inner_reference_to_outer = fixture.env.arena().bound(1);
    let body = fixture.lam(SymbolId::ANONYMOUS, set, inner_reference_to_outer);
    let open_argument = fixture.env.arena().bound(0);
    let result = instantiate(fixture.env.arena(), body, open_argument);
    let Node::Lam { body, .. } = fixture.env.arena().get(result) else {
        panic!("expected lambda");
    };
    assert!(matches!(fixture.env.arena().get(body), Node::Bound(1)));
}

#[test]
fn telescope_instantiation_does_not_resubstitute_open_arguments() {
    let fixture = Fixture::new();
    let arena = fixture.env.arena();
    let open = fixture.app(arena.bound(1), arena.bound(0));
    let arguments = [arena.bound(1), arena.bound(0)];

    let result = instantiate_telescope(arena, open, &arguments);
    let Node::App { func, arg } = arena.get(result) else {
        panic!("expected application");
    };
    assert!(matches!(arena.get(func), Node::Bound(1)));
    assert!(matches!(arena.get(arg), Node::Bound(0)));
}

#[test]
fn outer_telescope_instantiation_shifts_arguments_past_inner_binders() {
    let fixture = Fixture::new();
    let arena = fixture.env.arena();
    let open = fixture.app(arena.bound(2), arena.bound(1));
    let arguments = [arena.bound(1), arena.bound(0)];

    let result = instantiate_outer_telescope(arena, open, &arguments, 1);
    let Node::App { func, arg } = arena.get(result) else {
        panic!("expected application");
    };
    assert!(matches!(arena.get(func), Node::Bound(2)));
    assert!(matches!(arena.get(arg), Node::Bound(1)));
}

#[test]
fn substitution_reuses_unchanged_node_ids() {
    let fixture = Fixture::new();
    let (target, target_exp) = fixture.var("target");
    let (_, stable) = fixture.var("stable");
    let application = fixture.app(stable, target_exp);
    let replacement = fixture.env.arena().sort(Sort::Set(0));
    let substituted = exp_subst_module_param(
        fixture.env.arena(),
        application,
        ModuleParamId {
            module: ModuleId(0),
            position: target.index() as u32,
        },
        replacement,
    );
    let Node::App { func, arg } = fixture.env.arena().get(substituted) else {
        panic!("expected application");
    };
    assert_eq!(func, stable);
    assert_eq!(arg, replacement);
}

#[test]
fn alpha_equivalence_ignores_binder_names() {
    let fixture = Fixture::new();
    let set = fixture.env.arena().sort(Sort::Set(0));
    let left = fixture.lam(SymbolId(1), set, fixture.env.arena().bound(0));
    let right = fixture.lam(SymbolId(2), set, fixture.env.arena().bound(0));
    assert!(exp_is_alpha_eq(&fixture.env, left, right));
}

#[test]
fn free_variable_identity_does_not_depend_on_display_name() {
    let fixture = Fixture::new();
    let left = fixture.env.arena().module_param(ModuleParamId {
        module: ModuleId(0),
        position: 100,
    });
    let right = fixture.env.arena().module_param(ModuleParamId {
        module: ModuleId(0),
        position: 101,
    });

    assert!(!exp_is_alpha_eq(&fixture.env, left, right));
}

#[test]
fn named_occurrences_owned_by_binders_are_alpha_equivalent() {
    let fixture = Fixture::new();
    let set = fixture.env.arena().sort(Sort::Set(0));
    let left_var = SymbolId(1);
    let right_var = SymbolId(2);
    let left_body = fixture.env.arena().bound(0);
    let right_body = fixture.env.arena().bound(0);
    let left = fixture.lam(left_var, set, left_body);
    let right = fixture.lam(right_var, set, right_body);

    assert!(exp_is_alpha_eq(&fixture.env, left, right));
}

#[test]
fn application_infers_dependent_result() {
    let mut fixture = Fixture::new();
    let set = fixture.env.arena().sort(Sort::Set(0));
    let argument = fixture.push("A", set);
    let function_ty = fixture.prod(SymbolId::ANONYMOUS, set, fixture.env.arena().bound(0));
    let function = fixture.push("f", function_ty);
    let application = fixture.app(function, argument);
    let inferred = CheckSession::new(
        &fixture.env,
        fixture.env.root_module(),
        &mut fixture.context,
    )
    .infer(application)
    .unwrap();
    assert_eq!(inferred, argument);
}

#[test]
fn refinement_introduction_erases_to_its_element() {
    let mut fixture = Fixture::new();
    let set0 = fixture.env.arena().sort(Sort::Set(0));
    let carrier = fixture.push("A", set0);
    let power = fixture.env.arena().alloc(Node::PowerSet { set: carrier });
    let subset = fixture.push("S", power);
    let element = fixture.push("a", carrier);
    let membership = fixture.env.arena().alloc(Node::Pred {
        superset: carrier,
        subset,
        element,
    });
    let proof = fixture.push("p", membership);
    let intro = fixture.env.arena().alloc(Node::SubsetIntro {
        superset: carrier,
        subset,
        element,
        proof,
    });
    let lifted = fixture.env.arena().alloc(Node::TypeLift {
        superset: carrier,
        subset,
    });
    CheckSession::new(
        &fixture.env,
        fixture.env.root_module(),
        &mut fixture.context,
    )
    .check(intro, lifted)
    .unwrap();
    assert_eq!(erased_normal(&fixture.env, intro), element);
    assert!(erased_convertible(&fixture.env, intro, element));
}

#[test]
fn equality_uses_the_base_refinement_carrier() {
    let mut fixture = Fixture::new();
    let set0 = fixture.env.arena().sort(Sort::Set(0));
    let carrier = fixture.push("A", set0);
    let power = fixture.env.arena().alloc(Node::PowerSet { set: carrier });
    let left_subset = fixture.push("L", power);
    let right_subset = fixture.push("R", power);
    let left_ty = fixture.env.arena().alloc(Node::TypeLift {
        superset: carrier,
        subset: left_subset,
    });
    let right_ty = fixture.env.arena().alloc(Node::TypeLift {
        superset: carrier,
        subset: right_subset,
    });
    let left = fixture.push("left", left_ty);
    let right = fixture.push("right", right_ty);
    let equality = fixture.env.arena().alloc(Node::Equal { left, right });
    assert_eq!(
        CheckSession::new(
            &fixture.env,
            fixture.env.root_module(),
            &mut fixture.context
        )
        .infer_sort(equality)
        .unwrap(),
        Sort::Prop
    );
}

#[test]
fn defined_constants_are_transparent_for_reduction() {
    let mut fixture = Fixture::new();
    let proposition = fixture.env.arena().sort(Sort::Prop);
    let definition = fixture.env.add_definition(
        fixture.env.root_module(),
        crate::environment::DefinedConstant {
            kind: DefinitionKind::Pts,
            ty: proposition,
            body: proposition,
        },
    );
    let defined = fixture.env.arena().alloc(Node::DefinedConstant(definition));
    assert_eq!(whnf(&fixture.env, defined), proposition);
}

#[test]
fn inductive_constructor_and_eliminator_reduce() {
    let mut fixture = Fixture::new();
    let zero = CtorType {
        telescope: vec![],
        indices: vec![],
    };
    let successor = CtorType {
        telescope: vec![CtorBinder::StrictPositive {
            binders: vec![],
            self_indices: vec![],
        }],
        indices: vec![],
    };
    let spec = InductiveTypeSpecs::unchecked(vec![], vec![], Sort::Set(0), vec![zero, successor]);
    let spec = fixture.env.add_inductive(fixture.env.root_module(), spec);
    let nat = fixture.env.arena().alloc(Node::IndType {
        indspec: spec,
        parameters: vec![],
    });
    let zero = fixture.env.arena().alloc(Node::IndCtor {
        indspec: spec,
        parameters: vec![],
        idx: 0,
    });
    assert!(
        CheckSession::new(
            &fixture.env,
            fixture.env.root_module(),
            &mut fixture.context
        )
        .check(zero, nat)
        .is_ok()
    );
}

#[test]
fn inductive_validation_rejects_unclassified_self_reference() {
    let mut fixture = Fixture::new();
    let inductive = fixture.env.reserve_inductive(fixture.env.root_module());
    let this = fixture.env.arena().alloc(Node::IndType {
        indspec: inductive,
        parameters: vec![],
    });
    let spec = InductiveTypeSpecs::unchecked(
        vec![],
        vec![],
        Sort::Set(0),
        vec![CtorType {
            telescope: vec![CtorBinder::Simple((SymbolId::ANONYMOUS, this))],
            indices: vec![],
        }],
    );
    fixture.env.define_inductive(inductive, spec);
    let spec = fixture.env.inductive(inductive).clone();

    assert!(
        spec.validate(
            &mut CheckSession::new(
                &fixture.env,
                fixture.env.root_module(),
                &mut fixture.context,
            ),
            inductive,
        )
        .is_err()
    );
}

#[test]
fn session_restores_context_after_failed_binder_inference() {
    let mut fixture = Fixture::new();
    let set = fixture.env.arena().sort(Sort::Set(0));
    let invalid_body = fixture.env.arena().bound(1);
    let invalid_lambda = fixture.lam(SymbolId::ANONYMOUS, set, invalid_body);
    let mut session = CheckSession::new(
        &fixture.env,
        fixture.env.root_module(),
        &mut fixture.context,
    );
    let initial_len = session.context().len();

    assert!(session.infer(invalid_lambda).is_err());
    assert_eq!(session.context().len(), initial_len);
}

fn program_enum(fixture: &mut Fixture, constructor_count: usize) -> (Exp, Vec<Exp>) {
    let reflected_spec = InductiveTypeSpecs::unchecked(
        vec![],
        vec![],
        Sort::Set(0),
        (0..constructor_count)
            .map(|_| CtorType {
                telescope: vec![],
                indices: vec![],
            })
            .collect(),
    );
    let reflected = fixture
        .env
        .add_inductive(fixture.env.root_module(), reflected_spec);
    let spec = ProgramInductiveTypeSpecs::unchecked(
        vec![],
        (0..constructor_count)
            .map(|_| ProgramConstructorSpec::new(vec![]))
            .collect(),
        reflected,
    );
    let spec = fixture
        .env
        .add_program_inductive(fixture.env.root_module(), spec);
    let ty = fixture.env.arena().alloc(Node::ProgramIndType {
        indspec: spec,
        parameters: vec![],
    });
    let values = (0..constructor_count)
        .map(|idx| {
            fixture.env.arena().alloc(Node::ProgramIndCtor {
                indspec: spec,
                parameters: vec![],
                idx,
                fields: vec![],
            })
        })
        .collect();
    (ty, values)
}

fn terminating_step(fixture: &Fixture, state_ty: Exp, result_ty: Exp, output: Exp) -> Exp {
    let arena = fixture.env.arena();
    let finish = arena.alloc(Node::Finish {
        state_ty: crate::calculus::shift_bound_indices(arena, state_ty, 1, 0),
        result_ty: crate::calculus::shift_bound_indices(arena, result_ty, 1, 0),
        output: crate::calculus::shift_bound_indices(arena, output, 1, 0),
    });
    let returned = arena.alloc(Node::Return { value: finish });
    let function = arena.alloc(Node::ComputationLam {
        var: SymbolId::ANONYMOUS,
        value_ty: state_ty,
        body: returned,
    });
    arena.alloc(Node::Thunk {
        computation: function,
    })
}

#[test]
fn program_run_typechecks_without_a_termination_certificate() {
    let mut fixture = Fixture::new();
    let (state_ty, values) = program_enum(&mut fixture, 1);
    let value = values[0];
    let step = terminating_step(&fixture, state_ty, state_ty, value);
    let run = fixture.env.arena().alloc(Node::Run {
        state_ty,
        result_ty: state_ty,
        step,
        initial: value,
    });
    let inferred = CheckSession::new(
        &fixture.env,
        fixture.env.root_module(),
        &mut fixture.context,
    )
    .infer_computation(run)
    .unwrap();
    let expected = fixture
        .env
        .arena()
        .alloc(Node::ReturnType { value_ty: state_ty });
    assert!(exp_is_alpha_eq(&fixture.env, inferred, expected));
    let returned = fixture.env.arena().alloc(Node::Return { value });
    let crate::calculus::Evaluation::Normal(evaluated) =
        crate::calculus::evaluate_computation(&fixture.env, run)
    else {
        panic!("terminating run exhausted its reduction budget");
    };
    assert!(exp_is_alpha_eq(&fixture.env, evaluated, returned));
}

#[test]
fn set_run_requires_and_checks_explicit_proof_evidence() {
    let mut fixture = Fixture::new();
    let (program_ty, program_values) = program_enum(&mut fixture, 1);
    let arena = fixture.env.arena();
    let state_ty = crate::reflection::reflect_type(&fixture.env, program_ty).unwrap();
    let initial =
        crate::reflection::reflect_term(&fixture.env, ModuleId(0), &Vec::new(), program_values[0])
            .unwrap();
    let finish = arena.alloc(Node::Finish {
        state_ty,
        result_ty: state_ty,
        output: arena.bound(0),
    });
    let step = arena.alloc(Node::Lam {
        var: SymbolId::ANONYMOUS,
        ty: state_ty,
        body: finish,
    });

    let run = arena.alloc(Node::SetRun {
        state_ty,
        result_ty: state_ty,
        step,
        initial,
    });
    assert!(
        CheckSession::new(&fixture.env, ModuleId(0), &mut fixture.context)
            .infer_pts(run)
            .is_err()
    );

    let obligations = RefCell::new(Vec::new());
    let inferred = CheckSession::collecting(
        &fixture.env,
        ModuleId(0),
        &mut fixture.context,
        &obligations,
    )
    .infer_pts(run)
    .unwrap();
    assert!(exp_is_alpha_eq(&fixture.env, inferred, state_ty));
    let obligations = obligations.into_inner();
    assert_eq!(obligations.len(), 1);

    // The environment contains only already-checked declarations in normal
    // operation, so a declared theorem is valid explicit evidence here.
    let theorem = fixture.env.add_definition(
        ModuleId(0),
        DefinedConstant {
            kind: DefinitionKind::Pts,
            ty: obligations[0].proposition,
            body: initial,
        },
    );
    let witness = fixture.env.arena().alloc(Node::DefinedConstant(theorem));
    let evidence = vec![crate::exp::ProofEvidence {
        context: obligations[0].context.clone(),
        proposition: obligations[0].proposition,
        witness,
    }];
    let checked =
        CheckSession::with_evidence(&fixture.env, ModuleId(0), &mut fixture.context, &evidence)
            .infer_pts(run)
            .unwrap();
    assert!(exp_is_alpha_eq(&fixture.env, checked, state_ty));
}

#[test]
fn well_termination_reflects_program_context_but_box_requires_closed_programs() {
    let mut fixture = Fixture::new();
    let (program_ty, _) = program_enum(&mut fixture, 1);
    let parameter_name = fixture.env.intern("programValue");
    fixture.env.add_module_parameter(
        ModuleId(0),
        ModuleParameter {
            name: parameter_name,
            kind: ModuleParameterKind::ProgramValue { ty: program_ty },
        },
    );
    let parameter = arena_module_parameter(&fixture.env, 0);
    fixture.context.push(ContextEntry::ProgramValue {
        var: parameter_name,
        ty: program_ty,
    });

    CheckSession::new(&fixture.env, ModuleId(0), &mut fixture.context)
        .check_well_terminated_value(parameter, program_ty)
        .unwrap();

    let boxed = fixture.env.arena().alloc(Node::BoxProgram {
        program_ty,
        program: parameter,
    });
    assert!(
        CheckSession::new(&fixture.env, ModuleId(0), &mut fixture.context)
            .infer_pts(boxed)
            .is_err()
    );
}

fn arena_module_parameter(env: &CrateEnv, position: u32) -> Exp {
    env.arena().module_param(ModuleParamId {
        module: ModuleId(0),
        position,
    })
}

#[test]
fn divergent_program_run_stops_at_the_requested_fuel_budget() {
    let mut fixture = Fixture::new();
    let (state_ty, values) = program_enum(&mut fixture, 1);
    let arena = fixture.env.arena();
    let continue_forever = arena.alloc(Node::Continue {
        state_ty,
        result_ty: state_ty,
        next: arena.bound(0),
    });
    let step = arena.alloc(Node::Thunk {
        computation: arena.alloc(Node::ComputationLam {
            var: SymbolId::ANONYMOUS,
            value_ty: state_ty,
            body: arena.alloc(Node::Return {
                value: continue_forever,
            }),
        }),
    });
    let run = arena.alloc(Node::Run {
        state_ty,
        result_ty: state_ty,
        step,
        initial: values[0],
    });
    assert!(matches!(
        crate::calculus::evaluate_computation_with_fuel(&fixture.env, run, 16),
        crate::calculus::Evaluation::OutOfFuel(_)
    ));
}

#[test]
fn run_reduces_multiple_transitions_atomically_and_preserves_stuck_terms() {
    let mut fixture = Fixture::new();
    let (state_ty, values) = program_enum(&mut fixture, 2);
    let arena = fixture.env.arena();
    let first = values[0];
    let last = values[1];
    let Node::ProgramIndType { indspec: spec, .. } = arena.get(state_ty) else {
        unreachable!()
    };
    let continue_case = arena.alloc(Node::Continue {
        state_ty,
        result_ty: state_ty,
        next: last,
    });
    let finish_case = arena.alloc(Node::Finish {
        state_ty,
        result_ty: state_ty,
        output: last,
    });
    let body = arena.alloc(Node::ProgramCase {
        indspec: spec,
        scrutinee: arena.bound(0),
        branches: vec![
            ProgramCaseBranch {
                binders: vec![],
                body: arena.alloc(Node::Return {
                    value: continue_case,
                }),
            },
            ProgramCaseBranch {
                binders: vec![],
                body: arena.alloc(Node::Return { value: finish_case }),
            },
        ],
    });
    let step_function = arena.alloc(Node::ComputationLam {
        var: SymbolId::ANONYMOUS,
        value_ty: state_ty,
        body,
    });
    let step = arena.alloc(Node::Thunk {
        computation: step_function,
    });
    let run = arena.alloc(Node::Run {
        state_ty,
        result_ty: state_ty,
        step,
        initial: first,
    });
    let returned = arena.alloc(Node::Return { value: last });
    let crate::calculus::Evaluation::Normal(evaluated) =
        crate::calculus::evaluate_computation(&fixture.env, run)
    else {
        panic!("terminating run exhausted its reduction budget");
    };
    assert!(exp_is_alpha_eq(&fixture.env, evaluated, returned));

    let stuck = arena.alloc(Node::Run {
        state_ty,
        result_ty: state_ty,
        step: arena.bound(0),
        initial: first,
    });
    let crate::calculus::Evaluation::Normal(evaluated_stuck) =
        crate::calculus::evaluate_computation(&fixture.env, stuck)
    else {
        panic!("stuck computation unexpectedly exhausted its reduction budget");
    };
    let Node::RunCase {
        state_ty: found_state,
        result_ty: found_result,
        initial: found_initial,
        ..
    } = arena.get(evaluated_stuck)
    else {
        panic!("{}", format_exp(&fixture.env, evaluated_stuck));
    };
    assert!(exp_is_alpha_eq(&fixture.env, found_state, state_ty));
    assert!(exp_is_alpha_eq(&fixture.env, found_result, state_ty));
    assert!(exp_is_alpha_eq(&fixture.env, found_initial, first));
}

#[test]
fn reflection_maps_non_dependent_arrows_and_applications() {
    let mut fixture = Fixture::new();
    let (compute_ty, values) = program_enum(&mut fixture, 1);
    let value = values[0];
    let arena = fixture.env.arena();
    let returned_ty = arena.alloc(Node::ReturnType {
        value_ty: compute_ty,
    });
    let arrow = arena.alloc(Node::ComputationFunction {
        domain: compute_ty,
        codomain: returned_ty,
    });
    let reflected_arrow = crate::reflection::reflect_type(&fixture.env, arrow).unwrap();
    let reflected_ty = crate::reflection::reflect_type(&fixture.env, compute_ty).unwrap();
    let expected_arrow = fixture.prod(SymbolId::ANONYMOUS, reflected_ty, reflected_ty);
    assert!(exp_is_alpha_eq(
        &fixture.env,
        reflected_arrow,
        expected_arrow,
    ));

    let identity = arena.alloc(Node::ComputationLam {
        var: SymbolId::ANONYMOUS,
        value_ty: compute_ty,
        body: arena.alloc(Node::Return {
            value: arena.bound(0),
        }),
    });
    let reflected_identity =
        crate::reflection::reflect_term(&fixture.env, ModuleId(0), &Vec::new(), identity).unwrap();
    let reflected_value =
        crate::reflection::reflect_term(&fixture.env, ModuleId(0), &Vec::new(), value).unwrap();
    let application = fixture.app(reflected_identity, reflected_value);
    let normalized_application = normalize(&fixture.env, application);
    let normalized_value = normalize(&fixture.env, reflected_value);
    assert!(
        exp_is_alpha_eq(&fixture.env, normalized_application, normalized_value,),
        "application={}, value={}",
        format_exp(&fixture.env, normalized_application),
        format_exp(&fixture.env, normalized_value)
    );
}

#[test]
fn reflection_erases_return_thunk_and_maps_thunked_applications() {
    let mut fixture = Fixture::new();
    let (value_ty, values) = program_enum(&mut fixture, 1);
    let value = values[0];
    let arena = fixture.env.arena();

    let return_ty = arena.alloc(Node::ReturnType { value_ty });
    let thunk_ty = arena.alloc(Node::ThunkType {
        computation_ty: return_ty,
    });
    let returned = arena.alloc(Node::Return { value });
    let thunked = arena.alloc(Node::Thunk {
        computation: returned,
    });
    let reflected_value =
        crate::reflection::reflect_term(&fixture.env, ModuleId(0), &Vec::new(), value).unwrap();

    for reflected_ty in [return_ty, thunk_ty]
        .map(|compute_ty| crate::reflection::reflect_type(&fixture.env, compute_ty).unwrap())
    {
        assert!(exp_is_alpha_eq(
            &fixture.env,
            reflected_ty,
            crate::reflection::reflect_type(&fixture.env, value_ty).unwrap(),
        ));
    }

    let reflected_return =
        crate::reflection::reflect_term(&fixture.env, ModuleId(0), &Vec::new(), returned).unwrap();
    let reflected_thunk =
        crate::reflection::reflect_term(&fixture.env, ModuleId(0), &Vec::new(), thunked).unwrap();
    assert!(exp_is_alpha_eq(
        &fixture.env,
        normalize(&fixture.env, reflected_return),
        normalize(&fixture.env, reflected_value),
    ));
    assert!(exp_is_alpha_eq(
        &fixture.env,
        normalize(&fixture.env, reflected_thunk),
        normalize(&fixture.env, reflected_value),
    ));

    let identity = arena.alloc(Node::ComputationLam {
        var: SymbolId::ANONYMOUS,
        value_ty,
        body: arena.alloc(Node::Return {
            value: arena.bound(0),
        }),
    });
    let thunked_identity = arena.alloc(Node::Thunk {
        computation: identity,
    });
    let reflected_identity =
        crate::reflection::reflect_term(&fixture.env, ModuleId(0), &Vec::new(), thunked_identity)
            .unwrap();
    let application = fixture.app(reflected_identity, reflected_value);
    assert!(exp_is_alpha_eq(
        &fixture.env,
        normalize(&fixture.env, application),
        normalize(&fixture.env, reflected_value),
    ));
}

#[test]
fn continuing_run_preserves_computation_type_at_every_reduction_step() {
    let mut fixture = Fixture::new();
    let (state_ty, values) = program_enum(&mut fixture, 2);
    let arena = fixture.env.arena();
    let first = values[0];
    let last = values[1];
    let Node::ProgramIndType { indspec, .. } = arena.get(state_ty) else {
        unreachable!()
    };

    let step_body = arena.alloc(Node::ProgramCase {
        indspec,
        scrutinee: arena.bound(0),
        branches: vec![
            ProgramCaseBranch {
                binders: vec![],
                body: arena.alloc(Node::Return {
                    value: arena.alloc(Node::Continue {
                        state_ty,
                        result_ty: state_ty,
                        next: last,
                    }),
                }),
            },
            ProgramCaseBranch {
                binders: vec![],
                body: arena.alloc(Node::Return {
                    value: arena.alloc(Node::Finish {
                        state_ty,
                        result_ty: state_ty,
                        output: last,
                    }),
                }),
            },
        ],
    });
    let step = arena.alloc(Node::Thunk {
        computation: arena.alloc(Node::ComputationLam {
            var: SymbolId::ANONYMOUS,
            value_ty: state_ty,
            body: step_body,
        }),
    });
    let arena = fixture.env.arena();
    let mut current = arena.alloc(Node::Run {
        state_ty,
        result_ty: state_ty,
        step,
        initial: first,
    });
    let expected = arena.alloc(Node::ReturnType { value_ty: state_ty });

    for _ in 0..16 {
        let inferred = CheckSession::new(
            &fixture.env,
            fixture.env.root_module(),
            &mut fixture.context,
        )
        .infer_computation(current)
        .unwrap_or_else(|error| {
            panic!(
                "subject reduction failed for {}: {error:?}",
                format_exp(&fixture.env, current)
            )
        });
        assert!(exp_is_alpha_eq(&fixture.env, inferred, expected));

        let Some(next) = crate::calculus::reduce_computation_once(&fixture.env, current) else {
            let Node::Return { value } = arena.get(current) else {
                panic!("run got stuck at {}", format_exp(&fixture.env, current));
            };
            assert_eq!(value, last);
            return;
        };
        current = next;
    }
    panic!("continuing run did not terminate within the expected number of steps");
}
