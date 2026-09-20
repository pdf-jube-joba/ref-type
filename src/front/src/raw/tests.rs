use crate::raw::{
    calculus::{exp_is_alpha_eq, exp_reduce_if_top, instantiate, normalize},
    derivation::CheckSession,
    environment::{CrateEnv, ModuleArgument},
    exp::{ExpContextEntry, ExpNode},
    ids::{DefId, MetaVarId, ModuleParamId, ProgramInductiveId, SymbolId},
    program::{
        ComputationTermNode, ComputationTypeNode, ProgramContextEntry, ValueTermNode, ValueTypeNode,
    },
    program_calculus::{
        Evaluation, evaluate_computation, instantiate_value_type, remap_computation_global_ids,
        remap_value_type_global_ids, shift_computation_indices, shift_value_type_indices,
        strengthen_value_type, subst_computation_module_params, subst_value_type_module_params,
    },
    program_derivation::ProgramCheckSession,
    sort::Sort,
};

#[test]
fn arena_interns_all_node_families() {
    let env = CrateEnv::new();
    let arena = env.arena();
    let set = arena.sort(Sort::Set(0));
    assert_eq!(arena.sort(Sort::Set(0)), set);

    let bound = arena.exp_bound(0);
    assert_eq!(arena.exp_bound(0), bound);
    let application = arena.alloc(ExpNode::App {
        func: bound.clone(),
        arg: set.clone(),
    });
    assert_eq!(
        arena.alloc(ExpNode::App {
            func: bound,
            arg: set,
        }),
        application
    );

    let meta = ExpNode::Meta {
        metavariable: MetaVarId(0),
        spine: vec![application],
    };
    assert_eq!(arena.alloc(meta.clone()), arena.alloc(meta));

    let value_ty = arena.value_type_bound(0);
    assert_eq!(arena.value_type_bound(0), value_ty);
    let computation_ty = arena.alloc(ComputationTypeNode::Return {
        value_ty: value_ty.clone(),
    });
    assert_eq!(
        arena.alloc(ComputationTypeNode::Return { value_ty }),
        computation_ty
    );
    let value = arena.value_bound(0);
    assert_eq!(arena.value_bound(0), value);
    let computation = arena.alloc(ComputationTermNode::Return {
        value: value.clone(),
    });
    assert_eq!(
        arena.alloc(ComputationTermNode::Return { value }),
        computation
    );
}

#[test]
fn namespace_substitution_is_simultaneous_and_capture_avoiding() {
    use crate::raw::calculus::exp_subst_map;
    let env = CrateEnv::new();
    let a = env.arena();
    let p = ModuleParamId {
        module: env.root_module(),
        position: 0,
    };
    let q = ModuleParamId {
        module: env.root_module(),
        position: 1,
    };
    let p_term = a.exp_module_param(p);
    let q_term = a.exp_module_param(q);
    let pair = a.alloc(ExpNode::App {
        func: p_term,
        arg: q_term.clone(),
    });
    let replacement = a.exp_bound(0);
    let replaced = exp_subst_map(a, pair, &[(p, q_term.clone()), (q, replacement.clone())]);
    assert!(
        matches!(a.get(replaced), ExpNode::App { func, arg } if func == q_term && arg == replacement)
    );

    let lambda = a.alloc(ComputationTermNode::Lambda {
        var: SymbolId::ANONYMOUS,
        value_ty: a.value_type_module_param(p),
        body: a.alloc(ComputationTermNode::Return {
            value: a.alloc(ValueTermNode::ModuleParam(q)),
        }),
    });
    let substituted = subst_computation_module_params(
        a,
        lambda,
        &[
            (p, ModuleArgument::ProgramType(a.value_type_bound(0))),
            (q, ModuleArgument::ProgramValue(a.value_bound(0))),
        ],
        &[],
    );
    let ComputationTermNode::Lambda { value_ty, body, .. } = a.get(substituted) else {
        panic!("lambda")
    };
    assert!(matches!(a.get(value_ty), ValueTypeNode::Bound(0)));
    let ComputationTermNode::Return { value } = a.get(body) else {
        panic!("return")
    };
    assert!(matches!(a.get(value), ValueTermNode::Bound(1)));
}

#[test]
fn namespace_substitution_respects_nominal_declaration_telescopes() {
    use crate::raw::inductive::{CtorBinder, CtorType, InductiveTypeSpecs};
    let env = CrateEnv::new();
    let a = env.arena();
    let p = ModuleParamId {
        module: env.root_module(),
        position: 0,
    };
    let parameter = a.exp_module_param(p);
    let spec = InductiveTypeSpecs::unchecked(
        vec![(SymbolId::ANONYMOUS, a.sort(Sort::Set(0)))],
        vec![],
        Sort::Set(0),
        vec![CtorType {
            telescope: vec![
                CtorBinder::Simple((SymbolId::ANONYMOUS, parameter.clone())),
                CtorBinder::Simple((SymbolId::ANONYMOUS, parameter)),
            ],
            indices: vec![],
        }],
    );
    let substituted = spec.instantiate(a, &[(p, a.exp_bound(0))]);
    let ctor = &substituted.constructors()[0];
    let CtorBinder::Simple((_, first)) = &ctor.telescope[0] else {
        panic!("field")
    };
    let CtorBinder::Simple((_, second)) = &ctor.telescope[1] else {
        panic!("field")
    };
    assert!(matches!(a.get(first.clone()), ExpNode::Bound(1)));
    assert!(matches!(a.get(second.clone()), ExpNode::Bound(2)));
}

#[test]
fn conversion_does_not_reduce_alpha_equal_applications() {
    use crate::raw::calculus::{convertible, erased_convertible};

    let env = CrateEnv::new();
    let arena = env.arena();
    // Alpha-equivalent copies of (lambda x. f x x) ?a with distinct binder
    // names. The names keep the hash-consed handles distinct while conversion
    // must still recognize the terms without constructing either reduct.
    let application = |argument, binder| {
        let first = arena.alloc(ExpNode::App {
            func: arena.exp_bound(1),
            arg: arena.exp_bound(0),
        });
        let body = arena.alloc(ExpNode::App {
            func: first,
            arg: arena.exp_bound(0),
        });
        let lambda = arena.alloc(ExpNode::Lam {
            var: SymbolId(binder),
            ty: arena.sort(Sort::Set(0)),
            body,
        });
        arena.alloc(ExpNode::App {
            func: lambda,
            arg: arena.alloc(ExpNode::Meta {
                metavariable: MetaVarId(argument),
                spine: Vec::new(),
            }),
        })
    };
    let left = application(2, 10);
    let right = application(2, 11);
    assert_ne!(left, right);
    let before = arena.exp_len();
    assert!(convertible(&env, left.clone(), right.clone()));
    assert!(erased_convertible(&env, left.clone(), right.clone()));
    let after = arena.exp_len();
    assert_eq!(after, before, "conversion unnecessarily reduced the terms");

    let reduced = normalize(&env, left.clone());
    assert!(convertible(&env, left.clone(), reduced.clone()));
    assert!(erased_convertible(&env, right.clone(), reduced));
    assert!(!convertible(&env, left, application(3, 12)));
    assert!(!erased_convertible(&env, right, application(3, 13)));
}

#[test]
fn boxed_program_types_compare_structurally() {
    let env = CrateEnv::new();
    let arena = env.arena();
    let left_state = arena.alloc(ValueTypeNode::RunStep {
        state_ty: arena.value_type_module_param(crate::raw::ids::ModuleParamId {
            module: env.root_module(),
            position: 0,
        }),
        result_ty: arena.value_type_module_param(crate::raw::ids::ModuleParamId {
            module: env.root_module(),
            position: 1,
        }),
    });
    let right_state = arena.alloc(ValueTypeNode::RunStep {
        state_ty: arena.value_type_module_param(crate::raw::ids::ModuleParamId {
            module: env.root_module(),
            position: 0,
        }),
        result_ty: arena.value_type_module_param(crate::raw::ids::ModuleParamId {
            module: env.root_module(),
            position: 1,
        }),
    });
    assert_eq!(left_state, right_state);
    let left_return = arena.alloc(ComputationTypeNode::Return {
        value_ty: left_state,
    });
    let right_return = arena.alloc(ComputationTypeNode::Return {
        value_ty: right_state,
    });
    let left = arena.alloc(ExpNode::BoxType {
        program_ty: left_return.clone(),
    });
    let right = arena.alloc(ExpNode::BoxType {
        program_ty: right_return.clone(),
    });
    assert!(exp_is_alpha_eq(&env, left, right));

    let output = arena.value_bound(0);
    let program = arena.alloc(ValueTermNode::Finish {
        state_ty: arena.value_type_module_param(crate::raw::ids::ModuleParamId {
            module: env.root_module(),
            position: 0,
        }),
        result_ty: arena.value_type_module_param(crate::raw::ids::ModuleParamId {
            module: env.root_module(),
            position: 1,
        }),
        output,
    });
    let returned = arena.alloc(ComputationTermNode::Return { value: program });
    let boxed = arena.alloc(ExpNode::BoxProgram {
        program_ty: left_return,
        program: returned,
    });
    let forced = arena.alloc(ExpNode::ForceBox {
        program_ty: right_return,
        boxed,
    });
    assert!(matches!(
        exp_reduce_if_top(&env, forced).map(|exp| arena.get(exp)),
        Some(ExpNode::Finish { .. })
    ));
}

#[test]
fn beta_reduction_remains_set_only() {
    let env = CrateEnv::new();
    let arena = env.arena();
    let set = arena.sort(Sort::Set(0));
    let body = arena.exp_bound(0);
    let lambda = arena.alloc(ExpNode::Lam {
        var: SymbolId::ANONYMOUS,
        ty: set.clone(),
        body: body.clone(),
    });
    let application = arena.alloc(ExpNode::App {
        func: lambda,
        arg: set.clone(),
    });
    assert!(exp_is_alpha_eq(
        &env,
        normalize(&env, application),
        set.clone()
    ));
    assert_eq!(instantiate(arena, body, set.clone()), set);
}

#[test]
fn repeated_weak_head_reduction_reuses_the_result() {
    use crate::raw::calculus::whnf;

    let env = CrateEnv::new();
    let arena = env.arena();
    let ty = arena.sort(Sort::Set(0));
    // (lambda x. lambda y. x) a must substitute under y before it can
    // return a lambda. Repeating it should not allocate another copy.
    let inner = arena.alloc(ExpNode::Lam {
        var: SymbolId::ANONYMOUS,
        ty: ty.clone(),
        body: arena.exp_bound(1),
    });
    let function = arena.alloc(ExpNode::Lam {
        var: SymbolId::ANONYMOUS,
        ty,
        body: inner,
    });
    let application = arena.alloc(ExpNode::App {
        func: function.clone(),
        arg: arena.exp_bound(2),
    });
    let reduced = whnf(&env, application.clone());
    let ExpNode::Lam { body, .. } = arena.get(reduced.clone()) else {
        panic!("lambda")
    };
    assert_eq!(arena.get(body), ExpNode::Bound(3));
    let before = arena.exp_len();
    assert_eq!(whnf(&env, application), reduced);
    assert_eq!(arena.exp_len(), before);

    // Reusing the function with a different argument must still substitute it.
    let other = arena.alloc(ExpNode::App {
        func: function,
        arg: arena.exp_bound(4),
    });
    let ExpNode::Lam { body, .. } = arena.get(whnf(&env, other)) else {
        panic!("lambda")
    };
    assert_eq!(arena.get(body), ExpNode::Bound(5));
}

#[test]
fn weak_head_cache_keeps_erasure_separate_from_strict_reduction() {
    use crate::raw::calculus::{convertible, erased_convertible, whnf};
    use crate::raw::exp::Prove;

    let env = CrateEnv::new();
    let arena = env.arena();
    let set = arena.sort(Sort::Set(0));
    let element = arena.exp_bound(0);
    let refined = |proof| {
        arena.alloc(ExpNode::SubsetIntro {
            superset: set.clone(),
            subset: set.clone(),
            element: element.clone(),
            proof,
        })
    };
    let left = refined(arena.alloc(ExpNode::Prove(Prove::IdRefl {
        element: element.clone(),
    })));
    let right = refined(arena.exp_bound(1));

    assert!(erased_convertible(&env, left.clone(), right.clone()));
    assert!(erased_convertible(&env, left.clone(), element.clone()));
    assert_eq!(whnf(&env, left.clone()), left);
    assert_eq!(whnf(&env, right.clone()), right);
    assert!(!convertible(&env, left.clone(), right.clone()));
    assert!(!convertible(&env, left.clone(), element));
    assert!(erased_convertible(&env, left, right));
}

#[test]
fn substitution_preserves_free_variables_under_binders() {
    use crate::raw::calculus::shift_bound_indices;

    let env = CrateEnv::new();
    let arena = env.arena();
    let ty = arena.sort(Sort::Set(0));
    let argument = arena.alloc(ExpNode::App {
        func: arena.exp_bound(0),
        arg: arena.exp_bound(1),
    });
    assert_eq!(shift_bound_indices(arena, argument.clone(), 0, 0), argument);
    assert_eq!(
        instantiate(arena, arena.exp_bound(0), argument.clone()),
        argument
    );

    // In lambda y. x y, replacing x with an open term must still shift
    // its free variables, while y remains bound to the inner lambda.
    let body = arena.alloc(ExpNode::Lam {
        var: SymbolId::ANONYMOUS,
        ty: ty.clone(),
        body: arena.alloc(ExpNode::App {
            func: arena.exp_bound(1),
            arg: arena.exp_bound(0),
        }),
    });
    let expected = arena.alloc(ExpNode::Lam {
        var: SymbolId::ANONYMOUS,
        ty,
        body: arena.alloc(ExpNode::App {
            func: arena.alloc(ExpNode::App {
                func: arena.exp_bound(1),
                arg: arena.exp_bound(2),
            }),
            arg: arena.exp_bound(0),
        }),
    });
    assert!(exp_is_alpha_eq(
        &env,
        instantiate(arena, body, argument),
        expected
    ));
}

#[test]
fn set_and_program_contexts_are_distinct() {
    let env = CrateEnv::new();
    let set = env.arena().sort(Sort::Set(0));
    let mut set_context = vec![ExpContextEntry {
        var: SymbolId(2),
        ty: set,
    }];
    CheckSession::new(&env, env.root_module(), &mut set_context)
        .check_wellformed_context()
        .unwrap();

    let value_ty = env.arena().alloc(ValueTypeNode::Bound(0));
    let mut program_context = vec![ProgramContextEntry::ValueType { var: SymbolId(3) }];
    ProgramCheckSession::new(&env, &mut program_context)
        .check_value_type(value_ty)
        .unwrap();
}

#[test]
fn program_typing_and_evaluation_use_program_handles() {
    let env = CrateEnv::new();
    let arena = env.arena();
    let value = arena.value_bound(0);
    let returned = arena.alloc(ComputationTermNode::Return { value });
    assert_eq!(
        evaluate_computation(&env, returned.clone()),
        Evaluation::Normal(returned)
    );
}

#[test]
fn program_case_preserves_field_order_and_fuel_boundary() {
    use crate::raw::program::ProgramCaseBranch;
    use crate::raw::program_calculus::{evaluate_computation_with_fuel, value_is_alpha_eq};

    let env = CrateEnv::new();
    let arena = env.arena();
    let indspec = ProgramInductiveId {
        module: env.root_module(),
        index: 0,
    };
    let fields: Vec<_> = (0..2)
        .map(|position| {
            arena.alloc(ValueTermNode::ModuleParam(ModuleParamId {
                module: env.root_module(),
                position,
            }))
        })
        .collect();
    let pair = |fields| {
        arena.alloc(ValueTermNode::InductiveConstructor {
            indspec,
            parameters: vec![],
            idx: 1,
            fields,
        })
    };
    let scrutinee = pair(fields);
    let body = arena.alloc(ComputationTermNode::Return {
        value: pair(vec![arena.value_bound(1), arena.value_bound(0)]),
    });
    let case = arena.alloc(ComputationTermNode::Case {
        indspec,
        scrutinee: scrutinee.clone(),
        branches: vec![
            ProgramCaseBranch {
                binders: vec![],
                body: arena.alloc(ComputationTermNode::Force {
                    value: arena.value_bound(0),
                }),
            },
            ProgramCaseBranch {
                binders: vec![SymbolId::ANONYMOUS; 2],
                body,
            },
        ],
    });
    assert_eq!(
        evaluate_computation_with_fuel(&env, case.clone(), 0),
        Evaluation::OutOfFuel(case.clone())
    );
    for fuel in [1, 2] {
        let Evaluation::Normal(result) = evaluate_computation_with_fuel(&env, case.clone(), fuel)
        else {
            panic!("case should finish in one step");
        };
        let ComputationTermNode::Return { value } = arena.get(result.clone()) else {
            panic!("selected the wrong branch");
        };
        assert!(value_is_alpha_eq(arena, value, scrutinee.clone()));
        assert_eq!(
            evaluate_computation_with_fuel(&env, result.clone(), 0),
            Evaluation::Normal(result)
        );
    }
}

#[test]
fn program_run_stores_accessibility_proof() {
    let env = CrateEnv::new();
    let arena = env.arena();
    let state_ty = arena.alloc(ValueTypeNode::Bound(0));
    let step = arena.alloc(ValueTermNode::Bound(0));
    let initial = arena.alloc(ValueTermNode::Bound(1));
    let run = arena.alloc(ComputationTermNode::Run {
        state_ty: state_ty.clone(),
        result_ty: state_ty,
        step,
        initial,
        accessibility: arena.exp_bound(2),
    });
    let ComputationTermNode::Run { accessibility, .. } = arena.get(run) else {
        panic!()
    };
    assert_eq!(arena.get(accessibility), ExpNode::Bound(2));
}

#[test]
fn run_case_proofs_follow_type_and_value_substitution() {
    use crate::raw::{
        exp::Prove, program_calculus::instantiate_value_in_computation, program_definitions,
    };
    let env = CrateEnv::new();
    let arena = env.arena();
    // The body is under A, x. Its proof mentions both binders.
    let state_ty = arena.value_type_bound(1);
    let initial = arena.value_bound(0);
    let proof = arena.alloc(ExpNode::Lam {
        var: SymbolId::ANONYMOUS,
        ty: arena.exp_bound(1),
        body: arena.alloc(ExpNode::Prove(Prove::IdRefl {
            element: arena.exp_bound(1),
        })),
    });
    let body = arena.alloc(ComputationTermNode::RunCase {
        state_ty: state_ty.clone(),
        result_ty: state_ty,
        step: initial.clone(),
        initial: initial.clone(),
        transition: arena.alloc(ComputationTermNode::Return { value: initial }),
        accessibility: proof.clone(),
        transition_equality: proof,
    });
    let instantiated =
        program_definitions::instantiate_computation(&env, body, &[arena.value_type_bound(2)], 1);
    let ComputationTermNode::RunCase {
        accessibility,
        transition_equality,
        state_ty,
        ..
    } = arena.get(instantiated.clone())
    else {
        panic!()
    };
    assert_eq!(arena.get(state_ty), ValueTypeNode::Bound(3));
    assert!(exp_is_alpha_eq(
        &env,
        accessibility.clone(),
        transition_equality
    ));
    let ExpNode::Lam { ty, body, .. } = arena.get(accessibility) else {
        panic!()
    };
    assert_eq!(arena.get(ty), ExpNode::Bound(3));
    assert!(
        matches!(arena.get(body), ExpNode::Prove(Prove::IdRefl { element }) if arena.get(element.clone()
) == ExpNode::Bound(1))
    );

    let instantiated = instantiate_value_in_computation(&env, instantiated, arena.value_bound(4));
    let ComputationTermNode::RunCase {
        accessibility,
        transition_equality,
        state_ty,
        ..
    } = arena.get(instantiated)
    else {
        panic!()
    };
    assert_eq!(arena.get(state_ty), ValueTypeNode::Bound(2));
    assert!(exp_is_alpha_eq(
        &env,
        accessibility.clone(),
        transition_equality
    ));
    let ExpNode::Lam { ty, body, .. } = arena.get(accessibility) else {
        panic!()
    };
    assert_eq!(arena.get(ty), ExpNode::Bound(2));
    assert!(
        matches!(arena.get(body), ExpNode::Prove(Prove::IdRefl { element }) if arena.get(element.clone()
) == ExpNode::Bound(5))
    );
}

#[test]
fn unchanged_program_transforms_reuse_arena_handles() {
    let env = CrateEnv::new();
    let arena = env.arena();
    let parameter_id = ModuleParamId {
        module: env.root_module(),
        position: 0,
    };
    let parameter = arena.value_type_module_param(parameter_id);
    let returned = arena.alloc(crate::raw::program::ComputationTypeNode::Return {
        value_ty: parameter.clone(),
    });
    let thunk = arena.alloc(ValueTypeNode::Thunk {
        computation_ty: returned,
    });
    let inductive_remapping = std::collections::HashMap::from([(
        ProgramInductiveId {
            module: env.root_module(),
            index: 10,
        },
        ProgramInductiveId {
            module: env.root_module(),
            index: 11,
        },
    )]);
    let unrelated_parameter = ModuleParamId {
        module: env.root_module(),
        position: 1,
    };
    let substitutions = [(
        unrelated_parameter,
        ModuleArgument::ProgramType(parameter.clone()),
    )];

    assert_eq!(shift_value_type_indices(arena, thunk.clone(), 1, 0), thunk);
    assert_eq!(
        instantiate_value_type(arena, thunk.clone(), parameter, 0),
        thunk
    );
    assert_eq!(
        remap_value_type_global_ids(
            arena,
            thunk.clone(),
            &Default::default(),
            &inductive_remapping
        ),
        thunk
    );
    assert_eq!(
        subst_value_type_module_params(arena, thunk.clone(), &substitutions),
        thunk
    );
    assert_eq!(strengthen_value_type(arena, thunk.clone(), 0), Some(thunk));

    let value = arena.alloc(ValueTermNode::ModuleParam(parameter_id));
    let computation = arena.alloc(ComputationTermNode::Return { value });
    let definition_remapping = std::collections::HashMap::from([(
        DefId {
            module: env.root_module(),
            index: 10,
        },
        DefId {
            module: env.root_module(),
            index: 11,
        },
    )]);
    assert_eq!(
        shift_computation_indices(arena, computation.clone(), 1, 0),
        computation
    );
    assert_eq!(
        remap_computation_global_ids(
            arena,
            computation.clone(),
            &definition_remapping,
            &inductive_remapping,
            &Default::default()
        ),
        computation
    );
    assert_eq!(
        subst_computation_module_params(arena, computation.clone(), &substitutions, &[]),
        computation
    );
}

#[test]
fn strengthening_rejects_a_dependent_program_type() {
    let env = CrateEnv::new();
    let arena = env.arena();
    let dependent = arena.value_type_bound(0);
    assert_eq!(strengthen_value_type(arena, dependent, 0), None);

    let outer = arena.value_type_bound(1);
    let strengthened = strengthen_value_type(arena, outer, 0).unwrap();
    assert!(matches!(arena.get(strengthened), ValueTypeNode::Bound(0)));
}

#[test]
fn value_let_checks_its_annotation_and_reflects_open_terms() {
    use crate::raw::program::ComputationTypeNode;
    let env = CrateEnv::new();
    let arena = env.arena();
    // A: VType, a: A. The annotation is outside the new let binder.
    let mut context = vec![
        ProgramContextEntry::ValueType { var: SymbolId(0) },
        ProgramContextEntry::ValueTerm {
            var: SymbolId(1),
            ty: arena.value_type_bound(0),
        },
    ];
    let value = arena.value_bound(0);
    let body = arena.alloc(ComputationTermNode::Return {
        value: value.clone(),
    });
    let make_let = |value_ty| {
        arena.alloc(ComputationTermNode::ValueLet {
            var: SymbolId(2),
            value_ty,
            value: value.clone(),
            body: body.clone(),
        })
    };
    let term = make_let(arena.value_type_bound(1));
    let inferred = ProgramCheckSession::new(&env, &mut context)
        .infer_computation_term(term.clone())
        .unwrap();
    let ComputationTypeNode::Return { value_ty } = arena.get(inferred.clone()) else {
        panic!()
    };
    assert_eq!(arena.get(value_ty), ValueTypeNode::Bound(1));
    let wrong = arena.alloc(ValueTypeNode::Thunk {
        computation_ty: inferred.clone(),
    });
    for annotation in [arena.value_type_bound(0), wrong] {
        assert!(
            ProgramCheckSession::new(&env, &mut context)
                .infer_computation_term(make_let(annotation))
                .is_err()
        );
        assert_eq!(context.len(), 2);
    }

    let reflected = crate::raw::reflection::reflect_computation(&env, term).unwrap();
    let ExpNode::App { func, arg } = arena.get(reflected.clone()) else {
        panic!()
    };
    assert_eq!(arena.get(arg), ExpNode::Bound(0));
    let ExpNode::Lam { ty, body, .. } = arena.get(func) else {
        panic!()
    };
    assert_eq!(arena.get(ty), ExpNode::Bound(1));
    assert_eq!(arena.get(body), ExpNode::Bound(0));
    let mut reflected_context = crate::raw::reflection::reflect_context(&env, &context).unwrap();
    CheckSession::new(&env, env.root_module(), &mut reflected_context)
        .check_pts(
            reflected,
            crate::raw::reflection::reflect_computation_type(&env, inferred).unwrap(),
        )
        .unwrap();
}

#[test]
fn value_let_annotations_follow_binder_shifts_and_substitution() {
    use crate::raw::program_calculus::{computation_is_alpha_eq, instantiate_value_in_computation};
    let env = CrateEnv::new();
    let arena = env.arena();
    // In A: VType, a: A, bind x = a and then y = x.
    let inner = arena.alloc(ComputationTermNode::ValueLet {
        var: SymbolId(3),
        value_ty: arena.value_type_bound(2),
        value: arena.value_bound(0),
        body: arena.alloc(ComputationTermNode::Return {
            value: arena.value_bound(0),
        }),
    });
    let outer = arena.alloc(ComputationTermNode::ValueLet {
        var: SymbolId(2),
        value_ty: arena.value_type_bound(1),
        value: arena.value_bound(0),
        body: inner.clone(),
    });
    let shifted = shift_computation_indices(arena, outer.clone(), 1, 0);
    let ComputationTermNode::ValueLet {
        value_ty,
        value,
        body,
        ..
    } = arena.get(shifted.clone())
    else {
        panic!()
    };
    assert_eq!(arena.get(value_ty), ValueTypeNode::Bound(2));
    assert_eq!(arena.get(value), ValueTermNode::Bound(1));
    let ComputationTermNode::ValueLet {
        value_ty, value, ..
    } = arena.get(body)
    else {
        panic!()
    };
    assert_eq!(arena.get(value_ty), ValueTypeNode::Bound(3));
    assert_eq!(arena.get(value), ValueTermNode::Bound(0));

    let substituted = instantiate_value_in_computation(&env, inner.clone(), arena.value_bound(0));
    let ComputationTermNode::ValueLet { value_ty, .. } = arena.get(substituted) else {
        panic!()
    };
    assert_eq!(arena.get(value_ty), ValueTypeNode::Bound(1));
    let Evaluation::Normal(normal) = evaluate_computation(&env, outer.clone()) else {
        panic!()
    };
    let ComputationTermNode::Return { value } = arena.get(normal) else {
        panic!()
    };
    assert_eq!(arena.get(value), ValueTermNode::Bound(0));
    let renamed = arena.alloc(ComputationTermNode::ValueLet {
        var: SymbolId(99),
        value_ty: arena.value_type_bound(1),
        value: arena.value_bound(0),
        body: inner.clone(),
    });
    assert!(computation_is_alpha_eq(arena, outer.clone(), renamed));
    assert!(!computation_is_alpha_eq(arena, outer.clone(), shifted));
    let different_annotation = arena.alloc(ComputationTermNode::ValueLet {
        var: SymbolId(2),
        value_ty: arena.value_type_bound(2),
        value: arena.value_bound(0),
        body: inner,
    });
    assert!(!computation_is_alpha_eq(arena, outer, different_annotation));
}

#[test]
fn value_let_annotations_follow_module_instantiation() {
    let env = CrateEnv::new();
    let arena = env.arena();
    let parameter = ModuleParamId {
        module: env.root_module(),
        position: 0,
    };
    let old = ProgramInductiveId {
        module: env.root_module(),
        index: 0,
    };
    let new = ProgramInductiveId {
        module: env.root_module(),
        index: 1,
    };
    let body = arena.alloc(ComputationTermNode::Return {
        value: arena.value_bound(0),
    });
    let term = arena.alloc(ComputationTermNode::ValueLet {
        var: SymbolId(0),
        value_ty: arena.value_type_module_param(parameter),
        value: arena.value_bound(0),
        body,
    });
    let datatype = arena.alloc(ValueTypeNode::Inductive {
        indspec: old,
        parameters: vec![],
    });
    let instantiated = subst_computation_module_params(
        arena,
        term,
        &[(parameter, ModuleArgument::ProgramType(datatype.clone()))],
        &[],
    );
    let ComputationTermNode::ValueLet { value_ty, .. } = arena.get(instantiated.clone()) else {
        panic!()
    };
    assert_eq!(value_ty, datatype);
    let remapped = remap_computation_global_ids(
        arena,
        instantiated,
        &Default::default(),
        &std::collections::HashMap::from([(old, new)]),
        &Default::default(),
    );
    let ComputationTermNode::ValueLet { value_ty, .. } = arena.get(remapped) else {
        panic!()
    };
    assert_eq!(
        arena.get(value_ty),
        ValueTypeNode::Inductive {
            indspec: new,
            parameters: vec![]
        }
    );
}

#[test]
fn value_let_reflection_preserves_certificates_and_rejects_unsolved_annotations() {
    use crate::raw::{
        ids::MetaVarId,
        reflection::{ReflectionError, reflect_computation},
    };
    let env = CrateEnv::new();
    let arena = env.arena();
    let ty = arena.value_type_bound(1);
    let value = arena.value_bound(0);
    let accessibility = arena.exp_bound(0);
    let run = arena.alloc(ComputationTermNode::Run {
        state_ty: ty.clone(),
        result_ty: ty.clone(),
        step: value.clone(),
        initial: value.clone(),
        accessibility: accessibility.clone(),
    });
    let term = arena.alloc(ComputationTermNode::ValueLet {
        var: SymbolId(0),
        value_ty: ty,
        value: value.clone(),
        body: run,
    });
    let reflected = reflect_computation(&env, term).unwrap();
    let ExpNode::App { func, .. } = arena.get(reflected) else {
        panic!()
    };
    let ExpNode::Lam { body, .. } = arena.get(func) else {
        panic!()
    };
    assert!(
        matches!(arena.get(body), ExpNode::SetRun { accessibility: proof, .. } if proof == accessibility)
    );
    let meta = arena.alloc(ValueTypeNode::Meta {
        metavariable: MetaVarId(0),
        spine: vec![],
    });
    let term = arena.alloc(ComputationTermNode::ValueLet {
        var: SymbolId(0),
        value_ty: meta,
        value: value.clone(),
        body: arena.alloc(ComputationTermNode::Return { value }),
    });
    assert_eq!(
        reflect_computation(&env, term),
        Err(ReflectionError::UnresolvedMetavariable)
    );
}

#[test]
fn set_recursion_rejects_mixed_or_non_set_sorts() {
    for (state_sort, result_sort) in [
        (Sort::Set(0), Sort::Set(1)),
        (Sort::Set(2), Sort::Set(0)),
        (Sort::Prop, Sort::Prop),
        (Sort::SetKind(0), Sort::SetKind(0)),
    ] {
        let env = CrateEnv::new();
        let arena = env.arena();
        let mut context = vec![
            ExpContextEntry {
                var: SymbolId(0),
                ty: arena.sort(state_sort),
            },
            ExpContextEntry {
                var: SymbolId(1),
                ty: arena.sort(result_sort),
            },
        ];
        let state_ty = arena.exp_bound(1);
        let result_ty = arena.exp_bound(0);
        // The signature must be rejected before checking any term arguments.
        let argument = arena.exp_bound(2);
        let terms = [
            ExpNode::RunStep {
                state_ty: state_ty.clone(),
                result_ty: result_ty.clone(),
            },
            ExpNode::Continue {
                state_ty: state_ty.clone(),
                result_ty: result_ty.clone(),
                next: argument.clone(),
            },
            ExpNode::Finish {
                state_ty: state_ty.clone(),
                result_ty: result_ty.clone(),
                output: argument.clone(),
            },
            ExpNode::Acc {
                state_ty: state_ty.clone(),
                result_ty: result_ty.clone(),
                step: argument.clone(),
                state: argument.clone(),
            },
            ExpNode::SetRun {
                state_ty: state_ty.clone(),
                result_ty: result_ty.clone(),
                step: argument.clone(),
                initial: argument.clone(),
                accessibility: argument.clone(),
            },
            ExpNode::SetRunCase {
                state_ty: state_ty.clone(),
                result_ty: result_ty.clone(),
                step: argument.clone(),
                initial: argument.clone(),
                transition: argument.clone(),
                accessibility: argument.clone(),
                transition_equality: argument.clone(),
            },
            ExpNode::RunStepRec {
                state_ty: state_ty.clone(),
                result_ty: result_ty.clone(),
                motive: argument.clone(),
                on_continue: argument.clone(),
                on_finish: argument.clone(),
                scrutinee: argument.clone(),
            },
            ExpNode::Prove(crate::raw::exp::Prove::AccIntro {
                state_ty: state_ty.clone(),
                result_ty: result_ty.clone(),
                step: argument.clone(),
                state: argument.clone(),
                predecessors: argument.clone(),
            }),
            ExpNode::Prove(crate::raw::exp::Prove::AccDescent {
                state_ty,
                result_ty,
                step: argument.clone(),
                from: argument.clone(),
                to: argument.clone(),
                accessibility: argument.clone(),
                transition: argument,
            }),
        ];
        let mut session = CheckSession::new(&env, env.root_module(), &mut context);
        for term in terms {
            let error = session.infer_pts(arena.alloc(term)).unwrap_err();
            assert!(
                format!("{error:?}").contains("must inhabit the same Set(i)"),
                "{error:?}"
            );
        }
    }
}

#[test]
fn definition_registration_rejects_unchecked_terms_without_inserting_them() {
    use crate::raw::{environment::DefinedConstant, ids::MetaVarId};
    let mut env = CrateEnv::new();
    let module = env.root_module();
    let set = env.arena().sort(Sort::Set(0));
    let kind = env.arena().sort(Sort::SetKind(0));
    let prop = env.arena().sort(Sort::Prop);
    assert!(
        env.add_definition(
            module,
            DefinedConstant::Pts {
                ty: prop,
                body: set.clone()
            }
        )
        .is_err()
    );
    let meta = env.arena().alloc(ExpNode::Meta {
        metavariable: MetaVarId(0),
        spine: vec![],
    });
    assert!(
        env.add_definition(
            module,
            DefinedConstant::Pts {
                ty: set.clone(),
                body: meta
            }
        )
        .is_err()
    );
    let bound = env.arena().exp_bound(0);
    assert!(
        env.add_definition(
            module,
            DefinedConstant::Pts {
                ty: set.clone(),
                body: bound
            }
        )
        .is_err()
    );
    let valid = env
        .add_definition(
            module,
            DefinedConstant::Pts {
                ty: kind,
                body: set,
            },
        )
        .unwrap();
    assert_eq!(
        valid.index, 0,
        "rejected definitions must not consume a slot"
    );
}

#[test]
fn program_registration_checks_body() {
    use crate::raw::environment::{DefinedConstant, ModuleParameter, ModuleParameterKind};
    let mut env = CrateEnv::new();
    let module = env.root_module();
    let a = env.intern("A");
    env.add_module_parameter(
        module,
        ModuleParameter {
            name: a,
            kind: ModuleParameterKind::ProgramType,
        },
    );
    let ty = env.arena().value_type_module_param(ModuleParamId {
        module,
        position: 0,
    });
    let v = env.intern("v");
    env.add_module_parameter(
        module,
        ModuleParameter {
            name: v,
            kind: ModuleParameterKind::ProgramValue { ty: ty.clone() },
        },
    );
    let body = env.arena().alloc(ValueTermNode::ModuleParam(ModuleParamId {
        module,
        position: 1,
    }));
    let bad_body = env.arena().value_bound(0);
    assert!(
        env.add_definition(
            module,
            DefinedConstant::ProgramValue {
                ty: ty.clone(),
                body: bad_body
            }
        )
        .is_err()
    );
    let id = env
        .add_definition(
            module,
            DefinedConstant::ProgramValue {
                ty: ty.clone(),
                body: body.clone(),
            },
        )
        .unwrap();
    assert_eq!(id.index, 0);
    let computation_ty = env
        .arena()
        .alloc(crate::raw::program::ComputationTypeNode::Return { value_ty: ty });
    let computation = env
        .arena()
        .alloc(ComputationTermNode::Return { value: body });
    assert!(
        env.add_definition(
            module,
            DefinedConstant::ProgramComputation {
                ty: computation_ty,
                body: computation,
            }
        )
        .is_ok()
    );
}

#[test]
fn instance_context_must_be_well_formed() {
    let mut env = CrateEnv::new();
    let module = env.root_module();
    let bound = env.arena().exp_bound(0);
    assert!(
        env.add_module_in_scope(
            module,
            vec![ExpContextEntry {
                var: SymbolId::ANONYMOUS,
                ty: bound,
            }]
        )
        .is_err()
    );
}
