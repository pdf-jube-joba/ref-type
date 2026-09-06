use crate::{
    calculus::{exp_is_alpha_eq, exp_reduce_if_top, instantiate, normalize},
    derivation::CheckSession,
    environment::{CrateEnv, ModuleArgument},
    exp::{ExpContextEntry, ExpNode},
    ids::{DefId, ModuleParamId, ProgramInductiveId, SymbolId},
    program::{
        ComputationNode, Program, ProgramContextEntry, ProgramType, ValueNode, ValueTypeNode,
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
fn conversion_does_not_reduce_alpha_equal_applications() {
    use crate::calculus::{convertible, erased_convertible};

    let env = CrateEnv::new();
    let arena = env.arena();
    // Independently allocated copies of (lambda x. f x x) a. Reducing this
    // application allocates substituted application nodes; alpha comparison
    // should recognize the copies without constructing either reduct.
    let application = |argument| {
        let first = arena.alloc(ExpNode::App {
            func: arena.exp_bound(1),
            arg: arena.exp_bound(0),
        });
        let body = arena.alloc(ExpNode::App {
            func: first,
            arg: arena.exp_bound(0),
        });
        let lambda = arena.alloc(ExpNode::Lam {
            var: SymbolId::ANONYMOUS,
            ty: arena.sort(Sort::Set(0)),
            body,
        });
        arena.alloc(ExpNode::App {
            func: lambda,
            arg: arena.exp_bound(argument),
        })
    };
    let left = application(2);
    let right = application(2);
    assert_ne!(left, right);
    let before = arena.exp_bound(99).index();
    assert!(convertible(&env, left, right));
    assert!(erased_convertible(&env, left, right));
    let after = arena.exp_bound(99).index();
    assert_eq!(
        after,
        before + 1,
        "conversion unnecessarily reduced the terms"
    );

    let reduced = normalize(&env, left);
    assert!(convertible(&env, left, reduced));
    assert!(erased_convertible(&env, right, reduced));
    assert!(!convertible(&env, left, application(3)));
    assert!(!erased_convertible(&env, right, application(3)));
}

#[test]
fn boxed_program_types_compare_structurally() {
    let env = CrateEnv::new();
    let arena = env.arena();
    let left_state = arena.alloc(ValueTypeNode::RunStep {
        state_ty: arena.value_type_module_param(crate::ids::ModuleParamId {
            module: env.root_module(),
            position: 0,
        }),
        result_ty: arena.value_type_module_param(crate::ids::ModuleParamId {
            module: env.root_module(),
            position: 1,
        }),
    });
    let right_state = arena.alloc(ValueTypeNode::RunStep {
        state_ty: arena.value_type_module_param(crate::ids::ModuleParamId {
            module: env.root_module(),
            position: 0,
        }),
        result_ty: arena.value_type_module_param(crate::ids::ModuleParamId {
            module: env.root_module(),
            position: 1,
        }),
    });
    assert_ne!(left_state, right_state);
    let left = arena.alloc(ExpNode::BoxType {
        program_ty: ProgramType::Value(left_state),
    });
    let right = arena.alloc(ExpNode::BoxType {
        program_ty: ProgramType::Value(right_state),
    });
    assert!(exp_is_alpha_eq(&env, left, right));

    let output = arena.value_bound(0);
    let program = arena.alloc(ValueNode::Finish {
        state_ty: arena.value_type_module_param(crate::ids::ModuleParamId {
            module: env.root_module(),
            position: 0,
        }),
        result_ty: arena.value_type_module_param(crate::ids::ModuleParamId {
            module: env.root_module(),
            position: 1,
        }),
        output,
    });
    let certified_reflection = crate::reflection::reflect_value(&env, program)
        .expect("run-free Program values reflect without a certificate");
    let boxed = arena.alloc(ExpNode::BoxProgram {
        program_ty: ProgramType::Value(left_state),
        program: Program::Value(program),
        certified_reflection,
    });
    let forced = arena.alloc(ExpNode::ForceBox {
        program_ty: ProgramType::Value(right_state),
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
        ty: set,
        body,
    });
    let application = arena.alloc(ExpNode::App {
        func: lambda,
        arg: set,
    });
    assert!(exp_is_alpha_eq(&env, normalize(&env, application), set));
    assert_eq!(instantiate(arena, body, set), set);
}

#[test]
fn substitution_preserves_free_variables_under_binders() {
    use crate::calculus::shift_bound_indices;

    let env = CrateEnv::new();
    let arena = env.arena();
    let ty = arena.sort(Sort::Set(0));
    let argument = arena.alloc(ExpNode::App {
        func: arena.exp_bound(0),
        arg: arena.exp_bound(1),
    });
    assert_eq!(shift_bound_indices(arena, argument, 0, 0), argument);
    assert_eq!(instantiate(arena, arena.exp_bound(0), argument), argument);

    // In lambda y. x y, replacing x with an open term must still shift
    // its free variables, while y remains bound to the inner lambda.
    let body = arena.alloc(ExpNode::Lam {
        var: SymbolId::ANONYMOUS,
        ty,
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
    let mut program_context = vec![ProgramContextEntry::Type { var: SymbolId(3) }];
    ProgramCheckSession::new(&env, &mut program_context)
        .check_value_type(value_ty)
        .unwrap();
}

#[test]
fn program_typing_and_evaluation_use_program_handles() {
    let env = CrateEnv::new();
    let arena = env.arena();
    let value = arena.value_bound(0);
    let returned = arena.alloc(ComputationNode::Return { value });
    assert_eq!(
        evaluate_computation(&env, returned),
        Evaluation::Normal(returned)
    );
}

#[test]
fn program_case_preserves_field_order_and_fuel_boundary() {
    use crate::program::ProgramCaseBranch;
    use crate::program_calculus::{evaluate_computation_with_fuel, value_is_alpha_eq};

    let env = CrateEnv::new();
    let arena = env.arena();
    let indspec = ProgramInductiveId {
        module: env.root_module(),
        index: 0,
    };
    let fields: Vec<_> = (0..2)
        .map(|position| {
            arena.alloc(ValueNode::ModuleParam(ModuleParamId {
                module: env.root_module(),
                position,
            }))
        })
        .collect();
    let pair = |fields| {
        arena.alloc(ValueNode::InductiveConstructor {
            indspec,
            parameters: vec![],
            idx: 1,
            fields,
        })
    };
    let scrutinee = pair(fields);
    let body = arena.alloc(ComputationNode::Return {
        value: pair(vec![arena.value_bound(1), arena.value_bound(0)]),
    });
    let case = arena.alloc(ComputationNode::Case {
        indspec,
        scrutinee,
        branches: vec![
            ProgramCaseBranch {
                binders: vec![],
                body: arena.alloc(ComputationNode::Force {
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
        evaluate_computation_with_fuel(&env, case, 0),
        Evaluation::OutOfFuel(case)
    );
    for fuel in [1, 2] {
        let Evaluation::Normal(result) = evaluate_computation_with_fuel(&env, case, fuel) else {
            panic!("case should finish in one step");
        };
        let ComputationNode::Return { value } = arena.get(result) else {
            panic!("selected the wrong branch");
        };
        assert!(value_is_alpha_eq(arena, value, scrutinee));
        assert_eq!(
            evaluate_computation_with_fuel(&env, result, 0),
            Evaluation::Normal(result)
        );
    }
}

#[test]
fn program_run_has_no_set_exp_node() {
    let env = CrateEnv::new();
    let arena = env.arena();
    let state_ty = arena.alloc(ValueTypeNode::Bound(0));
    let step = arena.alloc(ValueNode::Bound(0));
    let initial = arena.alloc(ValueNode::Bound(1));
    let run = arena.alloc(ComputationNode::Run {
        state_ty,
        result_ty: state_ty,
        step,
        initial,
    });
    assert!(matches!(arena.get(run), ComputationNode::Run { .. }));
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
    let returned = arena.alloc(crate::program::ComputationTypeNode::Return {
        value_ty: parameter,
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
    let substitutions = [(unrelated_parameter, ModuleArgument::ProgramType(parameter))];

    assert_eq!(shift_value_type_indices(arena, thunk, 1, 0), thunk);
    assert_eq!(instantiate_value_type(arena, thunk, parameter, 0), thunk);
    assert_eq!(
        remap_value_type_global_ids(arena, thunk, &Default::default(), &inductive_remapping),
        thunk
    );
    assert_eq!(
        subst_value_type_module_params(arena, thunk, &substitutions),
        thunk
    );
    assert_eq!(strengthen_value_type(arena, thunk, 0), Some(thunk));

    let value = arena.alloc(ValueNode::ModuleParam(parameter_id));
    let computation = arena.alloc(ComputationNode::Return { value });
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
        shift_computation_indices(arena, computation, 1, 0),
        computation
    );
    assert_eq!(
        remap_computation_global_ids(
            arena,
            computation,
            &definition_remapping,
            &inductive_remapping,
        ),
        computation
    );
    assert_eq!(
        subst_computation_module_params(arena, computation, &substitutions),
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
    use crate::program::ComputationTypeNode;
    let env = CrateEnv::new();
    let arena = env.arena();
    // A: VType, a: A. The annotation is outside the new let binder.
    let mut context = vec![
        ProgramContextEntry::Type { var: SymbolId(0) },
        ProgramContextEntry::Value {
            var: SymbolId(1),
            ty: arena.value_type_bound(0),
        },
    ];
    let value = arena.value_bound(0);
    let body = arena.alloc(ComputationNode::Return { value });
    let make_let = |value_ty| {
        arena.alloc(ComputationNode::ValueLet {
            var: SymbolId(2),
            value_ty,
            value,
            body,
        })
    };
    let term = make_let(arena.value_type_bound(1));
    let inferred = ProgramCheckSession::new(&env, &mut context)
        .infer_computation(term)
        .unwrap();
    let ComputationTypeNode::Return { value_ty } = arena.get(inferred) else {
        panic!()
    };
    assert_eq!(arena.get(value_ty), ValueTypeNode::Bound(1));
    let wrong = arena.alloc(ValueTypeNode::Thunk {
        computation_ty: inferred,
    });
    for annotation in [arena.value_type_bound(0), wrong] {
        assert!(
            ProgramCheckSession::new(&env, &mut context)
                .infer_computation(make_let(annotation))
                .is_err()
        );
        assert_eq!(context.len(), 2);
    }

    let reflected = crate::reflection::reflect_computation(&env, term).unwrap();
    let ExpNode::App { func, arg } = arena.get(reflected) else {
        panic!()
    };
    assert_eq!(arena.get(arg), ExpNode::Bound(0));
    let ExpNode::Lam { ty, body, .. } = arena.get(func) else {
        panic!()
    };
    assert_eq!(arena.get(ty), ExpNode::Bound(1));
    assert_eq!(arena.get(body), ExpNode::Bound(0));
    let mut reflected_context = crate::reflection::reflect_context(&env, &context).unwrap();
    CheckSession::new(&env, env.root_module(), &mut reflected_context)
        .check_pts(
            reflected,
            crate::reflection::reflect_computation_type(&env, inferred).unwrap(),
        )
        .unwrap();
}

#[test]
fn value_let_annotations_follow_binder_shifts_and_substitution() {
    use crate::program_calculus::{computation_is_alpha_eq, instantiate_value_in_computation};
    let env = CrateEnv::new();
    let arena = env.arena();
    // In A: VType, a: A, bind x = a and then y = x.
    let inner = arena.alloc(ComputationNode::ValueLet {
        var: SymbolId(3),
        value_ty: arena.value_type_bound(2),
        value: arena.value_bound(0),
        body: arena.alloc(ComputationNode::Return {
            value: arena.value_bound(0),
        }),
    });
    let outer = arena.alloc(ComputationNode::ValueLet {
        var: SymbolId(2),
        value_ty: arena.value_type_bound(1),
        value: arena.value_bound(0),
        body: inner,
    });
    let shifted = shift_computation_indices(arena, outer, 1, 0);
    let ComputationNode::ValueLet {
        value_ty,
        value,
        body,
        ..
    } = arena.get(shifted)
    else {
        panic!()
    };
    assert_eq!(arena.get(value_ty), ValueTypeNode::Bound(2));
    assert_eq!(arena.get(value), ValueNode::Bound(1));
    let ComputationNode::ValueLet {
        value_ty, value, ..
    } = arena.get(body)
    else {
        panic!()
    };
    assert_eq!(arena.get(value_ty), ValueTypeNode::Bound(3));
    assert_eq!(arena.get(value), ValueNode::Bound(0));

    let substituted = instantiate_value_in_computation(arena, inner, arena.value_bound(0));
    let ComputationNode::ValueLet { value_ty, .. } = arena.get(substituted) else {
        panic!()
    };
    assert_eq!(arena.get(value_ty), ValueTypeNode::Bound(1));
    let Evaluation::Normal(normal) = evaluate_computation(&env, outer) else {
        panic!()
    };
    let ComputationNode::Return { value } = arena.get(normal) else {
        panic!()
    };
    assert_eq!(arena.get(value), ValueNode::Bound(0));
    let renamed = arena.alloc(ComputationNode::ValueLet {
        var: SymbolId(99),
        value_ty: arena.value_type_bound(1),
        value: arena.value_bound(0),
        body: inner,
    });
    assert!(computation_is_alpha_eq(arena, outer, renamed));
    assert!(!computation_is_alpha_eq(arena, outer, shifted));
    let different_annotation = arena.alloc(ComputationNode::ValueLet {
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
    let body = arena.alloc(ComputationNode::Return {
        value: arena.value_bound(0),
    });
    let term = arena.alloc(ComputationNode::ValueLet {
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
        &[(parameter, ModuleArgument::ProgramType(datatype))],
    );
    let ComputationNode::ValueLet { value_ty, .. } = arena.get(instantiated) else {
        panic!()
    };
    assert_eq!(value_ty, datatype);
    let remapped = remap_computation_global_ids(
        arena,
        instantiated,
        &Default::default(),
        &std::collections::HashMap::from([(old, new)]),
    );
    let ComputationNode::ValueLet { value_ty, .. } = arena.get(remapped) else {
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
    use crate::{
        ids::MetaVarId,
        reflection::{ReflectionError, reflect_computation, reflect_computation_with_certificates},
    };
    let env = CrateEnv::new();
    let arena = env.arena();
    let ty = arena.value_type_bound(1);
    let value = arena.value_bound(0);
    let run = arena.alloc(ComputationNode::Run {
        state_ty: ty,
        result_ty: ty,
        step: value,
        initial: value,
    });
    let term = arena.alloc(ComputationNode::ValueLet {
        var: SymbolId(0),
        value_ty: ty,
        value,
        body: run,
    });
    assert_eq!(
        reflect_computation(&env, term),
        Err(ReflectionError::MissingRunCertificate)
    );
    let certificate = arena.exp_bound(0);
    let reflected = reflect_computation_with_certificates(
        &env,
        term,
        &std::collections::HashMap::from([(run, certificate)]),
    )
    .unwrap();
    let ExpNode::App { func, .. } = arena.get(reflected) else {
        panic!()
    };
    assert!(matches!(arena.get(func), ExpNode::Lam { body, .. } if body == certificate));
    let meta = arena.alloc(ValueTypeNode::Meta {
        metavariable: MetaVarId(0),
        spine: vec![],
    });
    let term = arena.alloc(ComputationNode::ValueLet {
        var: SymbolId(0),
        value_ty: meta,
        value,
        body: arena.alloc(ComputationNode::Return { value }),
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
                state_ty,
                result_ty,
            },
            ExpNode::Continue {
                state_ty,
                result_ty,
                next: argument,
            },
            ExpNode::Finish {
                state_ty,
                result_ty,
                output: argument,
            },
            ExpNode::Acc {
                state_ty,
                result_ty,
                step: argument,
                state: argument,
            },
            ExpNode::SetRun {
                state_ty,
                result_ty,
                step: argument,
                initial: argument,
                accessibility: argument,
            },
            ExpNode::SetRunCase {
                state_ty,
                result_ty,
                step: argument,
                initial: argument,
                transition: argument,
                accessibility: argument,
                transition_equality: argument,
            },
            ExpNode::RunStepRec {
                state_ty,
                result_ty,
                motive: argument,
                on_continue: argument,
                on_finish: argument,
                scrutinee: argument,
            },
            ExpNode::Prove(crate::exp::Prove::AccIntro {
                state_ty,
                result_ty,
                step: argument,
                state: argument,
                predecessors: argument,
            }),
            ExpNode::Prove(crate::exp::Prove::AccDescent {
                state_ty,
                result_ty,
                step: argument,
                from: argument,
                to: argument,
                accessibility: argument,
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
    use crate::{environment::DefinedConstant, ids::MetaVarId};
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
                body: set
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
                ty: set,
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
                ty: set,
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
fn program_registration_checks_body_and_reflection_certificate() {
    use crate::environment::{DefinedConstant, ModuleParameter, ModuleParameterKind};
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
            kind: ModuleParameterKind::ProgramValue { ty },
        },
    );
    let body = env.arena().alloc(ValueNode::ModuleParam(ModuleParamId {
        module,
        position: 1,
    }));
    let bad_body = env.arena().value_bound(0);
    assert!(
        env.add_definition(
            module,
            DefinedConstant::ProgramValue {
                ty,
                body: bad_body,
                certified_reflection: None,
            }
        )
        .is_err()
    );
    let bad_certificate = env.arena().sort(Sort::Set(0));
    assert!(
        env.add_definition(
            module,
            DefinedConstant::ProgramValue {
                ty,
                body,
                certified_reflection: Some(bad_certificate),
            }
        )
        .unwrap_err()
        .contains("certificate")
    );
    let certificate = crate::reflection::reflect_value(&env, body).unwrap();
    let id = env
        .add_definition(
            module,
            DefinedConstant::ProgramValue {
                ty,
                body,
                certified_reflection: Some(certificate),
            },
        )
        .unwrap();
    assert_eq!(id.index, 0);
    let computation_ty = env
        .arena()
        .alloc(crate::program::ComputationTypeNode::Return { value_ty: ty });
    let computation = env.arena().alloc(ComputationNode::Return { value: body });
    assert!(
        env.add_definition(
            module,
            DefinedConstant::ProgramComputation {
                ty: computation_ty,
                body: computation,
                certified_reflection: None,
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
