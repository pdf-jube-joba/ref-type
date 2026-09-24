use super::{calculus::*, check::Checker, environment::*, reflection::*, sort::*, syntax::*};
use crate::ids::*;

fn vk(a: &Arena, i: usize) -> ValueKind {
    a.alloc(ValueKindNode {
        level: i,
        form: ValueKindForm::Base,
    })
}

fn sk(a: &Arena, i: usize) -> SetKind {
    a.alloc(SetKindNode {
        level: i,
        form: SetKindForm::Base,
    })
}

#[test]
fn typed_handles_remain_tied_to_their_owning_environment() {
    let first = Environment::new();
    let second = Environment::new();
    let left: Expression = sk(first.arena(), 0).into();
    let right: Expression = sk(second.arena(), 0).into();
    assert_ne!(left, right);
    assert_ne!(first.arena().id(), second.arena().id());
    assert!(
        Checker::new(&first, vec![])
            .infer(right)
            .unwrap_err()
            .contains("another arena")
    );
    assert!(convertible(&first, right, right).is_err());
    assert!(!alpha_equal(first.arena(), right, right));
    assert!(Checker::new(&first, vec![]).infer(left).is_ok());
}

#[test]
fn definition_checking_discards_scratch_nodes_and_stale_cache_entries() {
    let mut env = Environment::new();
    let kind = sk(env.arena(), 0);
    let rule =
        ProductRule::new(Sort::Upper(BaseSort::Set(0)), Sort::Upper(BaseSort::Set(0))).unwrap();
    let bound = env.arena().alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::Bound { index: 0 },
    });
    let identity = env.arena().alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::LambdaType {
            rule,
            var: SymbolId::ANONYMOUS,
            domain: kind,
            body: bound,
        },
    });
    let classifier = env.arena().alloc(SetKindNode {
        level: 0,
        form: SetKindForm::ProdType {
            rule,
            var: SymbolId(1),
            domain: kind,
            body: kind,
        },
    });
    // The checker synthesizes an anonymous product distinct from the declared
    // product. Only the latter belongs to the persistent declaration.
    let counts = env.arena().node_counts();
    let snapshot = env.arena().read(identity);
    let id = env.fresh_global_id();
    env.register_definition(
        id,
        Definition {
            context: vec![],
            body: identity.into(),
            classifier: classifier.into(),
        },
    )
    .unwrap();
    assert_eq!(env.arena().node_counts(), counts);
    assert_eq!(env.arena().get(identity), *snapshot);
    assert_eq!(env.arena().alloc((*snapshot).clone()), identity);
    let unrelated = sk(env.arena(), 1);
    let inferred = Checker::new(&env, vec![]).infer_set_type(identity).unwrap();
    assert_ne!(inferred, unrelated);
    assert!(convertible(&env, inferred.into(), classifier.into()).unwrap());

    let counts = env.arena().node_counts();
    let bad_id = env.fresh_global_id();
    assert!(
        env.register_definition(
            bad_id,
            Definition {
                context: vec![],
                body: identity.into(),
                classifier: unrelated.into()
            }
        )
        .is_err()
    );
    assert!(env.definition(bad_id).is_none());
    assert_eq!(env.arena().node_counts(), counts);
    assert_eq!(
        Checker::new(&env, vec![]).infer_set_type(identity).unwrap(),
        inferred
    );
}

#[test]
fn closed_dag_queries_and_global_substitutions_preserve_sharing() {
    let env = Environment::new();
    let a = env.arena();
    let id = env.fresh_inductive_id();
    let other = env.fresh_inductive_id();
    let parameter = 0;
    let rule =
        ProductRule::new(Sort::Base(BaseSort::Set(0)), Sort::Base(BaseSort::Set(0))).unwrap();
    let product = |domain, body| {
        a.alloc(SetTypeNode {
            level: 0,
            form: SetTypeForm::ProdTerm {
                rule,
                var: SymbolId::ANONYMOUS,
                domain,
                body,
            },
        })
    };
    let leaf = a.alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::IndType {
            inductive: id,
            parameters: vec![],
        },
    });
    let mut shared = leaf;
    let mut remapped = a.alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::IndType {
            inductive: other,
            parameters: vec![],
        },
    });
    let mut named = a.alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::Ambient { level: parameter },
    });
    for _ in 0..24 {
        shared = product(shared, shared);
        remapped = product(remapped, remapped);
        named = product(named, named);
    }
    assert!(is_closed(a, shared.into()));
    assert!(closed_in_environment(&env, shared.into()));
    assert!(!contains_bound(a, shared.into(), 0));
    assert!(!is_closed(a, named.into()));
    assert_eq!(
        remap_ids(a, shared.into(), &[(id, other)].into(), &Default::default()).unwrap(),
        remapped.into()
    );
    assert_eq!(
        substitute_ambient(&env, named.into(), &[(parameter, leaf.into())].into()).unwrap(),
        shared.into()
    );
}

#[test]
fn local_closure_tracks_shared_binders_and_annotation_classifiers() {
    let arena = Arena::new();
    let bound = |index| {
        arena.alloc(SetTypeNode {
            level: 0,
            form: SetTypeForm::Bound { index },
        })
    };
    let rule =
        ProductRule::new(Sort::Upper(BaseSort::Set(0)), Sort::Upper(BaseSort::Set(0))).unwrap();
    let lambda = |body| {
        arena.alloc(SetTypeNode {
            level: 0,
            form: SetTypeForm::LambdaType {
                rule,
                var: SymbolId::ANONYMOUS,
                domain: sk(&arena, 0),
                body,
            },
        })
    };
    let free = bound(0);
    let closed = lambda(free);
    let open = lambda(bound(1));
    // The same node is open at the root and closed under one binder, including
    // after warming the arena's cache with both kinds of queries.
    for _ in 0..2 {
        assert!(!locally_closed(&arena, free.into()));
        assert!(locally_closed(&arena, closed.into()));
        assert!(!locally_closed(&arena, open.into()));
        assert!(locally_closed(&arena, lambda(open).into()));
    }

    let parameter = arena.alloc(SetTermNode {
        level: 0,
        form: SetTermForm::Ambient { level: 0 },
    });
    assert!(locally_closed(&arena, parameter.into()));
    let annotated = arena.annotated(parameter.into(), free.into()).unwrap();
    // A closed body cannot hide an open type annotation.
    assert!(!locally_closed(&arena, annotated));
}

#[test]
fn shared_syntax_transformations_respect_each_binder_depth() {
    let a = Arena::new();
    let ty = |index| {
        a.alloc(SetTypeNode {
            level: 0,
            form: SetTypeForm::Bound { index },
        })
    };
    let rule =
        ProductRule::new(Sort::Base(BaseSort::Set(0)), Sort::Base(BaseSort::Set(0))).unwrap();
    let product = |domain, body| {
        a.alloc(SetTypeNode {
            level: 0,
            form: SetTypeForm::ProdTerm {
                rule,
                var: SymbolId::ANONYMOUS,
                domain,
                body,
            },
        })
    };
    let argument = a.alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::Ambient { level: 0 },
    });
    let mut shared = ty(0);
    let mut shifted = ty(1);
    let mut substituted = argument;
    // Only the path through domains keeps index 0 free. Every body binds it.
    // This DAG has 25 nodes but more than 16 million paths to its leaf.
    for _ in 0..24 {
        shifted = product(shifted, shared);
        substituted = product(substituted, shared);
        shared = product(shared, shared);
    }
    assert_eq!(shift(&a, shared, 1, 0).unwrap(), shifted.into());
    assert_eq!(
        substitute(&a, shared, argument).unwrap(),
        substituted.into()
    );
    assert_eq!(shift(&a, shared, 0, 0).unwrap(), shared.into());
}

#[test]
fn telescope_substitution_is_simultaneous_and_avoids_intermediate_nodes() {
    let env = Environment::new();
    let a = env.arena();
    let bound = |index| {
        a.alloc(SetTypeNode {
            level: 0,
            form: SetTypeForm::Bound { index },
        })
    };
    let rule =
        ProductRule::new(Sort::Base(BaseSort::Set(0)), Sort::Base(BaseSort::Set(0))).unwrap();
    let product = |domain, body| {
        a.alloc(SetTypeNode {
            level: 0,
            form: SetTypeForm::ProdTerm {
                rule,
                var: SymbolId::ANONYMOUS,
                domain,
                body,
            },
        })
    };
    let body = product(bound(1), product(bound(1), bound(4)));
    // The shared index 1 selects different arguments at the two depths.
    // Index 4 refers outside the telescope; the arguments are themselves open.
    let expected = product(bound(0), product(bound(2), bound(2)));
    let arguments = [bound(0).into(), bound(1).into()];
    let counts = a.node_counts();
    assert_eq!(
        instantiate_telescope(&env, body.into(), &arguments).unwrap(),
        expected.into()
    );
    assert_eq!(a.node_counts(), counts);
    assert_eq!(
        instantiate_telescope(&env, body.into(), &[]).unwrap(),
        body.into()
    );

    let mut sequential = body.into();
    for (i, &argument) in arguments.iter().enumerate().rev() {
        sequential =
            substitute_with_reflection(&env, sequential, shift(a, argument, i, 0).unwrap())
                .unwrap();
    }
    assert_eq!(sequential, expected.into());
}

#[test]
fn weak_head_reduction_batches_arguments_and_preserves_partial_applications() {
    let env = Environment::new();
    let a = env.arena();
    let kind = sk(a, 0);
    let rule =
        ProductRule::new(Sort::Upper(BaseSort::Set(0)), Sort::Upper(BaseSort::Set(0))).unwrap();
    let bound = |index| {
        a.alloc(SetTypeNode {
            level: 0,
            form: SetTypeForm::Bound { index },
        })
    };
    let lambda = |body| {
        a.alloc(SetTypeNode {
            level: 0,
            form: SetTypeForm::LambdaType {
                rule,
                var: SymbolId::ANONYMOUS,
                domain: kind,
                body,
            },
        })
    };
    let apply = |function, argument| {
        a.alloc(SetTypeNode {
            level: 0,
            form: SetTypeForm::AppType {
                rule,
                function,
                argument,
            },
        })
    };
    let function = lambda(lambda(bound(1)));
    let function = a
        .annotated(function.into(), kind.into())
        .unwrap()
        .try_into()
        .unwrap();
    let first = bound(2);
    let second = bound(4);
    let partial = apply(function, first);
    let full = apply(partial, second);
    let extra = apply(full, second);
    let expected_partial = lambda(bound(3));
    let expected_extra = apply(first, second);
    let counts = a.node_counts();
    assert_eq!(whnf(&env, full.into()).unwrap(), first.into());
    assert_eq!(whnf(&env, partial.into()).unwrap(), expected_partial.into());
    assert_eq!(whnf(&env, extra.into()).unwrap(), expected_extra.into());
    assert_eq!(a.node_counts(), counts);
    assert_eq!(normalize(&env, full).unwrap(), first.into());

    let malformed = a.alloc(SetTypeNode {
        level: 1,
        form: a.get(full).form,
    });
    assert!(whnf(&env, malformed.into()).is_err());
}

#[test]
fn typed_nodes_are_interned_and_read_snapshots_survive_transformations() {
    let arena = Arena::new();
    let domain = arena.alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::Bound { index: 0 },
    });
    let rule =
        ProductRule::new(Sort::Base(BaseSort::Set(0)), Sort::Base(BaseSort::Set(0))).unwrap();
    let original = SetTypeNode {
        level: 0,
        form: SetTypeForm::ProdTerm {
            rule,
            var: SymbolId(4),
            domain,
            body: domain,
        },
    };
    let handle = arena.alloc(original.clone());
    assert_eq!(arena.alloc(original.clone()), handle);
    let snapshot = arena.read(handle);
    assert!(std::rc::Rc::ptr_eq(&snapshot, &arena.read(handle)));

    // Allocating during recursion must not conflict with a retained read.
    let changed: SetType = shift(&arena, handle, 1, 0).unwrap().try_into().unwrap();
    assert_ne!(changed, handle);
    assert_eq!(*snapshot, original);
    assert_eq!(arena.get(handle), original);
    let SetTypeForm::ProdTerm {
        domain: shifted,
        body,
        ..
    } = arena.get(changed).form
    else {
        panic!("expected a product");
    };
    assert_eq!(body, domain);
    assert_eq!(arena.get(shifted).form, SetTypeForm::Bound { index: 1 });
}

#[test]
fn substitution_tracks_each_inductive_motive_binder() {
    let arena = Arena::new();
    let ty = |index| {
        arena.alloc(SetTypeNode {
            level: 0,
            form: SetTypeForm::Bound { index },
        })
    };
    let term = |index| {
        arena.alloc(SetTermNode {
            level: 0,
            form: SetTermForm::Bound { index },
        })
    };
    let argument = arena.alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::Ambient { level: 0 },
    });
    let original = SetTypeNode {
        level: 0,
        form: SetTypeForm::IndElim {
            inductive: InductiveId {
                owner: arena.id(),
                index: 1,
            },
            motive_vars: vec![SymbolId(1), SymbolId(2)],
            scrutinee: term(1).into(),
            motive_domains: vec![ty(0).into(), ty(1).into()],
            motive_body: ty(2).into(),
            cases: vec![term(1).into()],
        },
    };
    let elimination = arena.alloc(original.clone());
    let result: SetType = substitute(&arena, elimination, argument)
        .unwrap()
        .try_into()
        .unwrap();
    let SetTypeForm::IndElim {
        scrutinee,
        motive_domains,
        motive_body,
        cases,
        ..
    } = arena.get(result).form
    else {
        panic!("expected an eliminator");
    };
    assert_eq!(scrutinee, term(0).into());
    assert_eq!(motive_domains, vec![argument.into(), argument.into()]);
    assert_eq!(motive_body, argument.into());
    assert_eq!(cases, vec![term(0).into()]);
    assert_eq!(arena.get(elimination), original);
}

#[test]
fn run_certificates_are_transformed_but_ignored_by_conversion() {
    let env = Environment::new();
    let arena = env.arena();
    let ty = arena.alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::Bound { index: 0 },
    });
    let term = |index| {
        arena.alloc(SetTermNode {
            level: 0,
            form: SetTermForm::Bound { index },
        })
    };
    let proof = |index| {
        arena.alloc(PropTermNode {
            form: PropTermForm::Bound { index },
        })
    };
    let run = |initial, accessibility| {
        arena.alloc(SetTermNode {
            level: 0,
            form: SetTermForm::SetRun {
                state_ty: ty,
                result_ty: ty,
                step: term(1),
                initial,
                accessibility,
            },
        })
    };
    let first = run(term(0), proof(0));
    let second = run(term(0), proof(1));
    assert_ne!(first, second);
    assert!(alpha_equal(arena, first.into(), second.into()));
    assert!(convertible(&env, first.into(), second.into()).unwrap());
    assert!(!alpha_equal(
        arena,
        first.into(),
        run(term(2), proof(0)).into()
    ));

    let shifted: SetTerm = shift(arena, first, 1, 0).unwrap().try_into().unwrap();
    let SetTermForm::SetRun {
        accessibility,
        initial,
        ..
    } = arena.get(shifted).form
    else {
        panic!("expected a run");
    };
    assert_eq!(accessibility, proof(1));
    assert_eq!(initial, term(1));
}

#[test]
fn checked_definition_templates_are_retained_without_becoming_constants() {
    let mut env = Environment::new();
    let kind = sk(env.arena(), 0);
    let body = env.arena().alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::Bound { index: 0 },
    });
    let id = env.fresh_global_id();
    let template = Definition {
        context: vec![Binding {
            var: SymbolId(1),
            classifier: kind.into(),
        }],
        body: body.into(),
        classifier: kind.into(),
    };
    env.register_definition_template(id, template.clone())
        .unwrap();
    assert!(env.definition(id).is_none());
    assert_eq!(env.definition_template(id).unwrap().context.len(), 1);
    assert!(env.register_definition_template(id, template).is_err());
}

#[test]
fn polymorphic_program_identity_and_reflection() {
    let env = Environment::new();
    let a = &env.arena;
    let k = vk(a, 0);
    let x = a.alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::Bound { index: 0 },
    });
    let v = a.alloc(ValueTermNode {
        level: 0,
        form: ValueTermForm::Bound { index: 0 },
    });
    let ret = a.alloc(ComputationTermNode {
        level: 0,
        form: ComputationTermForm::Return { value: v },
    });
    let r = ProductRule::new(
        Sort::Base(BaseSort::Value(0)),
        Sort::Base(BaseSort::Computation(0)),
    )
    .unwrap();
    let lam = a.alloc(ComputationTermNode {
        level: 0,
        form: ComputationTermForm::LambdaTerm {
            rule: r,
            var: SymbolId(2),
            domain: x,
            body: ret,
        },
    });
    let poly_rule = ProductRule::new(
        Sort::Upper(BaseSort::Value(0)),
        Sort::Base(BaseSort::Computation(0)),
    )
    .unwrap();
    let poly = a.alloc(ComputationTermNode {
        level: 1,
        form: ComputationTermForm::LambdaType {
            rule: poly_rule,
            var: SymbolId(1),
            domain: k.into(),
            body: lam,
        },
    });
    let mut checker = Checker::new(&env, vec![]);
    let ty = checker.infer_computation_term(poly).unwrap();
    assert_eq!(a.sort(ty), BaseSort::Computation(1));
    let refl = reflect_term(&env, poly.into()).unwrap();
    let rty = reflect_type(&env, ty.into()).unwrap();
    checker.check(refl, rty).unwrap();
    // Instantiate at an open value type A, then at x : A. The result has level 0.
    let arg = a.alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::Bound { index: 1 },
    });
    let applied = a.alloc(ComputationTermNode {
        level: 0,
        form: ComputationTermForm::AppType {
            rule: poly_rule,
            function: poly,
            argument: arg.into(),
        },
    });
    let applied = a.alloc(ComputationTermNode {
        level: 0,
        form: ComputationTermForm::AppTerm {
            rule: r,
            function: applied,
            argument: v,
        },
    });
    let mut checker = Checker::new(
        &env,
        vec![
            Binding {
                var: SymbolId(3),
                classifier: k.into(),
            },
            Binding {
                var: SymbolId(4),
                classifier: x.into(),
            },
        ],
    );
    let result_ty = checker.infer_computation_term(applied).unwrap();
    assert_eq!(a.sort(result_ty), BaseSort::Computation(0));
    let result = normalize(&env, applied).unwrap();
    assert!(matches!(
        a.read(ComputationTerm::try_from(result).unwrap()).form,
        ComputationTermForm::Return { .. }
    ));
    let inferred = checker.inferred(result).unwrap();
    assert!(convertible(&env, inferred, result_ty.into()).unwrap());
}
#[test]
fn type_operator_beta_preserves_annotations_under_value_binders() {
    let env = Environment::new();
    let a = &env.arena;
    let k = vk(a, 0);
    let x = a.alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::Bound { index: 0 },
    });
    let fx = a.alloc(ComputationTypeNode {
        level: 0,
        form: ComputationTypeForm::ReturnType { value_ty: x },
    });
    let r = ProductRule::new(
        Sort::Upper(BaseSort::Value(0)),
        Sort::Upper(BaseSort::Computation(0)),
    )
    .unwrap();
    let f = a.alloc(ComputationTypeNode {
        level: 0,
        form: ComputationTypeForm::LambdaType {
            rule: r,
            var: SymbolId(2),
            domain: k.into(),
            body: fx,
        },
    });
    let app = a.alloc(ComputationTypeNode {
        level: 0,
        form: ComputationTypeForm::AppType {
            rule: r,
            function: f,
            argument: x.into(),
        },
    });
    let mut checker = Checker::new(
        &env,
        vec![Binding {
            var: SymbolId(1),
            classifier: k.into(),
        }],
    );
    checker.infer_program_type(app.into()).unwrap();
    assert!(convertible(&env, app.into(), fx.into()).unwrap());
}
#[test]
fn incorrect_labels_levels_and_kind_as_type_are_rejected() {
    let env = Environment::new();
    let a = &env.arena;
    let k = sk(a, 0);
    let ty = a.alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::Bound { index: 0 },
    });
    let bad = a.alloc(SetTypeNode {
        level: 1,
        form: SetTypeForm::Bound { index: 0 },
    });
    let mut checker = Checker::new(
        &env,
        vec![Binding {
            var: SymbolId(1),
            classifier: k.into(),
        }],
    );
    assert!(checker.infer_set_type(bad).is_err());
    assert!(checker.check(ty, sk(a, 1)).is_err());
    let r = ProductRule {
        domain: Sort::Base(BaseSort::Set(0)),
        body: Sort::Base(BaseSort::Set(0)),
        result: Sort::Base(BaseSort::Set(1)),
    };
    assert!(r.validate().is_err());
    assert!(SetType::try_from(Expression::from(k)).is_err());
}
#[test]
fn substitution_rejects_cross_level_arguments() {
    let a = Arena::new();
    let x = a.alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::Bound { index: 0 },
    });
    let y = a.alloc(SetTypeNode {
        level: 1,
        form: SetTypeForm::Bound { index: 0 },
    });
    assert!(substitute(&a, x, y).is_err());
}

fn program_id(a: &Arena, i: usize) -> ComputationTerm {
    let x = a.alloc(ValueTypeNode {
        level: i,
        form: ValueTypeForm::Bound { index: 0 },
    });
    let v = a.alloc(ValueTermNode {
        level: i,
        form: ValueTermForm::Bound { index: 0 },
    });
    let ret = a.alloc(ComputationTermNode {
        level: i,
        form: ComputationTermForm::Return { value: v },
    });
    let r = ProductRule::new(
        Sort::Base(BaseSort::Value(i)),
        Sort::Base(BaseSort::Computation(i)),
    )
    .unwrap();
    let lambda = a.alloc(ComputationTermNode {
        level: i,
        form: ComputationTermForm::LambdaTerm {
            rule: r,
            var: SymbolId(2),
            domain: x,
            body: ret,
        },
    });
    let r = ProductRule::new(
        Sort::Upper(BaseSort::Value(i)),
        Sort::Base(BaseSort::Computation(i)),
    )
    .unwrap();
    a.alloc(ComputationTermNode {
        level: i + 1,
        form: ComputationTermForm::LambdaType {
            rule: r,
            var: SymbolId(1),
            domain: vk(a, i).into(),
            body: lambda,
        },
    })
}
#[test]
fn closed_polymorphic_box_type_application_then_value_application() {
    let env = Environment::new();
    let a = &env.arena;
    let id0 = program_id(a, 0);
    let id1 = program_id(a, 1);
    let mut c = Checker::new(&env, vec![]);
    let ty0 = c.infer_computation_term(id0).unwrap();
    let ty1 = c.infer_computation_term(id1).unwrap();
    let boxed = a.alloc(SetTermNode {
        level: 2,
        form: SetTermForm::BoxProgram {
            program_ty: ty1,
            program: id1,
        },
    });
    let ComputationTypeForm::ProdType {
        rule,
        domain,
        body,
        var,
    } = a.get(ty1).form
    else {
        panic!()
    };
    let arg_ty = a.alloc(ValueTypeNode {
        level: 1,
        form: ValueTypeForm::Thunk {
            computation_ty: ty0,
        },
    });
    let tapp = a.alloc(SetTermNode {
        level: 1,
        form: SetTermForm::BoxTypeApp {
            rule,
            var,
            domain,
            codomain: body,
            function: boxed,
            argument: arg_ty.into(),
        },
    });
    c.infer_set_term(tapp).unwrap();
    let arg = a.alloc(ValueTermNode {
        level: 1,
        form: ValueTermForm::ThunkValue { computation: id0 },
    });
    let result_ty = a.alloc(ComputationTypeNode {
        level: 1,
        form: ComputationTypeForm::ReturnType { value_ty: arg_ty },
    });
    let returned_arg = a.alloc(ComputationTermNode {
        level: 1,
        form: ComputationTermForm::Return { value: arg },
    });
    let boxed_arg = a.alloc(SetTermNode {
        level: 1,
        form: SetTermForm::BoxProgram {
            program_ty: result_ty,
            program: returned_arg,
        },
    });
    let r = ProductRule::new(
        Sort::Base(BaseSort::Value(1)),
        Sort::Base(BaseSort::Computation(1)),
    )
    .unwrap();
    let app = a.alloc(SetTermNode {
        level: 1,
        form: SetTermForm::BoxApp {
            rule: r,
            domain: arg_ty,
            codomain: result_ty,
            function: tapp,
            argument: boxed_arg,
        },
    });
    c.infer_set_term(app).unwrap();
    let forced = a.alloc(SetTermNode {
        level: 1,
        form: SetTermForm::ForceBox {
            program_ty: result_ty,
            boxed: app,
        },
    });
    c.infer_set_term(forced).unwrap();
    let reflected_arg = reflect_term(&env, arg.into()).unwrap();
    assert!(convertible(&env, forced.into(), reflected_arg.into()).unwrap());
    let nf = normalize(&env, forced).unwrap();
    c.inferred(nf).unwrap();
    assert_eq!(a.sort(nf), BaseSort::Set(1));
}
#[test]
fn computation_type_quantification_and_type_operator_domains() {
    let env = Environment::new();
    let a = &env.arena;
    let k = a.alloc(ComputationKindNode {
        level: 2,
        form: ComputationKindForm::Base,
    });
    let y = a.alloc(ComputationTypeNode {
        level: 2,
        form: ComputationTypeForm::Bound { index: 0 },
    });
    let u = a.alloc(ValueTypeNode {
        level: 2,
        form: ValueTypeForm::Thunk { computation_ty: y },
    });
    let v = a.alloc(ValueTermNode {
        level: 2,
        form: ValueTermForm::Bound { index: 0 },
    });
    let force = a.alloc(ComputationTermNode {
        level: 2,
        form: ComputationTermForm::Force { value: v },
    });
    let r = ProductRule::new(
        Sort::Base(BaseSort::Value(2)),
        Sort::Base(BaseSort::Computation(2)),
    )
    .unwrap();
    let lam = a.alloc(ComputationTermNode {
        level: 2,
        form: ComputationTermForm::LambdaTerm {
            rule: r,
            var: SymbolId(2),
            domain: u,
            body: force,
        },
    });
    let r = ProductRule::new(
        Sort::Upper(BaseSort::Computation(2)),
        Sort::Base(BaseSort::Computation(2)),
    )
    .unwrap();
    let lam = a.alloc(ComputationTermNode {
        level: 3,
        form: ComputationTermForm::LambdaType {
            rule: r,
            var: SymbolId(1),
            domain: k.into(),
            body: lam,
        },
    });
    let mut checker = Checker::new(&env, vec![]);
    let ty = checker.infer_computation_term(lam).unwrap();
    let reflected = reflect_term(&env, lam.into()).unwrap();
    let reflected_ty = reflect_type(&env, ty.into()).unwrap();
    checker.check(reflected, reflected_ty).unwrap();
}
#[test]
fn invalid_declaration_is_not_inserted() {
    let mut env = Environment::new();
    let id = env.fresh_global_id();
    let k = sk(&env.arena, 0);
    let result = env.register_definition(
        id,
        Definition {
            context: vec![],
            body: k.into(),
            classifier: Classifier::Upper(BaseSort::Set(1)),
        },
    );
    assert!(result.is_err());
    assert!(env.definition(id).is_none());
}
#[test]
fn product_signature_checks_all_program_rules_and_overflow() {
    for i in 0..3 {
        for j in 0..3 {
            for q in [BaseSort::Value(i), BaseSort::Computation(i)] {
                let rule =
                    ProductRule::new(Sort::Upper(q), Sort::Base(BaseSort::Computation(j))).unwrap();
                assert_eq!(
                    rule.result,
                    Sort::Base(BaseSort::Computation((i + 1).max(j)))
                );
                assert!(rule.reflected().validate().is_ok());
                for r in [BaseSort::Value(j), BaseSort::Computation(j)] {
                    assert!(
                        ProductRule::new(Sort::Upper(q), Sort::Upper(r))
                            .unwrap()
                            .reflected()
                            .validate()
                            .is_ok()
                    )
                }
            }
        }
    }
    assert!(
        ProductRule::new(
            Sort::Upper(BaseSort::Value(usize::MAX)),
            Sort::Base(BaseSort::Computation(0))
        )
        .is_err()
    );
    assert!(
        ProductRule::new(
            Sort::Base(BaseSort::Value(0)),
            Sort::Base(BaseSort::Value(0))
        )
        .is_err()
    );
    assert!(ProductRule::new(Sort::Base(BaseSort::Prop), Sort::Upper(BaseSort::Prop)).is_err());
}

fn natural(env: &mut Environment) -> (ProgramInductiveId, ValueType, ValueTerm) {
    let id = env.fresh_datatype_id();
    let reflected = env.fresh_inductive_id();
    let ty = env.arena.alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::Inductive {
            inductive: id,
            parameters: vec![],
        },
    });
    env.register_datatype(
        id,
        ProgramDatatype {
            parameters: vec![],
            level: 0,
            constructors: vec![vec![], vec![(SymbolId(1), ty)]],
            reflected,
        },
    )
    .unwrap();
    let zero = env.arena.alloc(ValueTermNode {
        level: 0,
        form: ValueTermForm::InductiveConstructor {
            inductive: id,
            constructor: 0,
            parameters: vec![],
            fields: vec![],
        },
    });
    (id, ty, zero)
}
#[test]
fn datatype_registration_generates_and_checks_its_set_mirror() {
    let mut env = Environment::new();
    let (id, ty, zero) = natural(&mut env);
    let mirror = env.datatype(id).unwrap().reflected;
    assert_eq!(env.inductive(mirror).unwrap().constructors.len(), 2);
    let s = env.arena.alloc(ValueTermNode {
        level: 0,
        form: ValueTermForm::InductiveConstructor {
            inductive: id,
            constructor: 1,
            parameters: vec![],
            fields: vec![zero],
        },
    });
    let mut c = Checker::new(&env, vec![]);
    c.check(s, ty).unwrap();
    let refl = reflect_term(&env, s.into()).unwrap();
    let refl_ty = reflect_type(&env, ty.into()).unwrap();
    c.check(refl, refl_ty).unwrap();
}
#[test]
fn positivity_checks_expand_type_operators_and_reject_negative_fields() {
    let mut env = Environment::new();
    let id = env.fresh_datatype_id();
    let mirror = env.fresh_inductive_id();
    let own = env.arena.alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::Inductive {
            inductive: id,
            parameters: vec![],
        },
    });
    let ret = env.arena.alloc(ComputationTypeNode {
        level: 0,
        form: ComputationTypeForm::ReturnType { value_ty: own },
    });
    let r = ProductRule::new(
        Sort::Base(BaseSort::Value(0)),
        Sort::Base(BaseSort::Computation(0)),
    )
    .unwrap();
    let negative = env.arena.alloc(ComputationTypeNode {
        level: 0,
        form: ComputationTypeForm::ProdTerm {
            rule: r,
            var: SymbolId(1),
            domain: own,
            body: ret,
        },
    });
    let negative = env.arena.alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::Thunk {
            computation_ty: negative,
        },
    });
    assert!(
        env.register_datatype(
            id,
            ProgramDatatype {
                parameters: vec![],
                level: 0,
                constructors: vec![vec![(SymbolId(1), negative)]],
                reflected: mirror
            }
        )
        .is_err()
    );
    assert!(env.datatype(id).is_none());
    assert!(env.inductive(mirror).is_none());
    let a = &env.arena;
    let x = a.alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::Bound { index: 0 },
    });
    let r = ProductRule::new(
        Sort::Upper(BaseSort::Value(0)),
        Sort::Upper(BaseSort::Value(0)),
    )
    .unwrap();
    let identity = a.alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::LambdaType {
            rule: r,
            var: SymbolId(1),
            domain: vk(a, 0).into(),
            body: x,
        },
    });
    let positive = a.alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::AppType {
            rule: r,
            function: identity,
            argument: own.into(),
        },
    });
    env.register_datatype(
        id,
        ProgramDatatype {
            parameters: vec![],
            level: 0,
            constructors: vec![vec![(SymbolId(1), positive)]],
            reflected: mirror,
        },
    )
    .unwrap();
}
#[test]
fn boxed_annotation_cannot_hide_an_open_ambient_variable() {
    let mut env = Environment::new();
    let (_, ty, _zero) = natural(&mut env);
    let p = 0;
    env.push_binding(Binding {
        var: SymbolId(1),
        classifier: ty.into(),
    })
    .unwrap();
    let body = env.arena.alloc(ValueTermNode {
        level: 0,
        form: ValueTermForm::Ambient { level: p },
    });
    let id = env.fresh_global_id();
    env.register_definition_template(
        id,
        Definition {
            context: vec![],
            body: body.into(),
            classifier: ty.into(),
        },
    )
    .unwrap();
    let constant = env.arena.alloc(ValueTermNode {
        level: 0,
        form: ValueTermForm::Annotated {
            body,
            classifier: ty.into(),
        },
    });
    let computation_ty = env.arena.alloc(ComputationTypeNode {
        level: 0,
        form: ComputationTypeForm::ReturnType { value_ty: ty },
    });
    let computation = env.arena.alloc(ComputationTermNode {
        level: 0,
        form: ComputationTermForm::Return { value: constant },
    });
    let boxed = env.arena.alloc(SetTermNode {
        level: 0,
        form: SetTermForm::BoxProgram {
            program_ty: computation_ty,
            program: computation,
        },
    });
    assert!(
        Checker::new(&env, vec![])
            .infer_set_term(boxed)
            .unwrap_err()
            .contains("closed")
    );
    assert_eq!(reduce_once(&env, constant).unwrap(), None);
}
#[test]
fn program_run_evaluates_and_rejects_a_wrong_embedded_proof() {
    let mut env = Environment::new();
    let (_, ty, zero) = natural(&mut env);
    let a = &env.arena;
    let finish = a.alloc(ValueTermNode {
        level: 0,
        form: ValueTermForm::Finish {
            state_ty: ty,
            result_ty: ty,
            output: zero,
        },
    });
    let ret = a.alloc(ComputationTermNode {
        level: 0,
        form: ComputationTermForm::Return { value: finish },
    });
    let r = ProductRule::new(
        Sort::Base(BaseSort::Value(0)),
        Sort::Base(BaseSort::Computation(0)),
    )
    .unwrap();
    let lam = a.alloc(ComputationTermNode {
        level: 0,
        form: ComputationTermForm::LambdaTerm {
            rule: r,
            var: SymbolId(1),
            domain: ty,
            body: ret,
        },
    });
    let step = a.alloc(ValueTermNode {
        level: 0,
        form: ValueTermForm::ThunkValue { computation: lam },
    });
    let termination_parameter = 0;
    let accessibility_ty = a.alloc(PropTypeNode {
        form: PropTypeForm::Acc {
            state_ty: reflect_type(&env, ty.into()).unwrap(),
            result_ty: reflect_type(&env, ty.into()).unwrap(),
            step: reflect_term(&env, step.into()).unwrap(),
            state: reflect_term(&env, zero.into()).unwrap(),
        },
    });
    let accessibility = a.alloc(PropTermNode {
        form: PropTermForm::Ambient {
            level: termination_parameter,
        },
    });
    env.push_binding(Binding {
        var: SymbolId::ANONYMOUS,
        classifier: accessibility_ty.into(),
    })
    .unwrap();
    let a = &env.arena;
    let run = a.alloc(ComputationTermNode {
        level: 0,
        form: ComputationTermForm::Run {
            state_ty: ty,
            result_ty: ty,
            step,
            initial: zero,
            accessibility,
        },
    });
    let mut c = Checker::new(&env, vec![]);
    let result_ty = c.infer_computation_term(run).unwrap();
    let bad = a.alloc(ComputationTermNode {
        level: 0,
        form: ComputationTermForm::Run {
            state_ty: ty,
            result_ty: ty,
            step,
            initial: zero,
            accessibility: a.alloc(PropTermNode {
                form: PropTermForm::IdRefl {
                    element: reflect_term(&env, zero.into()).unwrap(),
                },
            }),
        },
    });
    assert!(c.infer_computation_term(bad).is_err());
    // Equality ignores proof identity, while checking still rejects a wrong proof.
    assert!(alpha_equal(a, run.into(), bad.into()));
    assert!(matches!(
        evaluate(&env, run, 0).unwrap(),
        Evaluation::OutOfFuel(_)
    ));
    let Evaluation::Normal(result) = evaluate(&env, run, 10).unwrap() else {
        panic!()
    };
    c.check(result, result_ty).unwrap();
    assert!(matches!(
        a.read(ComputationTerm::try_from(result).unwrap()).form,
        ComputationTermForm::Return { .. }
    ));
}

#[test]
fn program_proof_substitution_uses_the_reflected_argument() {
    let mut env = Environment::new();
    let (_, ty, zero) = natural(&mut env);
    let a = &env.arena;
    let variable = a.alloc(ValueTermNode {
        level: 0,
        form: ValueTermForm::Bound { index: 0 },
    });
    let reflected_variable = a.alloc(SetTermNode {
        level: 0,
        form: SetTermForm::Bound { index: 0 },
    });
    let proof = a.alloc(PropTermNode {
        form: PropTermForm::IdRefl {
            element: reflected_variable,
        },
    });
    let run = a.alloc(ComputationTermNode {
        level: 0,
        form: ComputationTermForm::Run {
            state_ty: ty,
            result_ty: ty,
            step: variable,
            initial: variable,
            accessibility: proof,
        },
    });
    let instantiated: ComputationTerm = substitute_with_reflection(&env, run, zero)
        .unwrap()
        .try_into()
        .unwrap();
    let type_variable = a.alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::Bound { index: 1 },
    });
    let polymorphic_run = a.alloc(ComputationTermNode {
        level: 0,
        form: ComputationTermForm::Run {
            state_ty: type_variable,
            result_ty: type_variable,
            step: variable,
            initial: variable,
            accessibility: proof,
        },
    });
    assert_eq!(
        instantiate_telescope(&env, polymorphic_run.into(), &[ty.into(), zero.into()]).unwrap(),
        instantiated.into()
    );
    let ComputationTermForm::Run {
        initial,
        accessibility,
        ..
    } = a.read(instantiated).form
    else {
        panic!()
    };
    assert_eq!(initial, zero);
    assert_eq!(
        a.read(accessibility).form,
        PropTermForm::IdRefl {
            element: reflect_term(&env, zero.into()).unwrap()
        }
    );
    let shifted: ComputationTerm = shift(a, run, 1, 0).unwrap().try_into().unwrap();
    let ComputationTermForm::Run { accessibility, .. } = a.read(shifted).form else {
        panic!()
    };
    let PropTermForm::IdRefl { element } = a.read(accessibility).form else {
        panic!()
    };
    assert!(matches!(
        a.read(element).form,
        SetTermForm::Bound { index: 1 }
    ));

    let parameter = 0;
    let reflected_parameter = a.alloc(SetTermNode {
        level: 0,
        form: SetTermForm::ReflectedAmbient { level: parameter },
    });
    let proof = a.alloc(PropTermNode {
        form: PropTermForm::IdRefl {
            element: reflected_parameter,
        },
    });
    let result: PropTerm = substitute_ambient(
        &env,
        proof.into(),
        &std::collections::HashMap::from([(parameter, zero.into())]),
    )
    .unwrap()
    .try_into()
    .unwrap();
    assert_eq!(
        a.read(result).form,
        PropTermForm::IdRefl {
            element: reflect_term(&env, zero.into()).unwrap()
        }
    );
}
#[test]
fn kind_valued_recursor_preserves_the_lower_result_level() {
    let env = Environment::new();
    let a = &env.arena;
    let b_kind = sk(a, 0);
    let a_kind = sk(a, 2);
    let a_var = a.alloc(SetTypeNode {
        level: 2,
        form: SetTypeForm::Bound { index: 0 },
    });
    let context = vec![
        Binding {
            var: SymbolId(1),
            classifier: b_kind.into(),
        },
        Binding {
            var: SymbolId(2),
            classifier: a_kind.into(),
        },
        Binding {
            var: SymbolId(3),
            classifier: a_var.into(),
        },
    ];
    let state = a.alloc(SetTypeNode {
        level: 2,
        form: SetTypeForm::Bound { index: 1 },
    });
    let value = a.alloc(SetTermNode {
        level: 2,
        form: SetTermForm::Bound { index: 0 },
    });
    let b = a.alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::Bound { index: 2 },
    });
    let nested_b = a.alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::Bound { index: 3 },
    });
    let rule =
        ProductRule::new(Sort::Base(BaseSort::Set(2)), Sort::Upper(BaseSort::Set(0))).unwrap();
    let branch = a.alloc(SetTypeNode {
        level: 2,
        form: SetTypeForm::LambdaTerm {
            rule,
            var: SymbolId(4),
            domain: state,
            body: nested_b,
        },
    });
    let scrutinee = a.alloc(SetTermNode {
        level: 2,
        form: SetTermForm::Continue {
            state_ty: state,
            result_ty: state,
            next: value,
        },
    });
    let rec = a.alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::Recursor {
            rule,
            var: SymbolId(4),
            state_ty: state,
            result_ty: state,
            motive: b_kind,
            on_continue: branch,
            on_finish: branch,
            scrutinee,
        },
    });
    let mut checker = Checker::new(&env, context);
    checker.infer_set_type(rec).unwrap();
    let reduced = normalize(&env, rec).unwrap();
    assert!(convertible(&env, reduced, b.into()).unwrap());
    checker.inferred(reduced).unwrap();
}
#[test]
fn public_checker_validates_context_and_named_definitions_cannot_capture_locals() {
    let mut env = Environment::new();
    let (_, ty, _) = natural(&mut env);
    let a = &env.arena;
    let bad_ty = a.alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::Bound { index: 0 },
    });
    let term = a.alloc(SetTermNode {
        level: 0,
        form: SetTermForm::Bound { index: 0 },
    });
    assert!(
        Checker::new(
            &env,
            vec![Binding {
                var: SymbolId(1),
                classifier: bad_ty.into()
            }]
        )
        .infer_set_term(term)
        .is_err()
    );
    let value = a.alloc(ValueTermNode {
        level: 0,
        form: ValueTermForm::Bound { index: 0 },
    });
    let context = vec![Binding {
        var: SymbolId(1),
        classifier: ty.into(),
    }];
    let id = env.fresh_global_id();
    assert!(
        env.register_definition(
            id,
            Definition {
                context,
                body: value.into(),
                classifier: ty.into()
            }
        )
        .is_err()
    );
    assert!(env.definition(id).is_none());
}

#[test]
fn prop_proofs_have_their_own_family_and_beta_reduce() {
    let env = Environment::new();
    let a = env.arena();
    let set_kind = sk(a, 0);
    let carrier = a.alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::Bound { index: 0 },
    });
    let element = a.alloc(SetTermNode {
        level: 0,
        form: SetTermForm::Bound { index: 0 },
    });
    let context = vec![
        Binding {
            var: SymbolId::ANONYMOUS,
            classifier: set_kind.into(),
        },
        Binding {
            var: SymbolId::ANONYMOUS,
            classifier: carrier.into(),
        },
    ];
    let proposition_node = PropTypeNode {
        form: PropTypeForm::Equal {
            left: element,
            right: element,
        },
    };
    let proposition = a.alloc(proposition_node.clone());
    let proof_node = PropTermNode {
        form: PropTermForm::IdRefl { element },
    };
    let proof = a.alloc(proof_node.clone());
    assert_eq!(a.get(proposition), proposition_node);
    assert_eq!(a.get(proof), proof_node);
    assert_eq!(a.sort(proof), BaseSort::Prop);
    assert_eq!(Expression::from(proof).family(), Family::PropTerm);
    assert!(SetTerm::try_from(Expression::from(proof)).is_err());
    assert!(SetExpression::try_from(Expression::from(proof)).is_err());
    assert!(SetArgument::try_from(Expression::from(proof)).is_err());
    assert!(matches!(LogicalExpression::from(proof),
        LogicalExpression::Prop(PropExpression::PropTerm(h)) if h == proof));
    assert!(matches!(LogicalArgument::from(element),
        LogicalArgument::Set(SetArgument::SetTerm(h)) if h == element));
    assert!(PropTerm::try_from(Expression::from(element)).is_err());
    assert!(SetType::try_from(Expression::from(proposition)).is_err());

    let mut checker = Checker::new(&env, context);
    assert_eq!(checker.infer_prop_term(proof).unwrap(), proposition);
    let kind = checker.infer_prop_type(proposition).unwrap();
    assert_eq!(
        a.get(kind),
        PropKindNode {
            form: PropKindForm::Base
        }
    );
    checker.check_prop_kind(kind).unwrap();
    assert!(SetKind::try_from(Expression::from(kind)).is_err());

    let rule = ProductRule::new(Sort::Base(BaseSort::Prop), Sort::Base(BaseSort::Prop)).unwrap();
    let body = a.alloc(PropTermNode {
        form: PropTermForm::Bound { index: 0 },
    });
    let identity_node = PropTermNode {
        form: PropTermForm::LambdaTerm {
            rule,
            var: SymbolId::ANONYMOUS,
            domain: proposition.into(),
            body,
        },
    };
    let identity = a.alloc(identity_node.clone());
    assert_eq!(a.get(identity), identity_node);
    let application = a.alloc(PropTermNode {
        form: PropTermForm::AppTerm {
            rule,
            function: identity,
            argument: proof.into(),
        },
    });
    assert_eq!(checker.infer_prop_term(application).unwrap(), proposition);
    assert_eq!(normalize(&env, application).unwrap(), proof.into());
    assert!(checker.check(proof, carrier).is_err());
}

#[test]
fn prop_type_operators_quantify_over_set_and_prop_kinds() {
    let env = Environment::new();
    let a = env.arena();
    let set_kind = sk(a, 0);
    let prop_kind = a.alloc(PropKindNode {
        form: PropKindForm::Base,
    });
    let set = a.alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::Bound { index: 0 },
    });
    let proposition = a.alloc(PropTypeNode {
        form: PropTypeForm::Exists { set },
    });
    let set_rule =
        ProductRule::new(Sort::Upper(BaseSort::Set(0)), Sort::Upper(BaseSort::Prop)).unwrap();
    let predicate = a.alloc(PropTypeNode {
        form: PropTypeForm::LambdaType {
            rule: set_rule,
            var: SymbolId::ANONYMOUS,
            domain: set_kind.into(),
            body: proposition,
        },
    });
    let prop_rule =
        ProductRule::new(Sort::Upper(BaseSort::Prop), Sort::Upper(BaseSort::Prop)).unwrap();
    let bound_prop = a.alloc(PropTypeNode {
        form: PropTypeForm::Bound { index: 0 },
    });
    let identity = a.alloc(PropTypeNode {
        form: PropTypeForm::LambdaType {
            rule: prop_rule,
            var: SymbolId::ANONYMOUS,
            domain: prop_kind.into(),
            body: bound_prop,
        },
    });
    let mut checker = Checker::new(
        &env,
        vec![Binding {
            var: SymbolId::ANONYMOUS,
            classifier: set_kind.into(),
        }],
    );
    for operator in [predicate, identity] {
        let kind = checker.infer_prop_type(operator).unwrap();
        checker.check_prop_kind(kind).unwrap();
        assert_eq!(a.alloc(a.get(kind)), kind);
    }
    for (rule, function, argument) in [
        (set_rule, predicate, LogicalType::from(set)),
        (prop_rule, identity, LogicalType::from(proposition)),
    ] {
        let node = PropTypeNode {
            form: PropTypeForm::AppType {
                rule,
                function,
                argument,
            },
        };
        let application = a.alloc(node.clone());
        assert_eq!(a.get(application), node);
        assert_eq!(checker.infer_prop_type(application).unwrap(), prop_kind);
        assert_eq!(normalize(&env, application).unwrap(), proposition.into());
    }
}

#[test]
fn maximum_bound_index_is_rejected_without_overflow() {
    let env = Environment::new();
    let term = env.arena.alloc(SetTermNode {
        level: 0,
        form: SetTermForm::Bound { index: usize::MAX },
    });
    assert!(Checker::new(&env, vec![]).infer_set_term(term).is_err());
}

#[test]
fn reflected_ambient_variables_are_not_closed() {
    let env = Environment::new();
    let parameter = 0;
    let term = env.arena.alloc(ValueTermNode {
        level: 0,
        form: ValueTermForm::Ambient { level: parameter },
    });
    let reflected = reflect_term(&env, term.into()).unwrap();
    assert!(!is_closed(&env.arena, term.into()));
    assert!(!is_closed(&env.arena, reflected.into()));
    assert!(locally_closed(&env.arena, reflected.into()));
}

#[test]
fn annotations_are_shared_transparent_and_checked_without_definition_names() {
    let env = Environment::new();
    let kind = sk(&env.arena, 0);
    let classifier = Classifier::Upper(BaseSort::Set(0));
    let annotated = env.arena.annotated(kind.into(), classifier).unwrap();
    assert_eq!(
        annotated,
        env.arena.annotated(kind.into(), classifier).unwrap()
    );
    assert_eq!(
        Checker::new(&env, vec![]).infer(annotated).unwrap(),
        classifier
    );
    assert_eq!(whnf(&env, annotated).unwrap(), kind.into());
    assert!(convertible(&env, annotated, kind.into()).unwrap());
    let forged = env
        .arena
        .annotated(kind.into(), Classifier::Upper(BaseSort::Set(1)))
        .unwrap();
    assert!(Checker::new(&env, vec![]).infer(forged).is_err());
}

#[test]
fn annotations_preserve_the_declared_classifier_and_check_the_body() {
    let mut env = Environment::new();
    let (_, program_ty, _) = natural(&mut env);
    let ty = reflect_type(&env, program_ty.into()).unwrap();
    let power = env.arena.alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::PowerSet { set: ty },
    });
    let subset = 0;
    env.push_binding(Binding {
        var: SymbolId(1),
        classifier: power.into(),
    })
    .unwrap();
    let subset = env.arena.alloc(SetTermNode {
        level: 0,
        form: SetTermForm::Ambient { level: subset },
    });
    let refined = env.arena.alloc(SetTypeNode {
        level: 0,
        form: SetTypeForm::TypeLift {
            superset: ty,
            subset,
        },
    });
    let x = 1;
    env.push_binding(Binding {
        var: SymbolId(2),
        classifier: refined.into(),
    })
    .unwrap();
    let body = env.arena.alloc(SetTermNode {
        level: 0,
        form: SetTermForm::Ambient { level: x },
    });
    let annotated = env.arena.annotated(body.into(), ty.into()).unwrap();
    let mut checker = Checker::new(&env, vec![]);
    assert_eq!(checker.infer(body).unwrap(), refined.into());
    assert_eq!(checker.infer(annotated).unwrap(), ty.into());
    assert!(convertible(&env, annotated, body.into()).unwrap());
    // The family and universe match, but the body does not inhabit Power(ty).
    let forged = env.arena.annotated(body.into(), power.into()).unwrap();
    assert!(checker.infer(forged).is_err());
}

#[test]
fn substitution_visits_annotation_body_and_classifier() {
    let mut env = Environment::new();
    let (_, ty, zero) = natural(&mut env);
    let a = &env.arena;
    let type_parameter = a.alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::Bound { index: 1 },
    });
    let body = a.alloc(ValueTermNode {
        level: 0,
        form: ValueTermForm::Bound { index: 0 },
    });
    let annotation = a.annotated(body.into(), type_parameter.into()).unwrap();
    let shifted = shift(a, annotation, 1, 0).unwrap();
    let Expression::ValueTerm(h) = shifted else {
        panic!("value")
    };
    let ValueTermForm::Annotated {
        body: shifted_body,
        classifier: Classifier::Expression(shifted_type),
    } = a.get(h).form
    else {
        panic!("annotation")
    };
    assert!(matches!(
        a.get(shifted_body).form,
        ValueTermForm::Bound { index: 1 }
    ));
    let Expression::ValueType(shifted_type) = shifted_type else {
        panic!("type")
    };
    assert!(matches!(
        a.get(shifted_type).form,
        ValueTypeForm::Bound { index: 2 }
    ));
    let closed = instantiate_telescope(&env, annotation, &[ty.into(), zero.into()]).unwrap();
    assert_eq!(Checker::new(&env, vec![]).infer(closed).unwrap(), ty.into());
    assert!(convertible(&env, closed, zero.into()).unwrap());
}

#[test]
fn ambient_templates_instantiate_under_local_binders_and_reflect() {
    let mut env = Environment::new();
    let kind = vk(env.arena(), 0);
    let type_level = env
        .push_binding(Binding {
            var: SymbolId(1),
            classifier: kind.into(),
        })
        .unwrap();
    let ty = env.arena().alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::Ambient { level: type_level },
    });
    let value_level = env
        .push_binding(Binding {
            var: SymbolId(2),
            classifier: ty.into(),
        })
        .unwrap();
    let value = env.arena().alloc(ValueTermNode {
        level: 0,
        form: ValueTermForm::Ambient { level: value_level },
    });
    let id = env.fresh_global_id();
    env.register_definition_template(
        id,
        Definition {
            context: vec![Binding {
                var: SymbolId(3),
                classifier: kind.into(),
            }],
            body: value.into(),
            classifier: ty.into(),
        },
    )
    .unwrap();
    let caller_type = env.arena().alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::Bound { index: 1 },
    });
    let caller_value = env.arena().alloc(ValueTermNode {
        level: 0,
        form: ValueTermForm::Bound { index: 0 },
    });
    let local_type = env.arena().alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::Bound { index: 0 },
    });
    let context = vec![
        Binding {
            var: SymbolId(4),
            classifier: kind.into(),
        },
        Binding {
            var: SymbolId(5),
            classifier: local_type.into(),
        },
    ];
    let instance = env
        .instantiate_template(
            id,
            &std::collections::HashMap::from([
                (type_level, caller_type.into()),
                (value_level, caller_value.into()),
            ]),
            context,
        )
        .unwrap();
    let expected_body = env.arena().alloc(ValueTermNode {
        level: 0,
        form: ValueTermForm::Bound { index: 1 },
    });
    let expected_type = env.arena().alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::Bound { index: 2 },
    });
    assert_eq!(instance.body, expected_body.into());
    assert_eq!(instance.classifier, expected_type.into());
    assert_eq!(instance.context.len(), 3);
    let reflected = reflect_term(&env, instance.body.try_into().unwrap()).unwrap();
    let reflected_type = reflect_type(&env, expected_type.into()).unwrap();
    let context = crate::reflection::reflect_context(&env, &instance.context).unwrap();
    Checker::new(&env, context)
        .check(reflected, reflected_type)
        .unwrap();
    let (copy, map) = env.transfer().unwrap();
    let copied_id = map.globals[&id];
    assert_ne!(id, copied_id);
    drop(env);
    let definition = copy.definition_template(copied_id).unwrap();
    Checker::new(&copy, definition.context.clone())
        .check(definition.body, definition.classifier)
        .unwrap();
}

#[test]
fn foreign_handles_and_nominal_ids_fail_without_publishing() {
    let mut source = Environment::new();
    let (id, ty, _) = natural(&mut source);
    let mut target = Environment::new();
    assert!(Checker::new(&target, vec![]).infer(ty).is_err());
    assert!(
        target
            .register_datatype(id, source.datatype(id).unwrap().clone())
            .is_err()
    );
    let key = target.fresh_global_id();
    assert!(
        target
            .register_definition(
                key,
                Definition {
                    context: vec![],
                    body: ty.into(),
                    classifier: vk(source.arena(), 0).into(),
                }
            )
            .is_err()
    );
    assert!(
        target
            .push_binding(Binding {
                var: SymbolId(1),
                classifier: ty.into()
            })
            .is_err()
    );
    assert!(target.ambient_context().is_empty());
    assert!(target.definition(key).is_none());
    assert_eq!(target.declaration_node_count(), 0);
    let foreign_nominal = target.arena().alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::Inductive {
            inductive: id,
            parameters: vec![],
        },
    });
    assert!(
        Checker::new(&target, vec![])
            .infer(foreign_nominal)
            .is_err()
    );
    let circular = target.arena().alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::Ambient { level: 0 },
    });
    assert!(
        target
            .push_binding(Binding {
                var: SymbolId(1),
                classifier: circular.into()
            })
            .is_err()
    );
    assert!(target.ambient_context().is_empty());
    let level = target
        .push_binding(Binding {
            var: SymbolId(1),
            classifier: vk(target.arena(), 0).into(),
        })
        .unwrap();
    assert_eq!(level, 0);
    Checker::new(&target, vec![]).infer(circular).unwrap();
}

#[test]
fn interrupted_nominal_registration_rolls_back_and_can_be_retried() {
    use crate::control::{self, CancellationToken, Interrupted};
    let mut env = Environment::new();
    let id = env.fresh_inductive_id();
    let spec = InductiveSpec {
        parameters: vec![],
        arity: sk(env.arena(), 0).into(),
        constructors: vec![],
        sort: Sort::Base(BaseSort::Set(0)),
    };
    let interrupted = control::run(CancellationToken::default(), Some(1), || {
        env.register_inductive(id, spec.clone())
    });
    assert_eq!(interrupted, Err(Interrupted::ResourceLimit));
    assert!(env.inductive(id).is_none());
    env.register_inductive(id, spec).unwrap();
    let datatype = env.fresh_datatype_id();
    let mirror = env.fresh_inductive_id();
    let spec = ProgramDatatype {
        parameters: vec![],
        constructors: vec![vec![]],
        level: 0,
        reflected: mirror,
    };
    let interrupted = control::run(CancellationToken::default(), Some(2), || {
        env.register_datatype(datatype, spec.clone())
    });
    assert_eq!(interrupted, Err(Interrupted::ResourceLimit));
    assert!(env.datatype(datatype).is_none());
    assert!(env.inductive(mirror).is_none());
    env.register_datatype(datatype, spec).unwrap();
    let count = env.declaration_node_count();
    let interrupted = control::run(CancellationToken::default(), Some(4), || env.transfer());
    assert!(matches!(interrupted, Err(Interrupted::ResourceLimit)));
    assert_eq!(env.declaration_node_count(), count);
    let copied = env.transfer().unwrap().0;
    assert_eq!(copied.declaration_node_count(), count);
}
