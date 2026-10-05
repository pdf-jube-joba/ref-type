use crate::{
    calculus::instantiate,
    check::Checker,
    environment::Environment,
    ids::SymbolId,
    metavariables::{Constraint, Error, MetaContext, Outcome},
    sort::{BaseSort, Sort},
    syntax::{Binding, Context, Mode, Node},
};
fn context(env: &Environment) -> Context {
    vec![Binding {
        var: SymbolId::ANONYMOUS,
        ty: env.arena.sort(Sort::Base(BaseSort::Set(0))),
    }]
}

#[test]
fn strict_boundary_requires_solutions_in_term_context_and_expected() {
    let env = Environment::new();
    let mut metas = MetaContext::new();
    let ctx = context(&env);
    let a = env.arena.bound(0);
    let hole = metas.fresh(&env.arena, ctx.clone(), Some(a));
    assert!(matches!(
        Checker::new(&env, &mut metas, ctx.clone()).infer(hole),
        Err(Error::Unresolved { .. })
    ));
    let unknown = metas.fresh(&env.arena, vec![], Some(ctx[0].ty));
    let term = env.arena.alloc(Node::Lambda {
        mode: Mode::Pure,
        var: SymbolId::ANONYMOUS,
        domain: unknown,
        body: env.arena.bound(0),
    });
    assert!(matches!(
        Checker::new(&env, &mut metas, vec![]).infer(term),
        Err(Error::Unresolved { .. })
    ));
    assert!(matches!(metas.finish(&env), Err(Error::Unresolved { .. })));
}

#[test]
fn pattern_abstraction_supports_permuted_context_and_weakening() {
    let env = Environment::new();
    let mut metas = MetaContext::new();
    let mut ctx = context(&env);
    ctx.push(Binding {
        var: SymbolId::ANONYMOUS,
        ty: env.arena.bound(0),
    });
    let hole = metas.fresh(&env.arena, ctx.clone(), Some(env.arena.bound(1)));
    let Node::Meta { id, .. } = env.arena.get(hole) else {
        panic!()
    };
    let mut occurrence_context = context(&env);
    occurrence_context.push(Binding {
        var: SymbolId::ANONYMOUS,
        ty: env.arena.bound(0),
    });
    occurrence_context.push(Binding {
        var: SymbolId::ANONYMOUS,
        ty: env.arena.bound(1),
    });
    let occurrence = env.arena.alloc(Node::Meta {
        id,
        arguments: vec![env.arena.bound(2), env.arena.bound(0)],
    });
    assert_eq!(
        metas
            .unify(&env, &occurrence_context, occurrence, env.arena.bound(0))
            .unwrap(),
        Outcome::Solved
    );
    metas.finish(&env).unwrap();
    assert_eq!(metas.zonk(&env.arena, hole).unwrap(), env.arena.bound(0));
    assert_eq!(
        Checker::new(&env, &mut metas, occurrence_context)
            .infer(occurrence)
            .unwrap(),
        env.arena.bound(2)
    );
}

#[test]
fn assignment_type_and_scope_are_checked() {
    let env = Environment::new();
    let mut metas = MetaContext::new();
    let ctx = context(&env);
    let hole = metas.fresh(&env.arena, ctx.clone(), Some(env.arena.bound(0)));
    assert!(metas.unify(&env, &ctx, hole, env.arena.bound(1)).is_err());
    assert_eq!(
        metas.unify(&env, &ctx, hole, ctx[0].ty).unwrap(),
        Outcome::Solved
    );
    assert!(metas.finish(&env).is_err());
    assert!(Checker::new(&env, &mut metas, ctx).infer(hole).is_err());
}

#[test]
fn rollback_restores_solutions_and_invalidates_new_ids() {
    let env = Environment::new();
    let mut metas = MetaContext::new();
    let ctx = context(&env);
    let hole = metas.fresh(&env.arena, vec![], None);
    let snapshot = metas.snapshot();
    let doomed = metas.fresh(&env.arena, vec![], None);
    metas.unify(&env, &vec![], hole, ctx[0].ty).unwrap();
    metas.rollback(snapshot).unwrap();
    assert!(matches!(metas.finish(&env), Err(Error::Unresolved { .. })));
    assert!(matches!(
        metas.zonk(&env.arena, doomed),
        Err(Error::InvalidMeta(_))
    ));
    assert_eq!(metas.zonk(&env.arena, hole).unwrap(), hole);
}

#[test]
fn pending_type_constraint_solves_after_its_domain() {
    let env = Environment::new();
    let mut metas = MetaContext::new();
    let ctx = context(&env);
    let domain = metas.fresh(&env.arena, ctx.clone(), Some(ctx[0].ty));
    let term = env.arena.alloc(Node::Lambda {
        mode: Mode::Pure,
        var: SymbolId::ANONYMOUS,
        domain,
        body: env.arena.bound(0),
    });
    let ty = metas.infer(&env, ctx.clone(), term).unwrap();
    metas.unify(&env, &ctx, domain, env.arena.bound(0)).unwrap();
    metas.finish(&env).unwrap();
    let result = Checker::new(&env, &mut metas, ctx).infer(term).unwrap();
    assert_eq!(
        metas.zonk(&env.arena, ty).unwrap(),
        metas.zonk(&env.arena, result).unwrap()
    );
}

#[test]
fn indirect_occurs_check_and_orphan_obligations() {
    let env = Environment::new();
    let mut metas = MetaContext::new();
    let a = metas.fresh(&env.arena, vec![], None);
    let b = metas.fresh(&env.arena, vec![], None);
    metas.unify(&env, &vec![], a, b).unwrap();
    let product = env.arena.alloc(Node::Product {
        var: SymbolId::ANONYMOUS,
        domain: a,
        body: a,
    });
    assert!(metas.unify(&env, &vec![], b, product).is_err());
    let set = env.arena.sort(Sort::Base(BaseSort::Set(0)));
    metas.unify(&env, &vec![], b, set).unwrap();
    metas.constrain(Constraint::IsSort {
        context: vec![],
        term: env.arena.bound(0),
    });
    assert!(metas.finish(&env).is_err());
}

#[test]
fn instantiation_visits_proof_operands_and_every_branch() {
    let env = Environment::new();
    let mut metas = MetaContext::new();
    let hole = metas.fresh(&env.arena, vec![], None);
    let term = env.arena.alloc(Node::SubsetIntro {
        superset: env.arena.bound(0),
        subset: env.arena.bound(0),
        element: env.arena.bound(0),
        proof: hole,
    });
    let result = instantiate(
        &env.arena,
        term,
        &[env.arena.sort(Sort::Base(BaseSort::Prop))],
    )
    .unwrap();
    assert!(metas.require_solved(&env.arena, [result]).is_err());
}

#[test]
fn reflection_preserves_bound_and_outer_variables() {
    let env = Environment::new();
    let mut metas = MetaContext::new();
    let v = env.arena.sort(Sort::Base(BaseSort::Value(0)));
    let ctx = vec![Binding {
        var: SymbolId::ANONYMOUS,
        ty: v,
    }];
    let a = env.arena.bound(0);
    let body = env.arena.alloc(Node::Return {
        value: env.arena.bound(0),
    });
    let fun = env.arena.alloc(Node::Lambda {
        mode: Mode::Computation,
        var: SymbolId::ANONYMOUS,
        domain: a,
        body,
    });
    let reflected = env.arena.alloc(Node::Reflect { term: fun });
    let reduced = env.whnf(reflected).unwrap();
    let Node::Lambda { domain, body, .. } = env.arena.get(reduced) else {
        panic!()
    };
    assert_eq!(env.arena.get(domain), Node::Reflect { term: a });
    assert_eq!(body, env.arena.bound(0));
    let expected = Checker::new(&env, &mut metas, ctx.clone())
        .infer(reflected)
        .unwrap();
    Checker::new(&env, &mut metas, ctx)
        .check(reduced, expected)
        .unwrap();
    let full = env.reflect_bound(fun).unwrap();
    let Node::Lambda { domain, .. } = env.arena.get(full) else {
        panic!()
    };
    assert_eq!(domain, a);
}

use crate::{
    calculus::{alpha_equal, shift},
    environment::{Datatype, Definition},
    ids::{InductiveId, ProgramInductiveId},
    reduction,
    syntax::{Arena, Expression},
};
fn binding(ty: Expression) -> Binding {
    Binding {
        var: SymbolId::ANONYMOUS,
        ty,
    }
}
fn sort(a: &Arena, s: BaseSort) -> Expression {
    a.sort(Sort::Base(s))
}
fn lambda(a: &Arena, mode: Mode, domain: Expression, body: Expression) -> Expression {
    a.alloc(Node::Lambda {
        mode,
        var: SymbolId::ANONYMOUS,
        domain,
        body,
    })
}
fn product(a: &Arena, domain: Expression, body: Expression) -> Expression {
    a.alloc(Node::Product {
        var: SymbolId::ANONYMOUS,
        domain,
        body,
    })
}
fn apply(a: &Arena, mode: Mode, function: Expression, argument: Expression) -> Expression {
    a.alloc(Node::App {
        mode,
        function,
        argument,
    })
}
fn refine(a: &Arena, ty: Expression, value: Expression) -> Expression {
    a.alloc(Node::SubsetIntro {
        superset: ty,
        subset: a.alloc(Node::Subset {
            var: SymbolId::ANONYMOUS,
            set: ty,
            predicate: a.alloc(Node::Equal {
                left: a.bound(0),
                right: a.bound(0),
            }),
        }),
        element: value,
        proof: a.alloc(Node::IdRefl { element: value }),
    })
}

#[test]
fn refined_predicates_reduce_without_losing_typing_evidence() {
    let env = Environment::new();
    let a = &env.arena;
    let prop = sort(a, BaseSort::Prop);
    // A : Set, P : A -> Prop, x : A.
    let context = vec![
        binding(sort(a, BaseSort::Set(0))),
        binding(product(a, a.bound(0), prop)),
        binding(a.bound(1)),
    ];
    let powerset = a.alloc(Node::PowerSet { set: a.bound(2) });
    let bare = a.alloc(Node::Subset {
        var: SymbolId::ANONYMOUS,
        set: a.bound(2),
        predicate: apply(a, Mode::Pure, a.bound(2), a.bound(0)),
    });
    let refined = refine(a, powerset, bare);
    let mut metas = MetaContext::new();
    let mut checker = Checker::new(&env, &mut metas, context.clone());
    let refined_ty = checker.infer(refined).unwrap();
    assert!(matches!(a.get(refined_ty), Node::TypeLift { .. }));
    checker.check(refined, powerset).unwrap();
    assert!(checker.check(bare, refined_ty).is_err());
    assert!(!reduction::erased_convertible(&env, refined_ty, powerset).unwrap());

    let mut invalid = a.get(refined);
    let Node::SubsetIntro { proof, .. } = &mut invalid else {
        unreachable!()
    };
    *proof = a.alloc(Node::IdRefl {
        element: a.bound(0),
    });
    assert!(checker.infer(a.alloc(invalid)).is_err());

    let nested = refine(a, refined_ty, refined);
    checker.infer(nested).unwrap();
    let membership = |subset, element| {
        a.alloc(Node::Pred {
            superset: a.bound(2),
            subset,
            element,
        })
    };
    let expected = apply(a, Mode::Pure, a.bound(1), a.bound(0));
    let bare_pred = membership(bare, a.bound(0));
    let nested_pred = membership(nested, a.bound(0));
    for left in [expected, bare_pred, nested_pred] {
        for right in [expected, bare_pred, nested_pred] {
            assert!(reduction::erased_convertible(&env, left, right).unwrap());
        }
        assert_eq!(env.whnf(left).unwrap(), expected);
        assert_eq!(reduction::normalize(&env, left).unwrap(), expected);
    }

    // The same reduction must expose a contextual hole to unification.
    let element = metas.fresh(a, context.clone(), Some(a.bound(2)));
    assert_eq!(
        metas
            .unify(&env, &context, membership(nested, element), expected)
            .unwrap(),
        Outcome::Solved
    );
    metas.finish(&env).unwrap();
    assert_eq!(metas.zonk(a, element).unwrap(), a.bound(0));

    // Expected propositions propagate through a lambda with an inferred domain.
    let domain = metas.fresh(a, context.clone(), Some(prop));
    let identity = lambda(a, Mode::Pure, domain, a.bound(0));
    let expected_ty = product(a, expected, shift(a, nested_pred, 1, 0).unwrap());
    metas
        .check(&env, context.clone(), identity, expected_ty)
        .unwrap();
    metas.finish(&env).unwrap();
    Checker::new(&env, &mut metas, context)
        .check(identity, expected_ty)
        .unwrap();
}

#[test]
fn refined_function_and_reflected_case_normalize() {
    let mut env = Environment::new();
    let (id, program_ty, zero) = natural(&mut env);
    let a = &env.arena;
    let ty = env.reflect_bound(program_ty).unwrap();
    let zero = env.reflect_bound(zero).unwrap();
    let mut metas = MetaContext::new();
    let identity = lambda(a, Mode::Pure, ty, a.bound(0));
    let identity_ty = Checker::new(&env, &mut metas, vec![])
        .infer(identity)
        .unwrap();
    let applied = apply(a, Mode::Pure, refine(a, identity_ty, identity), zero);
    let case = a.alloc(Node::SetCase {
        inductive: id,
        binders: vec![vec![], vec![SymbolId::ANONYMOUS]],
        scrutinee: a.alloc(Node::Ascribe {
            term: refine(a, ty, zero),
            ty,
        }),
        branches: vec![zero, a.bound(0)],
    });
    for term in [applied, case] {
        Checker::new(&env, &mut metas, vec![])
            .check(term, ty)
            .unwrap();
        assert_eq!(env.whnf(term).unwrap(), env.whnf(zero).unwrap());
        assert_eq!(
            reduction::normalize(&env, term).unwrap(),
            reduction::normalize(&env, zero).unwrap()
        );
    }
}

fn natural(env: &mut Environment) -> (ProgramInductiveId, Expression, Expression) {
    let id = ProgramInductiveId(0);
    let reflected = InductiveId(0);
    let ty = env.arena.alloc(Node::Inductive {
        inductive: id,
        parameters: vec![],
    });
    env.register_datatype(
        id,
        Datatype {
            parameters: vec![],
            level: 0,
            constructors: vec![vec![], vec![binding(ty)]],
            reflected,
        },
    )
    .unwrap();
    let zero = env.arena.alloc(Node::InductiveConstructor {
        inductive: id,
        constructor: 0,
        parameters: vec![],
        fields: vec![],
    });
    (id, ty, zero)
}
#[test]
fn arena_interning_read_snapshots_and_closed_dag_sharing() {
    let a = Arena::new();
    let set = sort(&a, BaseSort::Set(0));
    let e = product(&a, set, set);
    let read = a.read(e);
    assert_eq!(e, product(&a, set, set));
    assert_eq!(shift(&a, e, 123, 0).unwrap(), e);
    assert_eq!(instantiate(&a, e, &[set]).unwrap(), e);
    assert_eq!(*read, a.get(e));
    assert_eq!(a.max_loose_bound(e), None);
}
#[test]
fn simultaneous_substitution_and_batched_application_preserve_sharing() {
    let env = Environment::new();
    let a = &env.arena;
    let set = sort(a, BaseSort::Set(0));
    let body = lambda(a, Mode::Pure, set, a.bound(1));
    let fun = lambda(a, Mode::Pure, set, body);
    let partial = apply(a, Mode::Pure, fun, a.bound(2));
    let full = apply(a, Mode::Pure, partial, a.bound(4));
    let expected = lambda(a, Mode::Pure, set, a.bound(3));
    let count = a.len();
    assert_eq!(env.whnf(full).unwrap(), a.bound(2));
    assert_eq!(env.whnf(partial).unwrap(), expected);
    assert_eq!(a.len(), count);
    let body = apply(a, Mode::Pure, a.bound(1), a.bound(0));
    let expected = apply(a, Mode::Pure, a.bound(0), a.bound(1));
    assert_eq!(
        instantiate(a, body, &[a.bound(0), a.bound(1)]).unwrap(),
        expected
    );
}

#[test]
fn identity_substitution_respects_inner_binders_and_outer_free_variables() {
    use crate::calculus::instantiate_at;
    let a = Arena::new();
    let set = sort(&a, BaseSort::Set(0));
    let term = lambda(&a, Mode::Pure, a.bound(1), a.bound(2));
    let identity = [a.bound(1), a.bound(0)];
    assert_eq!(instantiate(&a, term, &identity).unwrap(), term);
    assert_eq!(instantiate_at(&a, term, &[a.bound(0)], 1).unwrap(), term);
    assert_eq!(
        instantiate_at(&a, a.bound(0), &[set], 1).unwrap(),
        a.bound(0)
    );
    // The same argument list removes variables outside the replaced telescope.
    assert_eq!(instantiate(&a, a.bound(3), &identity).unwrap(), a.bound(1));
    assert_eq!(
        instantiate_at(&a, a.bound(3), &identity, 1).unwrap(),
        a.bound(1)
    );
    let permutation = [a.bound(0), a.bound(1)];
    assert_eq!(
        instantiate(&a, term, &permutation).unwrap(),
        lambda(&a, Mode::Pure, a.bound(0), a.bound(1))
    );
}

#[test]
fn shared_substitution_respects_telescope_length_and_argument_order() {
    let env = Environment::new();
    let a = env.arena();
    let body = lambda(a, Mode::Pure, a.bound(1), a.bound(2));
    let expected = lambda(a, Mode::Pure, a.bound(4), a.bound(5));
    assert_eq!(
        env.instantiate(body, &[a.bound(4), a.bound(3)]).unwrap(),
        expected
    );
    assert_eq!(
        env.instantiate(body, &[a.bound(5), a.bound(4), a.bound(3)])
            .unwrap(),
        expected
    );
    assert_eq!(env.shifted(body, 3).unwrap(), expected);
    assert_eq!(
        env.instantiate(a.bound(2), &[a.bound(4), a.bound(3)])
            .unwrap(),
        a.bound(0)
    );
    assert_eq!(
        env.instantiate(body, &[a.bound(3), a.bound(4)]).unwrap(),
        lambda(a, Mode::Pure, a.bound(3), a.bound(4))
    );
}

#[test]
fn shared_instantiations_distinguish_arguments_and_reclaim_scratch_keys() {
    use crate::calculus::Instantiations;
    let a = Arena::new();
    let mut substitutions = Instantiations::default();
    let body = a.alloc(Node::IdRefl {
        element: a.bound(0),
    });
    let set = sort(&a, BaseSort::Set(0));
    let prop = sort(&a, BaseSort::Prop);
    let stable = substitutions.apply(&a, body, &[set]).unwrap();
    assert_eq!(substitutions.apply(&a, body, &[set]).unwrap(), stable);
    let stable_entries = substitutions.len();
    assert!(stable_entries > 0);
    for argument in [prop, set, prop] {
        let mark = a.scratch_mark();
        let cache_mark = substitutions.begin_scratch();
        let temporary = lambda(&a, Mode::Pure, argument, a.bound(0));
        let result = substitutions.apply(&a, body, &[temporary]).unwrap();
        assert_eq!(a.get(result), Node::IdRefl { element: temporary });
        a.finish_scratch(mark, []);
        substitutions.finish_scratch(&a, cache_mark);
        assert!(!a.is_live(result));
        assert_eq!(substitutions.len(), stable_entries);
        assert_eq!(substitutions.apply(&a, body, &[set]).unwrap(), stable);
    }
    let nested = product(&a, body, body);
    let expected = product(&a, stable, body);
    assert_eq!(substitutions.apply(&a, nested, &[set]).unwrap(), expected);
}

#[test]
fn binder_traversal_includes_motives_annotations_and_proofs() {
    let a = Arena::new();
    let set = sort(&a, BaseSort::Set(0));
    let motive = lambda(
        &a,
        Mode::Pure,
        a.bound(0),
        lambda(&a, Mode::Pure, a.bound(1), a.bound(2)),
    );
    let e = a.alloc(Node::Case {
        inductive: InductiveId(0),
        scrutinee: a.bound(0),
        motive,
        branches: vec![a.bound(0)],
    });
    let e = instantiate(&a, e, &[set]).unwrap();
    assert_eq!(a.max_loose_bound(e), None);
    let Node::Case { motive, .. } = a.get(e) else {
        panic!()
    };
    let Node::Lambda { domain, body, .. } = a.get(motive) else {
        panic!()
    };
    assert_eq!(domain, set);
    let Node::Lambda { domain, body, .. } = a.get(body) else {
        panic!()
    };
    assert_eq!(domain, set);
    assert_eq!(body, set);
}
#[test]
fn definitions_keep_identity_declared_types_and_explicit_context_arguments() {
    let mut env = Environment::new();
    let a = env.arena.clone();
    let set = sort(&a, BaseSort::Set(0));
    let mut metas = MetaContext::new();
    let definition = Definition {
        context: vec![binding(set), binding(a.bound(0))],
        ty: a.bound(1),
        body: a.bound(0),
    };
    let first = env
        .register_definition(&mut metas, definition.clone())
        .unwrap();
    let second = env.register_definition(&mut metas, definition).unwrap();
    assert_ne!(first, second);
    let ctx = vec![binding(set), binding(a.bound(0))];
    let args = vec![a.bound(1), a.bound(0)];
    let x = env.reference(first, args.clone()).unwrap();
    let y = env.reference(second, args).unwrap();
    assert_eq!(
        Checker::new(&env, &mut metas, ctx).infer(x).unwrap(),
        a.bound(1)
    );
    assert!(reduction::convertible(&env, x, y).unwrap());
    assert_eq!(env.whnf(x).unwrap(), a.bound(0));
    let wrong = env.reference(first, vec![set, set]).unwrap();
    assert!(Checker::new(&env, &mut metas, vec![]).infer(wrong).is_err());
    let foreign = Environment::with_arena(a.clone());
    assert!(foreign.definition(first).is_err());
}
#[test]
fn registration_checks_contexts_and_preserves_type_errors() {
    let mut env = Environment::new();
    let a = env.arena.clone();
    let set = sort(&a, BaseSort::Set(0));
    let prop = sort(&a, BaseSort::Prop);
    let mut metas = MetaContext::new();
    let bad = Definition {
        context: vec![],
        ty: prop,
        body: set,
    };
    assert!(env.register_definition(&mut metas, bad).is_err());
    let bad = Definition {
        context: vec![binding(a.bound(0))],
        ty: a.bound(0),
        body: a.bound(0),
    };
    assert!(env.register_definition(&mut metas, bad).is_err());
    let error = Checker::new(&env, &mut metas, vec![])
        .check(set, prop)
        .unwrap_err();
    let Error::TypeMismatch(error) = error else {
        panic!()
    };
    assert_eq!(
        error.arena.get(error.term),
        Node::Sort(Sort::Base(BaseSort::Set(0)))
    );
    assert!(
        Checker::new(&env, &mut metas, vec![])
            .infer(a.bound(usize::MAX))
            .is_err()
    );
}
#[test]
fn polymorphic_program_identity_reflects_with_its_definition_arguments() {
    let mut env = Environment::new();
    let a = env.arena.clone();
    let v = sort(&a, BaseSort::Value(0));
    let mut metas = MetaContext::new();
    let body = lambda(
        &a,
        Mode::Computation,
        a.bound(0),
        a.alloc(Node::Return { value: a.bound(0) }),
    );
    let ty = product(
        &a,
        a.bound(0),
        a.alloc(Node::ReturnType {
            value_ty: a.bound(1),
        }),
    );
    let id = env
        .register_definition(
            &mut metas,
            Definition {
                context: vec![binding(v)],
                ty,
                body,
            },
        )
        .unwrap();
    let e = env.reference(id, vec![a.bound(0)]).unwrap();
    let r = env.reflect_bound(e).unwrap();
    let Node::Definition { id: rid, arguments } = a.get(r) else {
        panic!()
    };
    assert_eq!(Some(rid), env.reflected_definition(id));
    assert_eq!(arguments, vec![a.bound(0)]);
    let reflected_ctx = vec![binding(sort(&a, BaseSort::Set(0)))];
    Checker::new(&env, &mut metas, reflected_ctx)
        .infer(r)
        .unwrap();
    assert!(alpha_equal(
        &a,
        env.whnf(r).unwrap(),
        env.reflect_bound(body).unwrap()
    ));
}
#[test]
fn datatype_registration_reflection_and_positivity_are_checked() {
    let mut env = Environment::new();
    let (id, ty, zero) = natural(&mut env);
    let a = env.arena.clone();
    let mut metas = MetaContext::new();
    let succ = a.alloc(Node::InductiveConstructor {
        inductive: id,
        constructor: 1,
        parameters: vec![],
        fields: vec![zero],
    });
    Checker::new(&env, &mut metas, vec![])
        .check(succ, ty)
        .unwrap();
    Checker::new(&env, &mut metas, vec![])
        .check(
            env.reflect_bound(succ).unwrap(),
            env.reflect_bound(ty).unwrap(),
        )
        .unwrap();
    assert_eq!(env.inductive(InductiveId(0)).unwrap().constructors.len(), 2);
    let bad_id = ProgramInductiveId(1);
    let own = a.alloc(Node::Inductive {
        inductive: bad_id,
        parameters: vec![],
    });
    let negative = a.alloc(Node::Thunk {
        computation_ty: product(&a, own, a.alloc(Node::ReturnType { value_ty: own })),
    });
    assert!(
        env.register_datatype(
            bad_id,
            Datatype {
                parameters: vec![],
                level: 0,
                constructors: vec![vec![binding(negative)]],
                reflected: InductiveId(1)
            }
        )
        .is_err()
    );
    assert!(env.datatype(bad_id).is_none());
    assert!(env.inductive(InductiveId(1)).is_none());
    let operator = lambda(&a, Mode::Pure, sort(&a, BaseSort::Value(0)), a.bound(0));
    let positive = apply(&a, Mode::Pure, operator, own);
    env.register_datatype(
        bad_id,
        Datatype {
            parameters: vec![],
            level: 0,
            constructors: vec![vec![binding(positive)]],
            reflected: InductiveId(1),
        },
    )
    .unwrap();
}
#[test]
fn box_closedness_checks_definition_arguments_before_reduction() {
    let mut env = Environment::new();
    let (_, ty, _) = natural(&mut env);
    let a = env.arena.clone();
    let mut metas = MetaContext::new();
    let id = env
        .register_definition(
            &mut metas,
            Definition {
                context: vec![binding(ty)],
                ty,
                body: a.bound(0),
            },
        )
        .unwrap();
    let open = env.reference(id, vec![a.bound(0)]).unwrap();
    let computation = a.alloc(Node::Return { value: open });
    let computation_ty = a.alloc(Node::ReturnType { value_ty: ty });
    let boxed = a.alloc(Node::BoxProgram {
        program_ty: computation_ty,
        program: computation,
    });
    assert!(
        Checker::new(&env, &mut metas, vec![binding(ty)])
            .infer(boxed)
            .is_err()
    );
    assert_eq!(env.whnf(open).unwrap(), a.bound(0));
}
#[test]
fn program_evaluation_checks_certificates_and_preserves_the_result_type() {
    let mut env = Environment::new();
    let (_, ty, zero) = natural(&mut env);
    let a = env.arena.clone();
    let mut metas = MetaContext::new();
    let finish = a.alloc(Node::ProgramFinish {
        state_ty: ty,
        result_ty: ty,
        output: zero,
    });
    let returned = a.alloc(Node::Return { value: finish });
    let step = a.alloc(Node::ThunkValue {
        computation: lambda(&a, Mode::Computation, ty, returned),
    });
    let proof_ty = crate::termination::termination(
        &a,
        env.reflect_bound(ty).unwrap(),
        env.reflect_bound(ty).unwrap(),
        env.reflect_bound(step).unwrap(),
        env.reflect_bound(zero).unwrap(),
    )
    .unwrap();
    let ctx = vec![binding(proof_ty)];
    let mut run = a.alloc(Node::Run {
        state_ty: ty,
        result_ty: ty,
        step,
        initial: zero,
        accessibility: a.bound(0),
    });
    let expected = Checker::new(&env, &mut metas, ctx.clone())
        .infer(run)
        .unwrap();
    let bad = a.alloc(Node::Run {
        state_ty: ty,
        result_ty: ty,
        step,
        initial: zero,
        accessibility: zero,
    });
    assert!(
        Checker::new(&env, &mut metas, ctx.clone())
            .infer(bad)
            .is_err()
    );
    for _ in 0..8 {
        Checker::new(&env, &mut metas, ctx.clone())
            .check(run, expected)
            .unwrap();
        match reduction::reduce_once(&env, run).unwrap() {
            Some(next) => run = next,
            None => break,
        }
    }
    assert_eq!(run, a.alloc(Node::Return { value: zero }));
}
#[test]
fn definition_congruence_solves_arguments_and_constant_bodies_ignore_them() {
    let mut env = Environment::new();
    let a = env.arena.clone();
    let set = sort(&a, BaseSort::Set(0));
    let mut metas = MetaContext::new();
    let id = env
        .register_definition(
            &mut metas,
            Definition {
                context: vec![binding(set)],
                ty: set,
                body: a.bound(0),
            },
        )
        .unwrap();
    let ctx = vec![binding(set)];
    let hole = metas.fresh(&a, ctx.clone(), Some(set));
    let x = env.reference(id, vec![hole]).unwrap();
    let y = env.reference(id, vec![a.bound(0)]).unwrap();
    assert_eq!(metas.unify(&env, &ctx, x, y).unwrap(), Outcome::Solved);
    metas.finish(&env).unwrap();
    assert_eq!(metas.zonk(&a, hole).unwrap(), a.bound(0));
    let ctx = vec![binding(set), binding(set)];
    let constant = env
        .register_definition(
            &mut MetaContext::new(),
            Definition {
                context: ctx.clone(),
                ty: set,
                body: a.bound(1),
            },
        )
        .unwrap();
    let x = env
        .reference(constant, vec![a.bound(1), a.bound(0)])
        .unwrap();
    let y = env
        .reference(constant, vec![a.bound(1), a.bound(1)])
        .unwrap();
    assert!(reduction::convertible(&env, x, y).unwrap());
}

#[test]
fn unification_checks_occurrence_arguments_and_extends_binder_contexts() {
    let env = Environment::new();
    let a = &env.arena;
    let set = sort(a, BaseSort::Set(0));
    let mut metas = MetaContext::new();
    let ctx = vec![binding(set), binding(a.bound(0))];
    let hole = metas.fresh(a, ctx.clone(), Some(a.bound(1)));
    let left = lambda(a, Mode::Pure, set, lambda(a, Mode::Pure, a.bound(0), hole));
    let right = lambda(
        a,
        Mode::Pure,
        set,
        lambda(a, Mode::Pure, a.bound(0), a.bound(0)),
    );
    metas.unify(&env, &vec![], left, right).unwrap();
    metas.finish(&env).unwrap();
    assert!(crate::calculus::alpha_equal(
        a,
        metas.zonk(a, left).unwrap(),
        right
    ));
    let Node::Meta { id, .. } = a.get(hole) else {
        unreachable!()
    };
    let invalid = a.alloc(Node::Meta {
        id,
        arguments: vec![set, a.bound(0)],
    });
    assert!(metas.unify(&env, &ctx, invalid, a.bound(0)).is_err());
}

#[test]
fn reflection_constraints_resume_and_rollback_invalidates_session_caches() {
    let mut env = Environment::new();
    let (_, ty, zero) = natural(&mut env);
    let a = env.arena.clone();
    let mut metas = MetaContext::new();
    let hole = metas.fresh(&a, vec![], Some(ty));
    let reflected = a.alloc(Node::Reflect { term: hole });
    let expected = env.reflect_bound(zero).unwrap();
    assert_eq!(
        metas.unify(&env, &vec![], reflected, expected).unwrap(),
        Outcome::Blocked
    );
    let snapshot = metas.snapshot();
    metas.unify(&env, &vec![], hole, zero).unwrap();
    metas.finish(&env).unwrap();
    assert!(
        crate::reduction::erased_convertible(&env, metas.zonk(&a, reflected).unwrap(), expected)
            .unwrap()
    );
    metas.rollback(snapshot).unwrap();
    assert!(matches!(
        Checker::new(&env, &mut metas, vec![]).infer(reflected),
        Err(Error::Unresolved { .. })
    ));
    assert!(matches!(metas.finish(&env), Err(Error::Unresolved { .. })));
}

#[test]
fn registration_reclaims_scratch_nodes_and_keeps_definitions_and_error_terms() {
    let mut env = Environment::new();
    let a = env.arena.clone();
    let set = sort(&a, BaseSort::Set(0));
    let body = lambda(&a, Mode::Pure, set, a.bound(0));
    let ty = a.alloc(Node::Product {
        var: SymbolId(91),
        domain: set,
        body: set,
    });
    let before = a.len();
    let snapshot = a.read(body);
    let id = env
        .register_definition(
            &mut MetaContext::new(),
            Definition {
                context: vec![],
                ty,
                body,
            },
        )
        .unwrap();
    assert_eq!(a.len(), before);
    assert_eq!(*snapshot, a.get(body));
    // Inference must recompute a type reclaimed with the registration's scratch nodes.
    let inferred = Checker::new(&env, &mut MetaContext::new(), vec![])
        .infer(body)
        .unwrap();
    assert!(crate::calculus::alpha_equal(&a, inferred, ty));
    let reference = env.reference(id, vec![]).unwrap();
    let inferred = Checker::new(&env, &mut MetaContext::new(), vec![])
        .infer(reference)
        .unwrap();
    assert_eq!(inferred, ty);
    let error = env
        .register_definition(
            &mut MetaContext::new(),
            Definition {
                context: vec![],
                ty: set,
                body,
            },
        )
        .unwrap_err();
    let Error::TypeMismatch(error) = error else {
        panic!("expected retained type error")
    };
    assert!(matches!(
        error.arena.get(error.inferred),
        Node::Product { .. }
    ));
    assert_eq!(error.arena.get(error.term), a.get(body));
}

#[test]
fn registration_reclaims_temporary_contexts_without_reusing_stale_types() {
    let mut env = Environment::new();
    let a = env.arena.clone();
    let set = sort(&a, BaseSort::Set(0));
    let prop = sort(&a, BaseSort::Prop);
    let outer = vec![binding(sort(&a, BaseSort::Set(1)))];
    let body = lambda(&a, Mode::Pure, set, a.bound(1));
    let mut metas = MetaContext::new();
    let expected = Checker::new(&env, &mut metas, outer.clone())
        .infer(body)
        .unwrap();
    for binding_ty in [set, prop, set, prop] {
        let ty = a.alloc(Node::Product {
            var: SymbolId::ANONYMOUS,
            domain: set,
            body: binding_ty,
        });
        let contexts = env.contexts.borrow().len();
        let id = env
            .register_definition(
                &mut metas,
                Definition {
                    context: vec![binding(binding_ty)],
                    ty,
                    body,
                },
            )
            .unwrap();
        assert_eq!(env.contexts.borrow().len(), contexts);
        let reference = env.reference(id, vec![a.bound(0)]).unwrap();
        assert_eq!(
            Checker::new(&env, &mut metas, vec![binding(binding_ty)])
                .infer(reference)
                .unwrap(),
            ty
        );
        assert_eq!(
            Checker::new(&env, &mut metas, outer.clone())
                .infer(body)
                .unwrap(),
            expected
        );
    }
}

#[test]
fn inference_restores_outer_context_after_successful_and_failed_binders() {
    let env = Environment::new();
    let a = &env.arena;
    let set = sort(a, BaseSort::Set(0));
    let prop = sort(a, BaseSort::Prop);
    let ctx = vec![binding(set), binding(a.bound(0))];
    let mut metas = MetaContext::new();
    let mut checker = Checker::new(&env, &mut metas, ctx.clone());
    for domain in [set, prop] {
        let term = lambda(a, Mode::Pure, domain, a.bound(0));
        let ty = checker.infer(term).unwrap();
        assert!(
            matches!(a.get(ty), Node::Product { domain: actual, body, .. }
            if actual == domain && body == domain)
        );
        assert_eq!(checker.infer(a.bound(0)).unwrap(), a.bound(1));
    }
    let bad = lambda(
        a,
        Mode::Pure,
        set,
        apply(a, Mode::Pure, a.bound(0), a.bound(0)),
    );
    assert!(checker.infer(bad).is_err());
    assert_eq!(checker.context(), &ctx);
    assert_eq!(checker.infer(a.bound(0)).unwrap(), a.bound(1));
}

#[test]
fn kind_valued_step_match_retains_its_result_universe() {
    let env = Environment::new();
    let a = &env.arena;
    let mut metas = MetaContext::new();
    let small = sort(a, BaseSort::Set(0));
    let large = sort(a, BaseSort::Set(2));
    let ctx = vec![binding(small), binding(large), binding(a.bound(0))];
    let state = a.bound(1);
    let step = a.alloc(Node::RunStep {
        state_ty: state,
        result_ty: state,
    });
    let motive = lambda(a, Mode::Pure, step, small);
    let branch = lambda(a, Mode::Pure, state, a.bound(3));
    let scrutinee = a.alloc(Node::Continue {
        state_ty: state,
        result_ty: state,
        next: a.bound(0),
    });
    let function = a.alloc(Node::SetStepMatch {
        state_ty: state,
        result_ty: state,
        motive,
        on_continue: branch,
        on_finish: branch,
    });
    let rec = a.alloc(Node::App {
        mode: Mode::Pure,
        function,
        argument: scrutinee,
    });
    let function_ty = Checker::new(&env, &mut metas, ctx.clone())
        .infer(function)
        .unwrap();
    let Node::Product { domain, .. } = a.get(function_ty) else {
        panic!("step match must have a function type")
    };
    assert!(crate::reduction::convertible(&env, domain, step).unwrap());
    let ty = Checker::new(&env, &mut metas, ctx).infer(rec).unwrap();
    assert!(crate::reduction::convertible(&env, ty, small).unwrap());
    assert!(crate::reduction::convertible(&env, rec, a.bound(2)).unwrap());
}

#[test]
fn closed_polymorphic_box_applies_types_then_values() {
    let env = Environment::new();
    let a = &env.arena;
    let mut metas = MetaContext::new();
    let identity = |level| {
        lambda(
            a,
            Mode::Computation,
            sort(a, BaseSort::Value(level)),
            lambda(
                a,
                Mode::Computation,
                a.bound(0),
                a.alloc(Node::Return { value: a.bound(0) }),
            ),
        )
    };
    let id0 = identity(0);
    let id1 = identity(1);
    let ty0 = Checker::new(&env, &mut metas, vec![]).infer(id0).unwrap();
    let ty1 = Checker::new(&env, &mut metas, vec![]).infer(id1).unwrap();
    let boxed = a.alloc(Node::BoxProgram {
        program_ty: ty1,
        program: id1,
    });
    let arg_ty = a.alloc(Node::Thunk {
        computation_ty: ty0,
    });
    let applied = a.alloc(Node::BoxTypeApp {
        function: a.alloc(Node::Ascribe {
            term: refine(a, a.alloc(Node::BoxType { program_ty: ty1 }), boxed),
            ty: a.alloc(Node::BoxType { program_ty: ty1 }),
        }),
        argument: arg_ty,
    });
    let arg = a.alloc(Node::ThunkValue { computation: id0 });
    let result_ty = a.alloc(Node::ReturnType { value_ty: arg_ty });
    let boxed_arg = a.alloc(Node::BoxProgram {
        program_ty: result_ty,
        program: a.alloc(Node::Return { value: arg }),
    });
    let app = a.alloc(Node::BoxApp {
        function: applied,
        argument: boxed_arg,
    });
    let force = a.alloc(Node::ForceBox {
        program_ty: result_ty,
        boxed: app,
    });
    Checker::new(&env, &mut metas, vec![]).infer(force).unwrap();
    let reflected = env.reflect_bound(arg).unwrap();
    assert!(crate::reduction::convertible(&env, force, reflected).unwrap());
    let normal = crate::reduction::normalize(&env, force).unwrap();
    Checker::new(&env, &mut metas, vec![])
        .infer(normal)
        .unwrap();
}

#[test]
fn product_signature_and_overflow_cover_all_program_relations() {
    use BaseSort::*;
    use Sort::{Base as B, Upper as U};
    for domain in [Value(2), Computation(2)] {
        assert_eq!(
            U(domain).product(B(Computation(1))),
            Some(B(Computation(3)))
        );
        assert_eq!(U(domain).product(U(Value(1))), Some(U(Value(2))));
        assert_eq!(
            U(domain).product(U(Computation(3))),
            Some(U(Computation(3)))
        );
        assert_eq!(U(domain).product(B(Value(0))), None);
    }
    assert_eq!(
        B(Value(1)).product(B(Computation(2))),
        Some(B(Computation(2)))
    );
    assert_eq!(U(Value(usize::MAX)).product(B(Computation(0))), None);
    assert_eq!(U(Set(usize::MAX)).product(B(Set(0))), None);
    assert_eq!(B(Prop).product(U(Prop)), None);
}

#[test]
fn set_and_prop_product_universes_are_non_cumulative() {
    use BaseSort::*;
    use Sort::{Base as B, Upper as U};
    assert_eq!(B(Set(1)).product(B(Set(3))), Some(B(Set(3))));
    assert_eq!(B(Set(2)).product(U(Set(0))), Some(U(Set(2))));
    assert_eq!(U(Set(1)).product(U(Set(4))), Some(U(Set(4))));
    assert_eq!(U(Set(2)).product(B(Set(1))), Some(B(Set(3))));
    assert_eq!(U(Set(3)).product(B(Prop)), Some(B(Prop)));
    let env = Environment::new();
    let a = &env.arena;
    let set0 = sort(a, Set(0));
    let set1 = sort(a, Set(1));
    assert!(
        Checker::new(&env, &mut MetaContext::new(), vec![binding(set0)])
            .check(a.bound(0), set1)
            .is_err()
    );
}

#[test]
fn flex_flex_uses_the_smaller_scope_and_origins_follow_dependencies() {
    let env = Environment::new();
    let a = &env.arena;
    let set = sort(a, BaseSort::Set(0));
    let mut metas = MetaContext::new();
    let small = metas.fresh(a, vec![], None);
    let large = metas.fresh(a, vec![binding(set)], None);
    let Node::Meta { id, .. } = a.get(small) else {
        unreachable!()
    };
    metas
        .set_origin(id, crate::metavariables::OriginId(17))
        .unwrap();
    let constraint = Constraint::Equal {
        context: vec![binding(set)],
        left: small,
        right: large,
    };
    assert_eq!(
        metas.constraint_origins(a, &constraint).unwrap(),
        vec![crate::metavariables::OriginId(17)]
    );
    assert_eq!(
        metas
            .unify(&env, &vec![binding(set)], small, large)
            .unwrap(),
        Outcome::Solved
    );
    metas.unify(&env, &vec![], small, set).unwrap();
    metas.finish(&env).unwrap();
    assert_eq!(metas.zonk(a, large).unwrap(), set);
}

#[test]
fn restricting_a_hole_preserves_its_diagnostic_origin() {
    let env = Environment::new();
    let a = &env.arena;
    let set = sort(a, BaseSort::Set(0));
    let mut metas = MetaContext::new();
    let hole = metas.fresh(a, vec![binding(set)], None);
    let Node::Meta { id, .. } = a.get(hole) else {
        unreachable!()
    };
    let origin = crate::metavariables::OriginId(42);
    metas.set_origin(id, origin).unwrap();
    let restricted = metas.restrict(&env, id, 0).unwrap();
    let constraint = Constraint::Equal {
        context: vec![],
        left: restricted,
        right: set,
    };
    assert_eq!(
        metas.constraint_origins(a, &constraint).unwrap(),
        vec![origin]
    );
    metas.unify(&env, &vec![], restricted, set).unwrap();
    metas.finish(&env).unwrap();
    assert_eq!(metas.zonk(a, hole).unwrap(), set);
}

#[test]
fn ascription_checks_type_and_erases_under_reduction() {
    let env = Environment::new();
    let arena = &env.arena;
    let mut metas = MetaContext::new();
    let mut ctx = context(&env);
    ctx.push(Binding {
        var: SymbolId::ANONYMOUS,
        ty: arena.bound(0),
    });
    let term = arena.bound(0);
    let ty = arena.bound(1);
    let annotated = arena.alloc(Node::Ascribe { term, ty });
    assert_eq!(
        Checker::new(&env, &mut metas, ctx.clone())
            .infer(annotated)
            .unwrap(),
        ty
    );
    assert_eq!(env.whnf(annotated).unwrap(), term);
    assert!(crate::reduction::convertible(&env, annotated, term).unwrap());
    let wrong = arena.alloc(Node::Ascribe {
        term,
        ty: arena.sort(Sort::Base(BaseSort::Prop)),
    });
    assert!(
        Checker::new(&env, &mut metas, ctx.clone())
            .infer(wrong)
            .is_err()
    );
    let invalid_type = arena.alloc(Node::Ascribe { term, ty: term });
    assert!(
        Checker::new(&env, &mut metas, ctx)
            .infer(invalid_type)
            .is_err()
    );
    let kind_annotation = arena.alloc(Node::Ascribe {
        term: arena.sort(Sort::Base(BaseSort::Set(0))),
        ty: arena.sort(Sort::Upper(BaseSort::Set(0))),
    });
    assert_eq!(
        Checker::new(&env, &mut metas, vec![])
            .infer(kind_annotation)
            .unwrap(),
        arena.sort(Sort::Upper(BaseSort::Set(0)))
    );
    let instantiated = instantiate(arena, annotated, &[arena.bound(3), arena.bound(2)]).unwrap();
    assert_eq!(
        arena.get(instantiated),
        Node::Ascribe {
            term: arena.bound(2),
            ty: arena.bound(3)
        }
    );
}

#[test]
fn ascription_propagates_expected_type_to_metas() {
    let env = Environment::new();
    let mut metas = MetaContext::new();
    let mut ctx = context(&env);
    let set = ctx[0].ty;
    ctx.push(Binding {
        var: SymbolId::ANONYMOUS,
        ty: env.arena.bound(0),
    });
    let ty = metas.fresh(&env.arena, ctx.clone(), Some(set));
    let term = env.arena.alloc(Node::Ascribe {
        term: env.arena.bound(0),
        ty,
    });
    metas.infer(&env, ctx.clone(), term).unwrap();
    metas.finish(&env).unwrap();
    assert_eq!(metas.zonk(&env.arena, ty).unwrap(), env.arena.bound(1));
    let term = metas.zonk(&env.arena, term).unwrap();
    assert_eq!(
        Checker::new(&env, &mut metas, ctx).infer(term).unwrap(),
        env.arena.bound(1)
    );
}

#[test]
fn annotated_program_values_can_be_forced_and_reflected() {
    let env = Environment::new();
    let arena = &env.arena;
    let mut metas = MetaContext::new();
    let ctx = vec![
        Binding {
            var: SymbolId::ANONYMOUS,
            ty: arena.sort(Sort::Base(BaseSort::Value(0))),
        },
        Binding {
            var: SymbolId::ANONYMOUS,
            ty: arena.bound(0),
        },
    ];
    let returned = arena.alloc(Node::Return {
        value: arena.bound(0),
    });
    let computation_ty = arena.alloc(Node::ReturnType {
        value_ty: arena.bound(1),
    });
    let thunk = arena.alloc(Node::ThunkValue {
        computation: returned,
    });
    let annotated = arena.alloc(Node::Ascribe {
        term: thunk,
        ty: arena.alloc(Node::Thunk { computation_ty }),
    });
    let forced = arena.alloc(Node::Force { value: annotated });
    assert_eq!(
        Checker::new(&env, &mut metas, ctx.clone())
            .infer(forced)
            .unwrap(),
        computation_ty
    );
    assert_eq!(crate::reduction::normalize(&env, forced).unwrap(), returned);
    let reflected = arena.alloc(Node::Reflect { term: annotated });
    assert_eq!(
        env.whnf(reflected).unwrap(),
        arena.alloc(Node::Reflect {
            term: arena.bound(0)
        })
    );
    Checker::new(&env, &mut metas, ctx)
        .infer(reflected)
        .unwrap();
}

#[test]
fn module_parameter_registration_requires_a_type() {
    use crate::ids::ParameterId;
    let mut env = Environment::new();
    let a = env.arena.clone();
    let set = sort(&a, BaseSort::Set(0));
    let proof = lambda(
        &a,
        Mode::Pure,
        sort(&a, BaseSort::Prop),
        lambda(&a, Mode::Pure, a.bound(0), a.bound(0)),
    );
    Checker::new(&env, &mut MetaContext::new(), vec![])
        .infer(proof)
        .unwrap();
    assert!(env.register_parameter(ParameterId(1), proof).is_err());
    assert_eq!(env.parameter(ParameterId(1)), None);
    env.register_parameter(ParameterId(1), set).unwrap();
    let parameter = a.alloc(Node::Parameter(ParameterId(1)));
    assert_eq!(
        Checker::new(&env, &mut MetaContext::new(), vec![])
            .infer(parameter)
            .unwrap(),
        set
    );
}

#[test]
fn inductive_registration_checks_the_arity_terminal_sort() {
    use crate::{environment::InductiveSpec, ids::InductiveId};
    let mut env = Environment::new();
    let a = env.arena.clone();
    let set = sort(&a, BaseSort::Set(0));
    let proof = lambda(
        &a,
        Mode::Pure,
        sort(&a, BaseSort::Prop),
        lambda(&a, Mode::Pure, a.bound(0), a.bound(0)),
    );
    Checker::new(&env, &mut MetaContext::new(), vec![])
        .infer(proof)
        .unwrap();
    let id = InductiveId(400);
    let falsehood = a.alloc(Node::Product {
        var: SymbolId::ANONYMOUS,
        domain: sort(&a, BaseSort::Prop),
        body: a.bound(0),
    });
    for arity in [proof, falsehood, sort(&a, BaseSort::Set(1)), a.bound(0)] {
        assert!(
            env.register_inductive(
                id,
                InductiveSpec {
                    parameters: vec![binding(set)],
                    arity,
                    constructors: vec![],
                    sort: Sort::Base(BaseSort::Set(0)),
                }
            )
            .is_err()
        );
        assert!(env.inductive(id).is_none());
    }
    let arity = a.alloc(Node::Product {
        var: SymbolId::ANONYMOUS,
        domain: a.bound(0),
        body: set,
    });
    env.register_inductive(
        id,
        InductiveSpec {
            parameters: vec![binding(set)],
            arity,
            constructors: vec![],
            sort: Sort::Base(BaseSort::Set(0)),
        },
    )
    .unwrap();
    let ty = a.alloc(Node::IndType {
        inductive: id,
        parameters: vec![a.bound(0)],
    });
    assert_eq!(
        Checker::new(&env, &mut MetaContext::new(), vec![binding(set)])
            .infer(ty)
            .unwrap(),
        arity
    );
    let id = InductiveId(401);
    for invalid in [proof, sort(&a, BaseSort::Set(1)), arity] {
        assert!(
            env.register_inductive(
                id,
                InductiveSpec {
                    parameters: vec![binding(set)],
                    arity: invalid,
                    constructors: vec![],
                    sort: Sort::Upper(BaseSort::Set(0)),
                }
            )
            .is_err()
        );
        assert!(env.inductive(id).is_none());
    }
    env.register_inductive(
        id,
        InductiveSpec {
            parameters: vec![],
            arity: set,
            constructors: vec![],
            sort: Sort::Upper(BaseSort::Set(0)),
        },
    )
    .unwrap();
    let ty = a.alloc(Node::IndType {
        inductive: id,
        parameters: vec![],
    });
    assert_eq!(
        Checker::new(&env, &mut MetaContext::new(), vec![])
            .infer(ty)
            .unwrap(),
        a.sort(Sort::Upper(BaseSort::Set(0)))
    );
}

#[test]
fn constraint_outcomes_survive_unrelated_goals_and_follow_rollback() {
    let env = Environment::new();
    let mut metas = MetaContext::new();
    let proposition = env.arena.sort(Sort::Base(BaseSort::Prop));
    let constraint = Constraint::Equal {
        context: vec![],
        left: proposition,
        right: proposition,
    };
    metas.constrain(constraint.clone());
    let snapshot = metas.snapshot();
    metas.fresh(&env.arena, vec![], None);
    assert!(matches!(metas.finish(&env), Err(Error::Unresolved { .. })));
    assert!(metas.is_discharged(&constraint));
    metas.rollback(snapshot).unwrap();
    assert!(!metas.is_discharged(&constraint));
    metas.finish(&env).unwrap();
    assert!(metas.is_discharged(&constraint));
}

#[test]
fn arena_properties_follow_binders_metas_and_scratch_lifetimes() {
    let a = Arena::new();
    let set = sort(&a, BaseSort::Set(0));
    let mut metas = MetaContext::new();
    let hole = metas.fresh(&a, vec![], Some(set));
    let open = product(&a, hole, a.bound(3));
    assert!(a.contains_meta(open));
    assert_eq!(a.max_loose_bound(open), Some(2));
    let mark = a.scratch_mark();
    let retained = lambda(&a, Mode::Pure, set, open);
    let discarded = product(&a, set, a.bound(100));
    assert_eq!(a.max_loose_bound(discarded), Some(99));
    a.finish_scratch(mark, [retained]);
    assert!(!a.is_live(discarded));
    assert!(a.contains_meta(retained));
    assert_eq!(a.max_loose_bound(retained), Some(1));
    let rebuilt = product(&a, set, a.bound(100));
    assert_ne!(rebuilt, discarded);
    assert_eq!(a.max_loose_bound(rebuilt), Some(99));
    assert!(!a.contains_meta(rebuilt));
}

#[test]
fn application_modes_preserve_logical_program_and_type_family_checks() {
    let mut env = Environment::new();
    let (_, nat, zero) = natural(&mut env);
    let a = env.arena.clone();
    let set = sort(&a, BaseSort::Set(0));
    let value = sort(&a, BaseSort::Value(0));
    let mut metas = MetaContext::new();

    let logical = lambda(&a, Mode::Pure, set, a.bound(0));
    let mut checker = Checker::new(&env, &mut metas, vec![binding(set)]);
    assert_eq!(
        checker
            .infer(apply(&a, Mode::Pure, logical, a.bound(0)))
            .unwrap(),
        set
    );
    assert!(
        checker
            .infer(apply(&a, Mode::Computation, logical, a.bound(0)))
            .is_err()
    );
    assert!(checker.infer(apply(&a, Mode::Pure, logical, zero)).is_err());

    let body = a.alloc(Node::Return { value: a.bound(0) });
    let program = lambda(&a, Mode::Computation, nat, body);
    let mut checker = Checker::new(&env, &mut metas, vec![]);
    let expected = a.alloc(Node::ReturnType { value_ty: nat });
    assert_eq!(
        checker
            .infer(apply(&a, Mode::Computation, program, zero))
            .unwrap(),
        expected
    );
    assert!(checker.infer(apply(&a, Mode::Pure, program, zero)).is_err());

    // A Program type parameter can also form a pure type family.
    let family = lambda(&a, Mode::Pure, value, a.bound(0));
    assert_eq!(
        checker.infer(apply(&a, Mode::Pure, family, nat)).unwrap(),
        value
    );
    assert!(
        checker
            .infer(apply(&a, Mode::Computation, family, nat))
            .is_err()
    );
}

#[test]
fn open_induction_motive_traversal_preserves_telescope_scope() {
    use crate::calculus::{alpha_equal, max_loose_bound, shift};
    use crate::ids::InductiveId;
    let env = Environment::new();
    let a = env.arena();
    // Ambient A, x : A. The motive telescope is (B : Set, y : B).
    let set = a.sort(Sort::Base(BaseSort::Set(0)));
    let term = a.alloc(Node::IndElim {
        inductive: InductiveId(0),
        scrutinee: a.bound(0),
        motive_bindings: vec![
            (SymbolId::ANONYMOUS, set),
            (SymbolId::ANONYMOUS, a.bound(0)),
        ],
        motive: a.bound(3),
        cases: vec![a.bound(1)],
    });
    assert_eq!(max_loose_bound(a, term), Some(1));
    let shifted = shift(a, term, 2, 0).unwrap();
    let Node::IndElim {
        motive_bindings,
        motive,
        scrutinee,
        cases,
        ..
    } = a.get(shifted)
    else {
        panic!()
    };
    assert_eq!(motive_bindings[1].1, a.bound(0));
    assert_eq!(motive, a.bound(5));
    assert_eq!(scrutinee, a.bound(2));
    assert_eq!(cases, vec![a.bound(3)]);
    let closed = instantiate(a, term, &[set, set]).unwrap();
    assert_eq!(max_loose_bound(a, closed), None);
    let mut renamed = a.get(term);
    if let Node::IndElim {
        motive_bindings, ..
    } = &mut renamed
    {
        motive_bindings[0].0 = SymbolId(17);
        motive_bindings[1].0 = SymbolId(18);
    }
    assert!(alpha_equal(a, term, a.alloc(renamed)));
}

#[test]
fn open_induction_motive_sort_boundaries_and_subject_reduction() {
    use crate::{environment::InductiveSpec, ids::InductiveId, reduction::convertible};
    use BaseSort::{Prop, Set};
    // The motive body's classifier is the elimination target sort.
    for (source_sort, target_sort, singleton, allowed) in [
        (Sort::Base(Set(0)), Sort::Base(Set(0)), false, true),
        (Sort::Base(Set(0)), Sort::Base(Set(1)), false, true),
        (Sort::Base(Set(1)), Sort::Base(Set(0)), false, false),
        (Sort::Base(Set(0)), Sort::Base(Prop), false, true),
        (Sort::Base(Set(0)), Sort::Upper(Prop), false, true),
        (Sort::Base(Prop), Sort::Base(Prop), false, true),
        (Sort::Base(Prop), Sort::Upper(Prop), false, false),
        (Sort::Base(Prop), Sort::Upper(Prop), true, true),
        (Sort::Base(Set(0)), Sort::Upper(Set(0)), false, false),
        (Sort::Base(Set(0)), Sort::Upper(Set(0)), true, true),
    ] {
        let mut env = Environment::new();
        let a = env.arena().clone();
        let source_id = InductiveId(0);
        let source = a.alloc(Node::IndType {
            inductive: source_id,
            parameters: vec![],
        });
        let count = if singleton { 1 } else { 2 };
        env.register_inductive(
            source_id,
            InductiveSpec {
                parameters: vec![],
                arity: a.sort(source_sort),
                constructors: vec![source; count],
                sort: source_sort,
            },
        )
        .unwrap();
        let target_id = InductiveId(1);
        let target_base = Sort::Base(target_sort.base());
        let target = a.alloc(Node::IndType {
            inductive: target_id,
            parameters: vec![],
        });
        env.register_inductive(
            target_id,
            InductiveSpec {
                parameters: vec![],
                arity: a.sort(target_base),
                constructors: vec![target],
                sort: target_base,
            },
        )
        .unwrap();
        let (motive, branch) = if target_sort.is_upper() {
            (a.sort(target_base), target)
        } else {
            (
                target,
                a.alloc(Node::IndCtor {
                    inductive: target_id,
                    constructor: 0,
                    parameters: vec![],
                }),
            )
        };
        let term = a.alloc(Node::IndElim {
            inductive: source_id,
            scrutinee: a.alloc(Node::IndCtor {
                inductive: source_id,
                constructor: 0,
                parameters: vec![],
            }),
            motive_bindings: vec![(SymbolId::ANONYMOUS, source)],
            motive,
            cases: vec![branch; count],
        });
        let mut metas = MetaContext::new();
        let inferred = Checker::new(&env, &mut metas, vec![]).infer(term);
        assert_eq!(
            inferred.is_ok(),
            allowed,
            "{source_sort:?} -> {target_sort:?}, singleton={singleton}: {inferred:?}"
        );
        if allowed {
            let reduced = env.whnf(term).unwrap();
            let reduced_type = Checker::new(&env, &mut metas, vec![])
                .infer(reduced)
                .unwrap();
            assert!(convertible(&env, inferred.unwrap(), reduced_type).unwrap());
            assert!(convertible(&env, reduced, branch).unwrap());
        } else {
            assert!(
                inferred
                    .unwrap_err()
                    .to_string()
                    .contains("forbidden large elimination")
            );
        }
        if target_sort.is_upper() {
            let lambda = a.alloc(Node::Lambda {
                mode: Mode::Pure,
                var: SymbolId::ANONYMOUS,
                domain: source,
                body: motive,
            });
            assert!(
                Checker::new(&env, &mut metas, vec![])
                    .infer(lambda)
                    .is_err()
            );
        }
    }
}

#[test]
fn motive_unification_extends_context_through_dependent_telescope() {
    use crate::ids::InductiveId;
    let env = Environment::new();
    let a = env.arena();
    let set = a.sort(Sort::Base(BaseSort::Set(0)));
    let var = SymbolId::ANONYMOUS;
    let context = vec![
        Binding { var, ty: set },
        Binding {
            var,
            ty: a.bound(0),
        },
    ];
    let mut metas = MetaContext::new();
    let mut under_b = context.clone();
    under_b.push(Binding { var, ty: set });
    let domain = metas.fresh(a, under_b.clone(), Some(set));
    let mut under_y = under_b;
    under_y.push(Binding { var, ty: domain });
    let body = metas.fresh(a, under_y, Some(set));
    let left = a.alloc(Node::IndElim {
        inductive: InductiveId(0),
        scrutinee: a.bound(0),
        motive_bindings: vec![(var, set), (var, domain)],
        motive: body,
        cases: vec![],
    });
    let right = a.alloc(Node::IndElim {
        inductive: InductiveId(0),
        scrutinee: a.bound(0),
        motive_bindings: vec![(var, set), (var, a.bound(0))],
        motive: a.bound(3),
        cases: vec![],
    });
    assert_eq!(
        metas.unify(&env, &context, left, right).unwrap(),
        Outcome::Solved
    );
    metas.finish(&env).unwrap();
    assert_eq!(metas.zonk(a, domain).unwrap(), a.bound(0));
    assert_eq!(metas.zonk(a, body).unwrap(), a.bound(3));
}
