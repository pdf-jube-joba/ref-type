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
        sort: SetSort::Set(i),
        form: SetKindForm::Base,
    })
}

#[test]
fn shared_syntax_transformations_respect_each_binder_depth() {
    let a = Arena::new();
    let ty = |index| {
        a.alloc(SetTypeNode {
            sort: SetSort::Set(0),
            form: SetTypeForm::Bound { index },
        })
    };
    let rule =
        ProductRule::new(Sort::Base(BaseSort::Set(0)), Sort::Base(BaseSort::Set(0))).unwrap();
    let product = |domain, body| {
        a.alloc(SetTypeNode {
            sort: SetSort::Set(0),
            form: SetTypeForm::ProdTerm {
                rule,
                var: SymbolId::ANONYMOUS,
                domain,
                body,
            },
        })
    };
    let argument = a.alloc(SetTypeNode {
        sort: SetSort::Set(0),
        form: SetTypeForm::ModuleParam {
            parameter: ModuleParamId {
                module: ModuleId(0),
                position: 0,
            },
        },
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
fn polymorphic_program_identity_and_reflection() {
    let env = Environment::new();
    let a = &env.arena;
    let k = vk(a, 0);
    let x = a.alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::Bound { index: 0 },
    });
    let v = a.alloc(ValueNode {
        level: 0,
        form: ValueForm::Bound { index: 0 },
    });
    let ret = a.alloc(ComputationNode {
        level: 0,
        form: ComputationForm::Return { value: v },
    });
    let r = ProductRule::new(
        Sort::Base(BaseSort::Value(0)),
        Sort::Base(BaseSort::Computation(0)),
    )
    .unwrap();
    let lam = a.alloc(ComputationNode {
        level: 0,
        form: ComputationForm::LambdaTerm {
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
    let poly = a.alloc(ComputationNode {
        level: 1,
        form: ComputationForm::LambdaType {
            rule: poly_rule,
            var: SymbolId(1),
            domain: k.into(),
            body: lam,
        },
    });
    let mut checker = Checker::new(&env, vec![]);
    let ty = checker.infer_computation(poly).unwrap();
    assert_eq!(a.sort(ty), BaseSort::Computation(1));
    let refl = reflect_term(&env, poly.into()).unwrap();
    let rty = reflect_type(&env, ty.into()).unwrap();
    checker.check(refl, rty).unwrap();
    // Instantiate at an open value type A, then at x : A. The result has level 0.
    let arg = a.alloc(ValueTypeNode {
        level: 0,
        form: ValueTypeForm::Bound { index: 1 },
    });
    let applied = a.alloc(ComputationNode {
        level: 0,
        form: ComputationForm::AppType {
            rule: poly_rule,
            function: poly,
            argument: arg.into(),
        },
    });
    let applied = a.alloc(ComputationNode {
        level: 0,
        form: ComputationForm::AppTerm {
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
    let result_ty = checker.infer_computation(applied).unwrap();
    assert_eq!(a.sort(result_ty), BaseSort::Computation(0));
    let result = normalize(&env, applied).unwrap();
    assert!(matches!(a.data(result).op, Op::Return));
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
        sort: SetSort::Set(0),
        form: SetTypeForm::Bound { index: 0 },
    });
    let bad = a.alloc(SetTypeNode {
        sort: SetSort::Set(1),
        form: SetTypeForm::Bound { index: 0 },
    });
    let mut checker = Checker::new(
        &env,
        vec![Binding {
            var: SymbolId(1),
            classifier: k.into(),
        }],
    );
    assert!(checker.infer_type(bad).is_err());
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
        sort: SetSort::Set(0),
        form: SetTypeForm::Bound { index: 0 },
    });
    let y = a.alloc(SetTypeNode {
        sort: SetSort::Set(1),
        form: SetTypeForm::Bound { index: 0 },
    });
    assert!(substitute(&a, x, y).is_err());
}
fn program_id(a: &Arena, i: usize) -> Computation {
    let x = a.alloc(ValueTypeNode {
        level: i,
        form: ValueTypeForm::Bound { index: 0 },
    });
    let v = a.alloc(ValueNode {
        level: i,
        form: ValueForm::Bound { index: 0 },
    });
    let ret = a.alloc(ComputationNode {
        level: i,
        form: ComputationForm::Return { value: v },
    });
    let r = ProductRule::new(
        Sort::Base(BaseSort::Value(i)),
        Sort::Base(BaseSort::Computation(i)),
    )
    .unwrap();
    let lambda = a.alloc(ComputationNode {
        level: i,
        form: ComputationForm::LambdaTerm {
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
    a.alloc(ComputationNode {
        level: i + 1,
        form: ComputationForm::LambdaType {
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
    let ty0 = c.infer_computation(id0).unwrap();
    let ty1 = c.infer_computation(id1).unwrap();
    let cert1 = reflect_term(&env, id1.into()).unwrap();
    let boxed = a.alloc(SetTermNode {
        sort: SetSort::Set(2),
        form: SetTermForm::BoxProgram {
            program_ty: ty1.into(),
            program: id1.into(),
            certified_reflection: cert1,
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
        sort: SetSort::Set(1),
        form: SetTermForm::BoxTypeApp {
            rule,
            var,
            domain,
            codomain: body,
            function: boxed,
            argument: arg_ty.into(),
        },
    });
    c.infer_term(tapp).unwrap();
    let arg = a.alloc(ValueNode {
        level: 1,
        form: ValueForm::ThunkValue { computation: id0 },
    });
    let cert0 = reflect_term(&env, arg.into()).unwrap();
    let boxed_arg = a.alloc(SetTermNode {
        sort: SetSort::Set(1),
        form: SetTermForm::BoxProgram {
            program_ty: arg_ty.into(),
            program: arg.into(),
            certified_reflection: cert0,
        },
    });
    let result_ty = a.alloc(ComputationTypeNode {
        level: 1,
        form: ComputationTypeForm::ReturnType { value_ty: arg_ty },
    });
    let r = ProductRule::new(
        Sort::Base(BaseSort::Value(1)),
        Sort::Base(BaseSort::Computation(1)),
    )
    .unwrap();
    let app = a.alloc(SetTermNode {
        sort: SetSort::Set(1),
        form: SetTermForm::BoxApp {
            rule: r,
            domain: arg_ty,
            codomain: result_ty,
            function: tapp,
            argument: boxed_arg,
        },
    });
    c.infer_term(app).unwrap();
    let forced = a.alloc(SetTermNode {
        sort: SetSort::Set(1),
        form: SetTermForm::ForceBox {
            program_ty: result_ty.into(),
            boxed: app,
        },
    });
    c.infer_term(forced).unwrap();
    assert!(convertible(&env, forced.into(), cert0.into()).unwrap());
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
    let v = a.alloc(ValueNode {
        level: 2,
        form: ValueForm::Bound { index: 0 },
    });
    let force = a.alloc(ComputationNode {
        level: 2,
        form: ComputationForm::Force { value: v },
    });
    let r = ProductRule::new(
        Sort::Base(BaseSort::Value(2)),
        Sort::Base(BaseSort::Computation(2)),
    )
    .unwrap();
    let lam = a.alloc(ComputationNode {
        level: 2,
        form: ComputationForm::LambdaTerm {
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
    let lam = a.alloc(ComputationNode {
        level: 3,
        form: ComputationForm::LambdaType {
            rule: r,
            var: SymbolId(1),
            domain: k.into(),
            body: lam,
        },
    });
    let mut checker = Checker::new(&env, vec![]);
    let ty = checker.infer_computation(lam).unwrap();
    let reflected = reflect_term(&env, lam.into()).unwrap();
    let reflected_ty = reflect_type(&env, ty.into()).unwrap();
    checker.check(reflected, reflected_ty).unwrap();
}
#[test]
fn invalid_declaration_is_not_inserted() {
    let mut env = Environment::new();
    let id = DefId {
        module: ModuleId(0),
        index: 0,
    };
    let k = sk(&env.arena, 0);
    let result = env.register_definition(
        id,
        Definition {
            context: vec![],
            body: k.into(),
            classifier: Classifier::Upper(BaseSort::Set(1)),
            certified_reflection: None,
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
fn natural(env: &mut Environment) -> (ProgramInductiveId, ValueType, Value) {
    let id = ProgramInductiveId {
        module: ModuleId(0),
        index: 0,
    };
    let reflected = InductiveId {
        module: ModuleId(0),
        index: 0,
    };
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
    let zero = env.arena.alloc(ValueNode {
        level: 0,
        form: ValueForm::InductiveConstructor {
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
    let s = env.arena.alloc(ValueNode {
        level: 0,
        form: ValueForm::InductiveConstructor {
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
    let id = ProgramInductiveId {
        module: ModuleId(0),
        index: 0,
    };
    let mirror = InductiveId {
        module: ModuleId(0),
        index: 0,
    };
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
fn boxed_constant_cannot_hide_an_open_module_parameter() {
    let mut env = Environment::new();
    let (_, ty, zero) = natural(&mut env);
    let p = ModuleParamId {
        module: ModuleId(0),
        position: 0,
    };
    env.register_parameter(
        p,
        Binding {
            var: SymbolId(1),
            classifier: ty.into(),
        },
        vec![],
    )
    .unwrap();
    let body = env.arena.alloc(ValueNode {
        level: 0,
        form: ValueForm::ModuleParam { parameter: p },
    });
    let id = DefId {
        module: ModuleId(0),
        index: 0,
    };
    env.register_definition(
        id,
        Definition {
            context: vec![],
            body: body.into(),
            classifier: ty.into(),
            certified_reflection: None,
        },
    )
    .unwrap();
    let constant = env.arena.alloc(ValueNode {
        level: 0,
        form: ValueForm::Constant { definition: id },
    });
    let cert = reflect_term(&env, zero.into()).unwrap();
    let boxed = env.arena.alloc(SetTermNode {
        sort: SetSort::Set(0),
        form: SetTermForm::BoxProgram {
            program_ty: ty.into(),
            program: constant.into(),
            certified_reflection: cert,
        },
    });
    assert!(
        Checker::new(&env, vec![])
            .infer_term(boxed)
            .unwrap_err()
            .contains("closed")
    );
    assert_eq!(reduce_once(&env, constant).unwrap(), None);
}
#[test]
fn program_run_evaluates_but_unrelated_box_certificate_is_rejected() {
    let mut env = Environment::new();
    let (_, ty, zero) = natural(&mut env);
    let a = &env.arena;
    let finish = a.alloc(ValueNode {
        level: 0,
        form: ValueForm::Finish {
            state_ty: ty,
            result_ty: ty,
            output: zero,
        },
    });
    let ret = a.alloc(ComputationNode {
        level: 0,
        form: ComputationForm::Return { value: finish },
    });
    let r = ProductRule::new(
        Sort::Base(BaseSort::Value(0)),
        Sort::Base(BaseSort::Computation(0)),
    )
    .unwrap();
    let lam = a.alloc(ComputationNode {
        level: 0,
        form: ComputationForm::LambdaTerm {
            rule: r,
            var: SymbolId(1),
            domain: ty,
            body: ret,
        },
    });
    let step = a.alloc(ValueNode {
        level: 0,
        form: ValueForm::ThunkValue { computation: lam },
    });
    let run = a.alloc(ComputationNode {
        level: 0,
        form: ComputationForm::Run {
            state_ty: ty,
            result_ty: ty,
            step,
            initial: zero,
        },
    });
    let mut c = Checker::new(&env, vec![]);
    let result_ty = c.infer_computation(run).unwrap();
    assert!(matches!(
        evaluate(&env, run, 0).unwrap(),
        Evaluation::OutOfFuel(_)
    ));
    let Evaluation::Normal(result) = evaluate(&env, run, 10).unwrap() else {
        panic!()
    };
    c.check(result, result_ty).unwrap();
    assert_eq!(a.data(result).op, Op::Return);
    let certificate = reflect_term(&env, zero.into()).unwrap();
    let boxed = a.alloc(SetTermNode {
        sort: SetSort::Set(0),
        form: SetTermForm::BoxProgram {
            program_ty: result_ty.into(),
            program: run.into(),
            certified_reflection: certificate,
        },
    });
    assert!(c.infer_term(boxed).is_err());
}
#[test]
fn kind_valued_recursor_preserves_the_lower_result_level() {
    let env = Environment::new();
    let a = &env.arena;
    let b_kind = sk(a, 0);
    let a_kind = sk(a, 2);
    let a_var = a.alloc(SetTypeNode {
        sort: SetSort::Set(2),
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
        sort: SetSort::Set(2),
        form: SetTypeForm::Bound { index: 1 },
    });
    let value = a.alloc(SetTermNode {
        sort: SetSort::Set(2),
        form: SetTermForm::Bound { index: 0 },
    });
    let b = a.alloc(SetTypeNode {
        sort: SetSort::Set(0),
        form: SetTypeForm::Bound { index: 2 },
    });
    let nested_b = a.alloc(SetTypeNode {
        sort: SetSort::Set(0),
        form: SetTypeForm::Bound { index: 3 },
    });
    let rule =
        ProductRule::new(Sort::Base(BaseSort::Set(2)), Sort::Upper(BaseSort::Set(0))).unwrap();
    let branch = a.alloc(SetTypeNode {
        sort: SetSort::Set(2),
        form: SetTypeForm::LambdaTerm {
            rule,
            var: SymbolId(4),
            domain: state,
            body: nested_b,
        },
    });
    let scrutinee = a.alloc(SetTermNode {
        sort: SetSort::Set(2),
        form: SetTermForm::Continue {
            state_ty: state,
            result_ty: state,
            next: value,
        },
    });
    let rec = a.alloc(SetTypeNode {
        sort: SetSort::Set(0),
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
    checker.infer_type(rec).unwrap();
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
        sort: SetSort::Set(0),
        form: SetTypeForm::Bound { index: 0 },
    });
    let term = a.alloc(SetTermNode {
        sort: SetSort::Set(0),
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
        .infer_term(term)
        .is_err()
    );
    let value = a.alloc(ValueNode {
        level: 0,
        form: ValueForm::Bound { index: 0 },
    });
    let context = vec![Binding {
        var: SymbolId(1),
        classifier: ty.into(),
    }];
    let id = DefId {
        module: ModuleId(0),
        index: 0,
    };
    assert!(
        env.register_definition(
            id,
            Definition {
                context,
                body: value.into(),
                classifier: ty.into(),
                certified_reflection: None
            }
        )
        .is_err()
    );
    assert!(env.definition(id).is_none());
}
