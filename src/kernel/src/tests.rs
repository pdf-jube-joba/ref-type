use crate::{
    calculus::{
        convertible, erased_convertible, erased_normal, exp_is_alpha_eq, exp_subst_module_param,
        instantiate, instantiate_outer_telescope, instantiate_telescope, normalize, whnf,
    },
    derivation::CheckSession,
    environment::{CrateEnv, ModuleParameter},
    exp::{Context, Exp, Node},
    ids::{ModuleId, ModuleParamId, SymbolId},
    inductive::{CtorBinder, CtorType, InductiveTypeSpecs},
    sort::Sort,
};

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
        self.env
            .add_module_parameter(ModuleId(0), ModuleParameter { name: var, ty });
        let exp = self.env.arena().module_param(ModuleParamId {
            module: ModuleId(0),
            position,
        });
        self.context.push((var, ty));
        exp
    }
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
