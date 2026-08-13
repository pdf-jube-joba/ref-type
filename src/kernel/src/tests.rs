use crate::{
    calculus::{
        convertible, erase, erased_convertible, erased_normal, exp_is_alpha_eq, normalize,
        reduce_one,
    },
    exp::{Context, DefinedConstant, Exp, Sort, Var},
    inductive::CtorBinder,
    utils::{self, app, lam, prod, var},
};
use std::rc::Rc;
// rustfmt doens not allow us variable starts with Uppercase letter
// ... => we use double lowercase letters
// e.g. A -> aa, P -> pp, P1 -> pp1 etc.

#[derive(Debug, Default)]
pub struct Checker {
    context: Context,
}

impl Checker {
    fn check(&mut self, term: &Exp, ty: &Exp) -> bool {
        let derivation = crate::derivation::check(&self.context, term, ty);
        match derivation {
            Ok(()) => true,
            Err(fail_der) => {
                print!("Type checking failed:\n{:?}", fail_der);
                false
            }
        }
    }
    fn infer(&mut self, term: &Exp) -> Option<Exp> {
        let derivation = crate::derivation::infer(&self.context, term);

        let ty = match derivation {
            Ok(ty) => ty,
            Err(fail_der) => {
                print!("Type inference failed:\n{:?}", fail_der);
                return None;
            }
        };
        Some(ty)
    }
    fn chk_indspec(
        &mut self,
        params: Vec<(Var, Exp)>,
        indices: Vec<(Var, Exp)>,
        sort: crate::exp::Sort,
        constructors: Vec<crate::inductive::CtorType>,
    ) -> Result<crate::inductive::InductiveTypeSpecs, String> {
        let indspecs = crate::inductive::InductiveTypeSpecs::new(
            &self.context,
            params.clone(),
            indices.clone(),
            sort,
            constructors.clone(),
        )
        .unwrap();
        Ok(indspecs)
    }
    fn push(&mut self, var: Var, ty: Exp) {
        crate::derivation::infer_sort(&self.context, &ty).unwrap();
        self.context.push((var, ty));
    }
}

// P: \Prop |- P: \Prop
#[test]
fn p_prop() {
    let mut checker = Checker::default();
    let pp = var!("P");
    checker.push(pp.clone(), Exp::Sort(Sort::Prop));
    checker.check(&Exp::Var(pp), &Exp::Sort(Sort::Prop));
}

// (P: \Prop), (p: P) |- P : \Prop
#[test]
fn no_need_elem() {
    let mut checker = Checker::default();
    let pp = var!("P");
    checker.push(pp.clone(), Exp::Sort(Sort::Prop));
    let p = var!("p");
    checker.push(p.clone(), Exp::Var(pp.clone()));
    checker.check(&Exp::Var(pp), &Exp::Sort(Sort::Prop));
}

// (P1: \Prop), (P2: \Prop) |- P1 -> P2 : \Prop
#[test]
fn imp_prop() {
    let mut checker = Checker::default();
    let pp1 = var!("P1");
    let pp2 = var!("P2");
    checker.push(pp1.clone(), Exp::Sort(Sort::Prop));
    checker.push(pp2.clone(), Exp::Sort(Sort::Prop));
    checker.check(
        &prod! {
            var: var!("_"),
            ty: Exp::Var(pp1.clone()),
            body: Exp::Var(pp2.clone()),
        },
        &Exp::Sort(Sort::Prop),
    );
}

// (P: \Prop) |- (p: P) => p: (p: P) -> P
#[test]
fn lam_prod() {
    let mut checker = Checker::default();
    let pp = var!("P");
    checker.push(pp.clone(), Exp::Sort(Sort::Prop));
    let p = var!("p");
    checker.check(
        &lam! {
            var: p.clone(),
            ty: Exp::Var(pp.clone()),
            body: Exp::Var(p.clone()),
        },
        &prod! {
            var: p.clone(),
            ty: Exp::Var(pp.clone()),
            body: Exp::Var(pp.clone()),
        },
    );
}

// |- (P: \Prop) -> (p: P) -> P: \Prop
#[test]
fn impredicative_true() {
    let mut checker = Checker::default();
    let pp = var!("P");
    let p = var!("p");
    checker.check(
        &prod! {
            var: pp.clone(),
            ty: Exp::Sort(Sort::Prop),
            body: prod! {
                var: p.clone(),
                ty: Exp::Var(pp.clone()),
                body: Exp::Var(pp.clone()),
            },
        },
        &Exp::Sort(Sort::Prop),
    );
}

// Modus ponens test
// A: \Prop, B: \Prop, f: A -> B, a: A |- f a : B
#[test]
fn modusponens_ctx() {
    let mut checker = Checker::default();
    let aa = var!("A");
    let bb = var!("B");
    let f = var!("f");
    let a = var!("a");
    checker.push(aa.clone(), Exp::Sort(Sort::Prop));
    checker.push(bb.clone(), Exp::Sort(Sort::Prop));
    checker.push(
        f.clone(),
        Exp::Prod {
            var: var!("_"),
            ty: Box::new(Exp::Var(aa.clone())),
            body: Box::new(Exp::Var(bb.clone())),
        },
    );
    checker.push(a.clone(), Exp::Var(aa.clone()));
    checker.check(
        &Exp::App {
            func: Box::new(Exp::Var(f.clone())),
            arg: Box::new(Exp::Var(a.clone())),
        },
        &Exp::Var(bb.clone()),
    );
}

// Modus ponens test with abstraction
// tele = [(A: \Prop), (B: \Prop), (f: A -> B), (a: A)]
// |- (tele[]) => (f a) : (tele[]) -> B
#[test]
fn modusponens_popped() {
    let mut checker = Checker::default();
    let aa = var!("A");
    let bb = var!("B");
    let f = var!("f");
    let a = var!("a");
    let telescope: Vec<(Var, Exp)> = vec![
        (aa.clone(), Exp::Sort(Sort::Prop)),
        (bb.clone(), Exp::Sort(Sort::Prop)),
        (
            f.clone(),
            Exp::Prod {
                var: var!("_"),
                ty: Box::new(Exp::Var(aa.clone())),
                body: Box::new(Exp::Var(bb.clone())),
            },
        ),
        (a.clone(), Exp::Var(aa.clone())),
    ];

    for (var, ty) in telescope.iter() {
        checker.push(var.clone(), ty.clone());
    }
    let term = utils::assoc_lam(
        telescope.clone(),
        Exp::App {
            func: Box::new(Exp::Var(f.clone())),
            arg: Box::new(Exp::Var(a.clone())),
        },
    );
    let ty = utils::assoc_prod(telescope, Exp::Var(bb.clone()));
    checker.check(&term, &ty);
}

// Alpha equivalence test
// A: \Prop |- (a: A) => a: (b: A) -> A
#[test]
fn alpha_equiv() {
    let mut checker = Checker::default();
    let aa = var!("A");
    let a = var!("a");
    let b = var!("b");
    checker.push(aa.clone(), Exp::Sort(Sort::Prop));
    checker.check(
        &lam! {
            var: a.clone(),
            ty: Exp::Var(aa.clone()),
            body: Exp::Var(a.clone()),
        },
        &prod! {
            var: b.clone(),
            ty: Exp::Var(aa.clone()),
            body: Exp::Var(aa.clone()),
        },
    );
}

// Type-level reduction
// X: \Prop, x: X |- x : ((Y: \Prop) => Y) X
#[test]
fn type_level_reduction() {
    let mut checker = Checker::default();
    let xx = var!("X");
    let x = var!("x");
    let yy = var!("Y");
    checker.push(xx.clone(), Exp::Sort(Sort::Prop));
    checker.push(x.clone(), Exp::Var(xx.clone()));
    checker.check(
        &Exp::Var(x.clone()),
        &Exp::App {
            func: Box::new(Exp::Lam {
                var: yy.clone(),
                ty: Box::new(Exp::Sort(Sort::Prop)),
                body: Box::new(Exp::Var(yy.clone())),
            }),
            arg: Box::new(Exp::Var(xx.clone())),
        },
    );
}

// Power set
// X: \Set(0) |- Power(X): \Set(0)
#[test]
fn powerset() {
    let mut checker = Checker::default();
    let xx = var!("X");
    checker.push(xx.clone(), Exp::Sort(Sort::Set(0)));
    checker.check(
        &Exp::PowerSet {
            set: Box::new(Exp::Var(xx.clone())),
        },
        &Exp::Sort(Sort::Set(0)),
    );
}

#[test]
fn powerset_level_is_preserved() {
    let mut checker = Checker::default();
    let xx = var!("X");
    checker.push(xx.clone(), Exp::Sort(Sort::Set(1)));

    let inferred = checker
        .infer(&Exp::PowerSet {
            set: Box::new(Exp::Var(xx.clone())),
        })
        .unwrap();

    assert!(matches!(inferred, Exp::Sort(Sort::Set(1))));
}

#[test]
fn equality_requires_set_carrier() {
    let pp = var!("P");
    let p = var!("p");
    let ctx = vec![
        (pp.clone(), Exp::Sort(Sort::Prop)),
        (p.clone(), Exp::Var(pp.clone())),
    ];

    let result = crate::derivation::infer(
        &ctx,
        &Exp::Equal {
            left: Box::new(Exp::Var(p.clone())),
            right: Box::new(Exp::Var(p.clone())),
        },
    );

    assert!(result.is_err());
}

#[test]
fn context_wellformedness_uses_prefix_context() {
    let x = var!("x");
    let y = var!("y");
    let ctx = vec![
        (x.clone(), Exp::Var(y.clone())),
        (y.clone(), Exp::Sort(Sort::Set(0))),
    ];

    assert!(crate::derivation::check_wellformed_ctx(&ctx).is_err());
}

#[test]
fn take_uses_explicit_domain_and_codomain() {
    let xx = var!("X");
    let tt = var!("T");
    let f = var!("f");
    let exists = var!("exists");
    let unique = var!("unique");
    let x1 = var!("x1");
    let x2 = var!("x2");
    let uniqueness_ty = Exp::Prod {
        var: x1.clone(),
        ty: Box::new(Exp::Var(xx.clone())),
        body: Box::new(Exp::Prod {
            var: x2.clone(),
            ty: Box::new(Exp::Var(xx.clone())),
            body: Box::new(Exp::Equal {
                left: Box::new(app!(Exp::Var(f.clone()), Exp::Var(x1))),
                right: Box::new(app!(Exp::Var(f.clone()), Exp::Var(x2))),
            }),
        }),
    };
    let ctx = vec![
        (xx.clone(), Exp::Sort(Sort::Set(0))),
        (tt.clone(), Exp::Sort(Sort::Set(0))),
        (
            f.clone(),
            Exp::Prod {
                var: var!("_"),
                ty: Box::new(Exp::Var(xx.clone())),
                body: Box::new(Exp::Var(tt.clone())),
            },
        ),
        (
            exists.clone(),
            Exp::Exists {
                set: Box::new(Exp::Var(xx.clone())),
            },
        ),
        (unique.clone(), uniqueness_ty),
    ];

    let take = Exp::Take {
        domain: Box::new(Exp::Var(xx.clone())),
        codomain: Box::new(Exp::Var(tt.clone())),
        map: Box::new(Exp::Var(f.clone())),
        existence: Box::new(Exp::Var(exists)),
        uniqueness: Some(Box::new(Exp::Var(unique))),
    };

    let derivation = crate::derivation::infer(&ctx, &take).unwrap();

    assert!(crate::calculus::exp_is_alpha_eq(
        &derivation,
        &Exp::Var(tt.clone())
    ));
}

#[test]
fn set_valued_take_rejects_missing_uniqueness_proof() {
    let xx = var!("X");
    let tt = var!("T");
    let f = var!("f");
    let exists = var!("exists");
    let ctx = vec![
        (xx.clone(), Exp::Sort(Sort::Set(0))),
        (tt.clone(), Exp::Sort(Sort::Set(0))),
        (
            f.clone(),
            Exp::Prod {
                var: var!("_"),
                ty: Box::new(Exp::Var(xx.clone())),
                body: Box::new(Exp::Var(tt.clone())),
            },
        ),
        (
            exists.clone(),
            Exp::Exists {
                set: Box::new(Exp::Var(xx.clone())),
            },
        ),
    ];

    let take = Exp::Take {
        domain: Box::new(Exp::Var(xx)),
        codomain: Box::new(Exp::Var(tt)),
        map: Box::new(Exp::Var(f)),
        existence: Box::new(Exp::Var(exists)),
        uniqueness: None,
    };

    assert!(crate::derivation::infer(&ctx, &take).is_err());
}

#[test]
fn subset_intro_rejects_a_non_power_subset() {
    let aa = var!("A");
    let not_subset = var!("not_subset");
    let x = var!("x");
    let ctx = vec![
        (aa.clone(), Exp::Sort(Sort::Set(0))),
        (not_subset.clone(), Exp::Var(aa.clone())),
        (x.clone(), Exp::Var(aa.clone())),
    ];
    let intro = Exp::SubsetIntro {
        superset: Box::new(Exp::Var(aa)),
        subset: Box::new(Exp::Var(not_subset.clone())),
        element: Box::new(Exp::Var(x)),
        proof: Box::new(Exp::Var(not_subset)),
    };

    assert!(crate::derivation::infer(&ctx, &intro).is_err());
}

#[test]
fn subset_intro_checks_membership_and_erases_to_its_element() {
    let aa = var!("A");
    let subset = var!("S");
    let x = var!("x");
    let proof = var!("p");
    let refinement = Exp::TypeLift {
        superset: Box::new(Exp::Var(aa.clone())),
        subset: Box::new(Exp::Var(subset.clone())),
    };
    let ctx = vec![
        (aa.clone(), Exp::Sort(Sort::Set(0))),
        (
            subset.clone(),
            Exp::PowerSet {
                set: Box::new(Exp::Var(aa.clone())),
            },
        ),
        (x.clone(), refinement.clone()),
        (
            proof.clone(),
            Exp::Pred {
                superset: Box::new(Exp::Var(aa.clone())),
                subset: Box::new(Exp::Var(subset.clone())),
                element: Box::new(Exp::Var(x.clone())),
            },
        ),
    ];
    let intro = Exp::SubsetIntro {
        superset: Box::new(Exp::Var(aa)),
        subset: Box::new(Exp::Var(subset)),
        element: Box::new(Exp::Var(x.clone())),
        proof: Box::new(Exp::Var(proof)),
    };

    let inferred = crate::derivation::infer(&ctx, &intro).unwrap();
    assert!(exp_is_alpha_eq(&inferred, &refinement));
    assert!(exp_is_alpha_eq(&normalize(&intro), &intro));
    assert!(exp_is_alpha_eq(&erased_normal(&intro), &Exp::Var(x)));
    assert!(exp_is_alpha_eq(&erase(&erase(&intro)), &erase(&intro)));
}

#[test]
fn erased_normalization_exposes_computational_redexes() {
    let aa = var!("A");
    let x = var!("x");
    let a = var!("a");
    let wrapped_identity = Exp::SubsetIntro {
        superset: Box::new(Exp::Var(aa.clone())),
        subset: Box::new(Exp::Var(var!("X"))),
        element: Box::new(Exp::Lam {
            var: x.clone(),
            ty: Box::new(Exp::Var(aa)),
            body: Box::new(Exp::Var(x)),
        }),
        proof: Box::new(Exp::Var(var!("p"))),
    };
    let application = Exp::App {
        func: Box::new(wrapped_identity),
        arg: Box::new(Exp::Var(a.clone())),
    };

    assert!(!exp_is_alpha_eq(
        &normalize(&application),
        &Exp::Var(a.clone())
    ));
    assert!(exp_is_alpha_eq(&erased_normal(&application), &Exp::Var(a)));
}

#[test]
fn erased_conversion_applies_inside_type_constructor_arguments() {
    let aa = var!("A");
    let subset = var!("S");
    let a = var!("a");
    let proof = var!("p");
    let constructor = var!("F");
    let value = var!("value");
    let binder = var!("x");
    let intro = Exp::SubsetIntro {
        superset: Box::new(Exp::Var(aa.clone())),
        subset: Box::new(Exp::Var(subset.clone())),
        element: Box::new(Exp::Var(a.clone())),
        proof: Box::new(Exp::Var(proof.clone())),
    };
    let indexed_by_intro = Exp::App {
        func: Box::new(Exp::Var(constructor.clone())),
        arg: Box::new(intro),
    };
    let indexed_by_element = Exp::App {
        func: Box::new(Exp::Var(constructor.clone())),
        arg: Box::new(Exp::Var(a.clone())),
    };
    let ctx = vec![
        (aa.clone(), Exp::Sort(Sort::Set(0))),
        (
            subset.clone(),
            Exp::PowerSet {
                set: Box::new(Exp::Var(aa.clone())),
            },
        ),
        (a.clone(), Exp::Var(aa.clone())),
        (
            proof,
            Exp::Pred {
                superset: Box::new(Exp::Var(aa.clone())),
                subset: Box::new(Exp::Var(subset)),
                element: Box::new(Exp::Var(a)),
            },
        ),
        (
            constructor,
            Exp::Prod {
                var: binder,
                ty: Box::new(Exp::Var(aa)),
                body: Box::new(Exp::Sort(Sort::Set(0))),
            },
        ),
        (value.clone(), indexed_by_intro.clone()),
    ];

    assert!(!convertible(&indexed_by_intro, &indexed_by_element));
    assert!(erased_convertible(&indexed_by_intro, &indexed_by_element));
    assert!(crate::derivation::check(&ctx, &Exp::Var(value), &indexed_by_element).is_ok());
}

#[test]
fn equality_uses_the_base_carrier_of_distinct_refinements() {
    let aa = var!("A");
    let left_subset = var!("Left");
    let right_subset = var!("Right");
    let a = var!("a");
    let left_proof = var!("left_proof");
    let right_proof = var!("right_proof");
    let left_refinement = Exp::TypeLift {
        superset: Box::new(Exp::Var(aa.clone())),
        subset: Box::new(Exp::Var(left_subset.clone())),
    };
    let ctx = vec![
        (aa.clone(), Exp::Sort(Sort::Set(0))),
        (
            left_subset.clone(),
            Exp::PowerSet {
                set: Box::new(Exp::Var(aa.clone())),
            },
        ),
        (
            right_subset.clone(),
            Exp::PowerSet {
                set: Box::new(Exp::Var(aa.clone())),
            },
        ),
        (a.clone(), Exp::Var(aa.clone())),
        (
            left_proof.clone(),
            Exp::Pred {
                superset: Box::new(Exp::Var(aa.clone())),
                subset: Box::new(Exp::Var(left_subset.clone())),
                element: Box::new(Exp::Var(a.clone())),
            },
        ),
        (
            right_proof.clone(),
            Exp::Pred {
                superset: Box::new(Exp::Var(aa.clone())),
                subset: Box::new(Exp::Var(right_subset.clone())),
                element: Box::new(Exp::Var(a.clone())),
            },
        ),
    ];
    let left = Exp::SubsetIntro {
        superset: Box::new(Exp::Var(aa.clone())),
        subset: Box::new(Exp::Var(left_subset)),
        element: Box::new(Exp::Var(a.clone())),
        proof: Box::new(Exp::Var(left_proof)),
    };
    let right = Exp::SubsetIntro {
        superset: Box::new(Exp::Var(aa)),
        subset: Box::new(Exp::Var(right_subset)),
        element: Box::new(Exp::Var(a.clone())),
        proof: Box::new(Exp::Var(right_proof)),
    };
    let equality = Exp::Equal {
        left: Box::new(left.clone()),
        right: Box::new(right.clone()),
    };

    assert!(crate::derivation::check(&ctx, &Exp::Var(a), &left_refinement).is_err());
    assert!(!convertible(&left, &right));
    assert!(erased_convertible(&left, &right));
    assert!(crate::derivation::infer(&ctx, &equality).is_ok());
}

#[test]
fn equality_follows_nested_refinements_to_the_base_carrier() {
    let aa = var!("A");
    let outer_subset = var!("Outer");
    let inner_subset = var!("Inner");
    let a = var!("a");
    let deeply_refined = var!("deeply_refined");
    let outer_refinement = Exp::TypeLift {
        superset: Box::new(Exp::Var(aa.clone())),
        subset: Box::new(Exp::Var(outer_subset.clone())),
    };
    let inner_refinement = Exp::TypeLift {
        superset: Box::new(outer_refinement.clone()),
        subset: Box::new(Exp::Var(inner_subset.clone())),
    };
    let ctx = vec![
        (aa.clone(), Exp::Sort(Sort::Set(0))),
        (
            outer_subset,
            Exp::PowerSet {
                set: Box::new(Exp::Var(aa.clone())),
            },
        ),
        (
            inner_subset,
            Exp::PowerSet {
                set: Box::new(outer_refinement),
            },
        ),
        (a.clone(), Exp::Var(aa)),
        (deeply_refined.clone(), inner_refinement),
    ];
    let equality = Exp::Equal {
        left: Box::new(Exp::Var(a)),
        right: Box::new(Exp::Var(deeply_refined)),
    };

    assert!(crate::derivation::infer(&ctx, &equality).is_ok());
}

#[test]
fn identity_elimination_checks_its_explicit_premise_proofs() {
    let aa = var!("A");
    let pp = var!("P");
    let x = var!("x");
    let proof = var!("p");
    let binder = var!("y");
    let ctx = vec![
        (aa.clone(), Exp::Sort(Sort::Set(0))),
        (pp.clone(), Exp::Sort(Sort::Prop)),
        (x.clone(), Exp::Var(aa.clone())),
        (proof.clone(), Exp::Var(pp.clone())),
    ];
    let term = Exp::IdElim {
        left: Box::new(Exp::Var(x.clone())),
        right: Box::new(Exp::Var(x.clone())),
        ty: Box::new(Exp::Var(aa)),
        var: binder,
        predicate: Box::new(Exp::Var(pp.clone())),
        base: Box::new(Exp::Var(proof)),
        equality: Box::new(Exp::IdRefl {
            element: Box::new(Exp::Var(x)),
        }),
    };

    let inferred = crate::derivation::infer(&ctx, &term).unwrap();
    assert!(crate::calculus::convertible(&inferred, &Exp::Var(pp)));
}

#[test]
fn take_eq_matches_system_shape() {
    let xx = var!("X");
    let tt = var!("T");
    let f = var!("f");
    let x = var!("x");
    let exists = var!("exists");
    let unique = var!("unique");
    let x1 = var!("x1");
    let x2 = var!("x2");
    let uniqueness_ty = Exp::Prod {
        var: x1.clone(),
        ty: Box::new(Exp::Var(xx.clone())),
        body: Box::new(Exp::Prod {
            var: x2.clone(),
            ty: Box::new(Exp::Var(xx.clone())),
            body: Box::new(Exp::Equal {
                left: Box::new(app!(Exp::Var(f.clone()), Exp::Var(x1))),
                right: Box::new(app!(Exp::Var(f.clone()), Exp::Var(x2))),
            }),
        }),
    };
    let ctx = vec![
        (xx.clone(), Exp::Sort(Sort::Set(0))),
        (tt.clone(), Exp::Sort(Sort::Set(0))),
        (
            f.clone(),
            Exp::Prod {
                var: var!("_"),
                ty: Box::new(Exp::Var(xx.clone())),
                body: Box::new(Exp::Var(tt.clone())),
            },
        ),
        (x.clone(), Exp::Var(xx.clone())),
        (
            exists.clone(),
            Exp::Exists {
                set: Box::new(Exp::Var(xx.clone())),
            },
        ),
        (unique.clone(), uniqueness_ty),
    ];

    let derivation = crate::derivation::infer(
        &ctx,
        &Exp::TakeEq {
            func: Box::new(Exp::Var(f.clone())),
            domain: Box::new(Exp::Var(xx.clone())),
            codomain: Box::new(Exp::Var(tt.clone())),
            element: Box::new(Exp::Var(x.clone())),
            existence: Box::new(Exp::Var(exists.clone())),
            uniqueness: Some(Box::new(Exp::Var(unique.clone()))),
        },
    )
    .unwrap();

    let expected = Exp::Equal {
        left: Box::new(Exp::Take {
            domain: Box::new(Exp::Var(xx.clone())),
            codomain: Box::new(Exp::Var(tt.clone())),
            map: Box::new(Exp::Var(f.clone())),
            existence: Box::new(Exp::Var(exists)),
            uniqueness: Some(Box::new(Exp::Var(unique))),
        }),
        right: Box::new(Exp::App {
            func: Box::new(Exp::Var(f.clone())),
            arg: Box::new(Exp::Var(x.clone())),
        }),
    };

    assert!(crate::calculus::exp_is_alpha_eq(&derivation, &expected));
}

#[test]
fn inductive_constructor_index_out_of_bounds_fails() {
    let specs = std::rc::Rc::new(
        crate::inductive::InductiveTypeSpecs::new(
            &Context::new(),
            vec![],
            vec![],
            Sort::Set(0),
            vec![crate::inductive::CtorType {
                telescope: vec![],
                indices: vec![],
            }],
        )
        .unwrap(),
    );

    let result = crate::derivation::infer(
        &Context::new(),
        &Exp::IndCtor {
            indspec: specs,
            parameters: vec![],
            idx: 1,
        },
    );

    assert!(result.is_err());
}

// A proof is an ordinary term whose type is a proposition.
#[test]
fn proof_by_construct() {
    let mut checker = Checker::default();
    let xx = var!("X");
    let x = var!("x");
    checker.push(xx.clone(), Exp::Sort(Sort::Prop));
    checker.push(x.clone(), Exp::Var(xx.clone()));
    assert!(checker.check(&Exp::Var(x.clone()), &Exp::Var(xx.clone())));
}

// Proof by assumption is ordinary application.
#[test]
fn proof_by_assumption() {
    let mut checker = Checker::default();
    let pp1 = var!("P1");
    let pp2 = var!("P2");
    let p1 = var!("p1");
    let pm = var!("pm");

    checker.push(pp1.clone(), Exp::Sort(Sort::Prop));
    checker.push(pp2.clone(), Exp::Sort(Sort::Prop));
    checker.push(p1.clone(), Exp::Var(pp1.clone()));
    checker.push(
        pm.clone(),
        Exp::Prod {
            var: var!("_"),
            ty: Box::new(Exp::Var(pp1.clone())),
            body: Box::new(Exp::Var(pp2.clone())),
        },
    );

    let proof_term = app!(Exp::Var(pm), Exp::Var(p1));

    checker.infer(&proof_term).unwrap();
}

// Explicit proof terms need no separate goal-resolution pass.
#[test]
fn solvegoals() {
    let mut checker = Checker::default();
    let pp1 = var!("P1");
    let pp2 = var!("P2");
    let p1 = var!("p1");
    let pm = var!("pm");
    let p1impp2 = prod! {
        var: var!("_"),
        ty: Exp::Var(pp1.clone()),
        body: Exp::Var(pp2.clone()),
    };
    checker.push(pp1.clone(), Exp::Sort(Sort::Prop));
    checker.push(pp2.clone(), Exp::Sort(Sort::Prop));
    checker.push(p1.clone(), Exp::Var(pp1.clone()));
    checker.push(pm.clone(), p1impp2.clone());

    let proof_term = app!(Exp::Var(pm), Exp::Var(p1));

    checker.infer(&proof_term).unwrap();
}

// Ordinary checking uses definitional equality for proposition types.
#[test]
fn solve_goal_unfolds_defined_proposition() {
    let pp = var!("P");
    let proof = var!("p");
    let alias = Exp::DefinedConstant(Rc::new(DefinedConstant {
        ty: Exp::Sort(Sort::Prop),
        body: Exp::Var(pp.clone()),
    }));
    let ctx = vec![(pp.clone(), Exp::Sort(Sort::Prop)), (proof.clone(), alias)];

    crate::derivation::check(&ctx, &Exp::Var(proof), &Exp::Var(pp)).unwrap();
}

/*
inductive Nat : Set 0 :=
| Zero : Nat
| Succ : Nat -> Nat
*/
#[test]
fn nat_test() {
    let params = vec![];
    let indices = vec![];
    let sort = Sort::Set(0);
    let constructors = vec![
        crate::inductive::CtorType {
            telescope: vec![],
            indices: vec![],
        },
        crate::inductive::CtorType {
            telescope: vec![
                (CtorBinder::StrictPositive {
                    binders: vec![],
                    self_indices: vec![],
                }),
            ],
            indices: vec![],
        },
    ];

    let mut checker = Checker::default();
    let indspec = std::rc::Rc::new(
        checker
            .chk_indspec(params, indices, sort, constructors)
            .unwrap(),
    );
    let nat_astype = Exp::IndType {
        indspec: indspec.clone(),
        parameters: vec![],
    };
    let nat_ty = Exp::Sort(Sort::Set(0));
    checker.check(&nat_astype, &nat_ty);

    let nat_zero = Exp::IndCtor {
        indspec: indspec.clone(),
        idx: 0,
        parameters: vec![],
    };
    let nat_succ = Exp::IndCtor {
        indspec: indspec.clone(),
        idx: 1,
        parameters: vec![],
    };

    let prim_rec_nat =
        crate::inductive::InductiveTypeSpecs::primitive_recursion(&indspec, vec![], Sort::Set(0));

    println!("{:?}", prim_rec_nat);

    // motive = (n: Nat) => Nat -> Nat: (n: Nat) -> Set(0)
    let motive = lam! {
        var: var!("n"),
        ty: nat_astype.clone(),
        body: prod! {
            var: var!("m"),
            ty: nat_astype.clone(),
            body: nat_astype.clone(),
        },
    };

    let apply0 = app! {
        func: prim_rec_nat.clone(),
        arg: motive,
    };

    checker.infer(&apply0);

    // zero_case = (m: Nat) => m: motive 0
    let zero_case = {
        let m_var = var!("m");
        lam! {
            var: m_var.clone(),
            ty: nat_astype.clone(),
            body: Exp::Var(m_var.clone()),
        }
    };

    let apply1 = app! {
        func: apply0,
        arg: zero_case,
    };

    checker.infer(&apply1);

    // succ_case = (n: Nat) => (rec_n: Nat -> Nat) => (m: Nat) => Succ (rec_n m): (n: Nat) -> motive n -> motive (Succ n)
    let succ_case = {
        let n_var = var!("n");
        let rec_n_var = var!("rec_n");
        let m_var = var!("m");
        lam! {
            var: n_var,
            ty: nat_astype.clone(),
            body: lam! {
                var: rec_n_var.clone(),
                ty: prod! {
                    var: m_var.clone(),
                    ty: nat_astype.clone(),
                    body: nat_astype.clone(),
                },
                body: lam! {
                    var: m_var.clone(),
                    ty: nat_astype.clone(),
                    body: app! {
                        func: nat_succ.clone(),
                        arg: app! {
                            func: Exp::Var(rec_n_var.clone()),
                            arg: Exp::Var(m_var.clone()),
                        },
                    },
                },
            },
        }
    };

    // add: Nat -> Nat -> Nat
    let nat_add = {
        let mut app = app! {
            func: apply1,
            arg: succ_case,
        };
        loop {
            println!("Reducing: {app:?}");
            let Some(app2) = reduce_one(&app) else {
                break app;
            };
            app = app2;
        }
    };

    let ty = checker.infer(&nat_add).unwrap();
    println!("Type of nat_add: {:?}", ty);

    let nat_one = app! {
        func: nat_succ.clone(),
        arg: nat_zero.clone(),
    };

    let nat_add_zero = app! {
        func: nat_add.clone(),
        arg: nat_zero.clone(),
    };

    let nat_add_one = app! {
        func: nat_add_zero.clone(),
        arg: nat_one.clone(),
    };

    let ty = checker.infer(&nat_add_one).unwrap();
    println!("Type of nat_add_one: {:?}", ty);

    let mut nat_add_zero_one = app! {
        func: nat_add_zero.clone(),
        arg: nat_one.clone(),
    };

    let ty = checker.infer(&nat_add_zero_one).unwrap();
    println!("Type of nat_add_zero_one: {:?}", ty);
    let normalized = loop {
        println!("Reducing: {nat_add_zero_one:?}");
        let Some(next) = reduce_one(&nat_add_zero_one) else {
            break nat_add_zero_one;
        };
        nat_add_zero_one = next;
    };
    println!("Normalized nat_add_zero_one: {:?}", normalized);
}

#[test]
/*
inductive Test(A: Set): Set :=
| with_a: A -> Test
*/
fn parametrized_inductive() {
    let var_a = var!("A");
    let params = vec![(var_a.clone(), Exp::Sort(Sort::Set(0)))];
    let indices = vec![];
    let sort = Sort::Set(0);
    let constructors = vec![crate::inductive::CtorType {
        telescope: vec![CtorBinder::Simple((Var::dummy(), Exp::Var(var_a.clone())))],
        indices: vec![],
    }];
    let mut checker = Checker::default();
    let i = checker
        .chk_indspec(params, indices, sort, constructors)
        .unwrap();
    let indspec = std::rc::Rc::new(i);

    let var_b = var!("B");
    checker.push(var_b.clone(), Exp::Sort(Sort::Set(0)));

    // we expect Test[B]#with_a : B -> Test[B]
    let with_b = Exp::IndCtor {
        indspec: indspec.clone(),
        idx: 0,
        parameters: vec![Exp::Var(var_b.clone())],
    };

    let expected_ty = prod! {
        var: var!("_"),
        ty: Exp::Var(var_b.clone()),
        body: Exp::IndType {
            indspec: indspec.clone(),
            parameters: vec![Exp::Var(var_b.clone())],
        },
    };
    assert!(checker.check(&with_b, &expected_ty));
}
