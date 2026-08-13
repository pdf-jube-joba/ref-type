use crate::{
    calculus::reduce_one,
    exp::{Context, DefinedConstant, Exp, JudgementSuccess, Sort, SuccessHead, Var},
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
    derivations: Vec<JudgementSuccess>,
}

impl Checker {
    fn history(&self) -> &Vec<JudgementSuccess> {
        &self.derivations
    }
    fn check(&mut self, term: &Exp, ty: &Exp) -> bool {
        let derivation = crate::derivation::check(&self.context, term, ty);
        match derivation {
            Ok(success) => {
                self.derivations.push(success);
                true
            }
            Err(fail_der) => {
                print!("Type checking failed:\n{:?}", fail_der);
                false
            }
        }
    }
    fn infer(&mut self, term: &Exp) -> Option<Exp> {
        let derivation = crate::derivation::infer(&self.context, term);

        let ty = match derivation {
            Ok(derivation) => {
                if let JudgementSuccess {
                    head: SuccessHead::TypeJudgement { ty, .. },
                    ..
                } = &derivation
                {
                    self.derivations.push(derivation.clone());
                    ty.clone()
                } else {
                    panic!("Expected TypeJudgement");
                }
            }
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
        let indspecs = crate::inductive::InductiveTypeSpecs {
            parameters: params.clone(),
            indices: indices.clone(),
            sort,
            constructors: constructors.clone(),
        };
        let _res = crate::inductive::acceptable_typespecs(&self.context, &indspecs).unwrap();
        self.derivations.push(_res);
        Ok(indspecs)
    }
    fn push(&mut self, var: Var, ty: Exp) {
        let der = crate::derivation::infer_sort(&self.context, &ty).unwrap();
        self.derivations.push(der);
        self.context.push((var, ty));
    }
    fn print_all(&self) {
        for der in self.history().iter() {
            println!("{:?}", der);
        }
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

    let (_, fail) = crate::derivation::check_wellformed_ctx(&ctx);

    assert!(fail.is_some());
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
        derivation.type_of().unwrap(),
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
fn refinement_cast_rejects_missing_membership_proof() {
    let aa = var!("A");
    let subset = var!("S");
    let x = var!("x");
    let ctx = vec![
        (aa.clone(), Exp::Sort(Sort::Set(0))),
        (
            subset.clone(),
            Exp::PowerSet {
                set: Box::new(Exp::Var(aa.clone())),
            },
        ),
        (x.clone(), Exp::Var(aa.clone())),
    ];
    let cast = Exp::Cast {
        exp: Box::new(Exp::Var(x)),
        to: Box::new(Exp::TypeLift {
            superset: Box::new(Exp::Var(aa)),
            subset: Box::new(Exp::Var(subset)),
        }),
        proof: None,
    };

    assert!(crate::derivation::infer(&ctx, &cast).is_err());
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
    assert!(crate::calculus::convertible(
        inferred.type_of().unwrap(),
        &Exp::Var(pp)
    ));
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

    assert!(crate::calculus::exp_is_alpha_eq(
        derivation.type_of().unwrap(),
        &expected
    ));
}

#[test]
fn inductive_constructor_index_out_of_bounds_fails() {
    let specs = std::rc::Rc::new(crate::inductive::InductiveTypeSpecs {
        parameters: vec![],
        indices: vec![],
        sort: Sort::Set(0),
        constructors: vec![crate::inductive::CtorType {
            telescope: vec![],
            indices: vec![],
        }],
    });

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
    for der in checker.history().iter() {
        println!("{:?}", der);
    }
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
    checker.print_all();
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
