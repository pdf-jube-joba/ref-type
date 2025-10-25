use crate::{
    checker::Checker,
    exp::{Exp, ProveCommandBy, ProveGoal, Sort, Var},
    utils::{self, app, lam, prod, prooflater, var},
};
// rustfmt doens not allow us variable starts with Uppercase letter
// ... => we use double lowercase letters
// e.g. A -> aa, P -> pp, P1 -> pp1 etc.

// "interactive" type checker

// Helper function to push variables into the context
fn push_var(checker: &mut Checker, var: &Var, ty: Exp) {
    checker.push(var.clone(), ty).unwrap();
    let last = checker.history().last().unwrap();
    println!("{}", last);
    assert!(last.node().unwrap().is_success());
}

// Helper function to check terms
fn check_term(checker: &mut Checker, term: &Exp, ty: &Exp) {
    checker.check(term, ty).unwrap();
    let last = checker.history().last().unwrap();
    println!("{}", last);
    assert!(last.node().unwrap().is_success());
}

// P: \Prop |- P: \Prop
#[test]
fn p_prop() {
    let mut checker = Checker::default();
    let pp = var!("P");
    push_var(&mut checker, &pp, Exp::Sort(Sort::Prop));
    check_term(&mut checker, &Exp::Var(pp), &Exp::Sort(Sort::Prop));
}

// (P: \Prop), (p: P) |- P : \Prop
#[test]
fn no_need_elem() {
    let mut checker = Checker::default();
    let pp = var!("P");
    push_var(&mut checker, &pp, Exp::Sort(Sort::Prop));
    let p = var!("p");
    push_var(&mut checker, &p, Exp::Var(pp.clone()));
    check_term(&mut checker, &Exp::Var(pp), &Exp::Sort(Sort::Prop));
}

// (P1: \Prop), (P2: \Prop) |- P1 -> P2 : \Prop
#[test]
fn imp_prop() {
    let mut checker = Checker::default();
    let pp1 = var!("P1");
    let pp2 = var!("P2");
    push_var(&mut checker, &pp1, Exp::Sort(Sort::Prop));
    push_var(&mut checker, &pp2, Exp::Sort(Sort::Prop));
    check_term(
        &mut checker,
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
    push_var(&mut checker, &pp, Exp::Sort(Sort::Prop));
    let p = var!("p");
    check_term(
        &mut checker,
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
    check_term(
        &mut checker,
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
    push_var(&mut checker, &aa, Exp::Sort(Sort::Prop));
    push_var(&mut checker, &bb, Exp::Sort(Sort::Prop));
    push_var(
        &mut checker,
        &f,
        Exp::Prod {
            var: var!("_"),
            ty: Box::new(Exp::Var(aa.clone())),
            body: Box::new(Exp::Var(bb.clone())),
        },
    );
    push_var(&mut checker, &a, Exp::Var(aa.clone()));
    check_term(
        &mut checker,
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
        push_var(&mut checker, var, ty.clone());
    }
    let term = utils::assoc_lam(
        telescope.clone(),
        Exp::App {
            func: Box::new(Exp::Var(f.clone())),
            arg: Box::new(Exp::Var(a.clone())),
        },
    );
    let ty = utils::assoc_prod(telescope, Exp::Var(bb.clone()));
    check_term(&mut checker, &term, &ty);
}

// Alpha equivalence test
// A: \Prop |- (a: A) => a: (b: A) -> A
#[test]
fn alpha_equiv() {
    let mut checker = Checker::default();
    let aa = var!("A");
    let a = var!("a");
    let b = var!("b");
    push_var(&mut checker, &aa, Exp::Sort(Sort::Prop));
    check_term(
        &mut checker,
        &Exp::Lam {
            var: a.clone(),
            ty: Box::new(Exp::Var(aa.clone())),
            body: Box::new(Exp::Var(a.clone())),
        },
        &Exp::Prod {
            var: b.clone(),
            ty: Box::new(Exp::Var(aa.clone())),
            body: Box::new(Exp::Var(aa.clone())),
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
    push_var(&mut checker, &xx, Exp::Sort(Sort::Prop));
    push_var(&mut checker, &x, Exp::Var(xx.clone()));
    check_term(
        &mut checker,
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
    push_var(&mut checker, &xx, Exp::Sort(Sort::Set(0)));
    check_term(
        &mut checker,
        &Exp::PowerSet {
            set: Box::new(Exp::Var(xx.clone())),
        },
        &Exp::Sort(Sort::Set(0)),
    );
}

// Proof by construct proof term
// X: \Prop, x: X |= X by ctx |- x: X
#[test]
fn proof_by_construct() {
    let mut checker = Checker::default();
    let xx = var!("X");
    let x = var!("x");
    push_var(&mut checker, &xx, Exp::Sort(Sort::Prop));
    push_var(&mut checker, &x, Exp::Var(xx.clone()));
    let der = checker.prove_command(&ProveCommandBy::Construct {
        proof_term: Exp::Var(x.clone()),
    });
    println!("{}", der);
    assert!(der.node().unwrap().is_success());
}

// Proof by assumption
// P1: \Prop, P2: \Prop, p1: P1, pm: P1 -> P2 |- (ProofLater(P1 -> P2) ProofLater(P1)): P2
// ... generated ctx |= P1 -> P2, ctx |= P1 (unproved)
#[test]
fn proof_by_assumption() {
    let mut checker = Checker::default();
    let pp1 = var!("P1");
    let pp2 = var!("P2");
    let p1 = var!("p1");
    let pm = var!("pm");
    push_var(&mut checker, &pp1, Exp::Sort(Sort::Prop));
    push_var(&mut checker, &pp2, Exp::Sort(Sort::Prop));
    push_var(&mut checker, &p1, Exp::Var(pp1.clone()));
    push_var(
        &mut checker,
        &pm,
        Exp::Prod {
            var: var!("_"),
            ty: Box::new(Exp::Var(pp1.clone())),
            body: Box::new(Exp::Var(pp2.clone())),
        },
    );
    let proof_term = Exp::App {
        func: Box::new(Exp::ProveLater {
            prop: Box::new(Exp::Prod {
                var: var!("_"),
                ty: Box::new(Exp::Var(pp1.clone())),
                body: Box::new(Exp::Var(pp2.clone())),
            }),
        }),
        arg: Box::new(Exp::ProveLater {
            prop: Box::new(Exp::Var(pp1.clone())),
        }),
    };

    // check without proof
    check_term(&mut checker, &proof_term, &Exp::Var(pp2.clone()));

    // check with proof by cast and proofrawterm
    let proof_term = {
        // ProofLater(P1 -> P2) ProofLater(P1))
        let exp = app! {
            func: prooflater!(
                prod!{
                    var: var!("_"),
                    ty: Exp::Var(pp1.clone()),
                    body: Exp::Var(pp2.clone()),
                }
            ),
            arg: prooflater!(Exp::Var(pp1.clone())),
        };
        let castto = Exp::Var(pp2.clone());

        Exp::Cast {
            exp: Box::new(exp),
            to: Box::new(castto),
        }
    };

    let der = checker.infer(&proof_term).unwrap();
    println!("{}", der);
}

// same but in Exp::Cast and solve all goals
// P1: \Prop, P2: \Prop, p1: P1, pm: P1 -> P2 |- (ProofLater(P1 -> P2) ProofLater(P1)): P2
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
    push_var(&mut checker, &pp1, Exp::Sort(Sort::Prop));
    push_var(&mut checker, &pp2, Exp::Sort(Sort::Prop));
    push_var(&mut checker, &p1, Exp::Var(pp1.clone()));
    push_var(&mut checker, &pm, p1impp2.clone());

    let proof_term = {
        // ProofLater(P1 -> P2) ProofLater(P1))
        let exp = app! {
            func: prooflater!(
                prod!{
                    var: var!("_"),
                    ty: Exp::Var(pp1.clone()),
                    body: Exp::Var(pp2.clone()),
                }
            ),
            arg: prooflater!(Exp::Var(pp1.clone())),
        };
        let goals: Vec<_> = vec![
            ProveGoal {
                extended_ctx: vec![].into(),
                goal_prop: p1impp2.clone(),
                proof_term: Exp::ProofTermRaw {
                    command: Box::new(ProveCommandBy::Construct {
                        proof_term: Exp::Var(pm.clone()),
                    }),
                },
            },
            ProveGoal {
                extended_ctx: vec![].into(),
                goal_prop: Exp::Var(pp1.clone()),
                proof_term: Exp::ProofTermRaw {
                    command: Box::new(ProveCommandBy::Construct {
                        proof_term: Exp::Var(p1.clone()),
                    }),
                },
            },
        ];

        Exp::ProveHere {
            exp: Box::new(exp),
            goals,
        }
    };

    let der = checker.infer(&proof_term).unwrap();
    println!("{}", der);
}
