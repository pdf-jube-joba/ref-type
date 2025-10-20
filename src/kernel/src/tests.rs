use crate::{
    checker::Checker,
    exp::ProveCommandBy,
    exp::{Exp, Sort, Var},
    utils,
};
// rustfmt doens not allow us variable starts with Uppercase letter
// ... => we use double lowercase letters
// e.g. A -> aa, P -> pp, P1 -> pp1 etc.

// Helper function to push variables into the context
fn push_var(checker: &mut Checker, var: &Var, ty: Exp) {
    let der = checker.push(var.clone(), ty);
    println!("{}", der);
    assert!(der.node().unwrap().is_success());
}

// Helper function to check terms
fn check_term(checker: &Checker, term: &Exp, ty: &Exp) {
    let der = checker.check(term, ty);
    println!("{}", der);
    assert!(der.node().unwrap().is_success());
}

fn prove_by(checker: &Checker, prop: &Exp, command: &ProveCommandBy) {
    // we use
    let proof_term = &Exp::ProofTermRaw {
        command: Box::new(command.clone()),
    };
    let der = checker.check(proof_term, prop);
    println!("{}", der);
    assert!(der.node().unwrap().is_success());
}

// P: \Prop |- P: \Prop
#[test]
fn p_prop() {
    let mut checker = Checker::default();
    let pp = Var::new("P");
    push_var(&mut checker, &pp, Exp::Sort(Sort::Prop));
    check_term(&checker, &Exp::Var(pp), &Exp::Sort(Sort::Prop));
}

// (P: \Prop), (p: P) |- P : \Prop
#[test]
fn no_need_elem() {
    let mut checker = Checker::default();
    let pp = Var::new("P");
    push_var(&mut checker, &pp, Exp::Sort(Sort::Prop));
    let p = Var::new("p");
    push_var(&mut checker, &p, Exp::Var(pp.clone()));
    check_term(&checker, &Exp::Var(pp), &Exp::Sort(Sort::Prop));
}

// (P1: \Prop), (P2: \Prop) |- P1 -> P2 : \Prop
#[test]
fn imp_prop() {
    let mut checker = Checker::default();
    let pp1 = Var::new("P1");
    let pp2 = Var::new("P2");
    push_var(&mut checker, &pp1, Exp::Sort(Sort::Prop));
    push_var(&mut checker, &pp2, Exp::Sort(Sort::Prop));
    check_term(
        &checker,
        &Exp::Prod {
            var: Var::new("_"),
            ty: Box::new(Exp::Var(pp1.clone())),
            body: Box::new(Exp::Var(pp2.clone())),
        },
        &Exp::Sort(Sort::Prop),
    );
}

// (P: \Prop) |- (p: P) => p: (p: P) -> P
#[test]
fn lam_prod() {
    let mut checker = Checker::default();
    let pp = Var::new("P");
    push_var(&mut checker, &pp, Exp::Sort(Sort::Prop));
    let p = Var::new("p");
    check_term(
        &checker,
        &Exp::Lam {
            var: p.clone(),
            ty: Box::new(Exp::Var(pp.clone())),
            body: Box::new(Exp::Var(p.clone())),
        },
        &Exp::Prod {
            var: p.clone(),
            ty: Box::new(Exp::Var(pp.clone())),
            body: Box::new(Exp::Var(pp.clone())),
        },
    );
}

// |- (P: \Prop) -> (p: P) -> P: \Prop
#[test]
fn impredicative_true() {
    let checker = Checker::default();
    let pp = Var::new("P");
    let p = Var::new("p");
    check_term(
        &checker,
        &Exp::Prod {
            var: pp.clone(),
            ty: Box::new(Exp::Sort(Sort::Prop)),
            body: Box::new(Exp::Prod {
                var: p.clone(),
                ty: Box::new(Exp::Var(pp.clone())),
                body: Box::new(Exp::Var(pp.clone())),
            }),
        },
        &Exp::Sort(Sort::Prop),
    );
}

// Modus ponens test
// A: \Prop, B: \Prop, f: A -> B, a: A |- f a : B
#[test]
fn modusponens_ctx() {
    let mut checker = Checker::default();
    let aa = Var::new("A");
    let bb = Var::new("B");
    let f = Var::new("f");
    let a = Var::new("a");
    push_var(&mut checker, &aa, Exp::Sort(Sort::Prop));
    push_var(&mut checker, &bb, Exp::Sort(Sort::Prop));
    push_var(
        &mut checker,
        &f,
        Exp::Prod {
            var: Var::new("_"),
            ty: Box::new(Exp::Var(aa.clone())),
            body: Box::new(Exp::Var(bb.clone())),
        },
    );
    push_var(&mut checker, &a, Exp::Var(aa.clone()));
    check_term(
        &checker,
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
    let aa = Var::new("A");
    let bb = Var::new("B");
    let f = Var::new("f");
    let a = Var::new("a");
    let telescope: Vec<(Var, Exp)> = vec![
        (aa.clone(), Exp::Sort(Sort::Prop)),
        (bb.clone(), Exp::Sort(Sort::Prop)),
        (
            f.clone(),
            Exp::Prod {
                var: Var::new("_"),
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
    check_term(&checker, &term, &ty);
}

// Alpha equivalence test
// A: \Prop |- (a: A) => a: (b: A) -> A
#[test]
fn alpha_equiv() {
    let mut checker = Checker::default();
    let aa = Var::new("A");
    let a = Var::new("a");
    let b = Var::new("b");
    push_var(&mut checker, &aa, Exp::Sort(Sort::Prop));
    check_term(
        &checker,
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
    let xx = Var::new("X");
    let x = Var::new("x");
    let yy = Var::new("Y");
    push_var(&mut checker, &xx, Exp::Sort(Sort::Prop));
    push_var(&mut checker, &x, Exp::Var(xx.clone()));
    check_term(
        &checker,
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
#[test]
fn powerset() {
    let mut checker = Checker::default();
    let xx = Var::new("X");
    push_var(&mut checker, &xx, Exp::Sort(Sort::Set(0)));
    check_term(
        &checker,
        &Exp::PowerSet {
            set: Box::new(Exp::Var(xx.clone())),
        },
        &Exp::Sort(Sort::Set(0)),
    );
}

// Proof by construct proof term
//
#[test]
fn proof_by_construct() {
    let mut checker = Checker::default();
    let xx = Var::new("X");
    let x = Var::new("x");
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
// ... generated ctx |= P1 -> P2, ctx |= P1
#[test]
fn proof_by_assumption() {
    let mut checker = Checker::default();
    let pp1 = Var::new("P1");
    let pp2 = Var::new("P2");
    let p1 = Var::new("p1");
    let pm = Var::new("pm");
    push_var(&mut checker, &pp1, Exp::Sort(Sort::Prop));
    push_var(&mut checker, &pp2, Exp::Sort(Sort::Prop));
    push_var(&mut checker, &p1, Exp::Var(pp1.clone()));
    push_var(
        &mut checker,
        &pm,
        Exp::Prod {
            var: Var::new("_"),
            ty: Box::new(Exp::Var(pp1.clone())),
            body: Box::new(Exp::Var(pp2.clone())),
        },
    );
    let proof_term = Exp::App {
        func: Box::new(Exp::ProveLater {
            prop: Box::new(Exp::Prod {
                var: Var::new("_"),
                ty: Box::new(Exp::Var(pp1.clone())),
                body: Box::new(Exp::Var(pp2.clone())),
            }),
        }),
        arg: Box::new(Exp::ProveLater {
            prop: Box::new(Exp::Var(pp1.clone())),
        }),
    };
    check_term(&checker, &proof_term, &Exp::Var(pp2.clone()));
}
