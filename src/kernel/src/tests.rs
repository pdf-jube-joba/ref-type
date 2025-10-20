use crate::{
    checker::Checker,
    exp::{Exp, Sort, Var},
    utils,
};

use crate::exp::ProveCommandBy;

// P: Prop |- P: Prop
#[test]
fn p_prop() {
    let mut checker = Checker::default();
    let p = Var::new("P");
    let (der, b) = checker.push(p.clone(), Exp::Sort(Sort::Prop));
    println!("{}", der);
    assert!(b);
    let (der, b) = checker.check(&Exp::Var(p.clone()), &Exp::Sort(Sort::Prop));
    println!("{}", der);
    assert!(b);
}

// (P: Prop), (p: P) |- P : Prop
#[test]
fn no_need_elem() {
    // push (P: Prop)
    let mut checker = Checker::default();
    let pp = Var::new("P");
    let (der, b) = checker.push(pp.clone(), Exp::Sort(Sort::Prop));
    println!("{}", der);
    assert!(b);
    // push (p: P)
    let p = Var::new("p");
    let (der, b) = checker.push(p.clone(), Exp::Var(pp.clone()));
    println!("{}", der);
    assert!(b);
    // check P : Prop without proof
    let (der, b) = checker.check(&Exp::Var(pp.clone()), &Exp::Sort(Sort::Prop));
    println!("{}", der);
    assert!(b);
}

// (P1: Prop), (P2: Prop) |- P1 -> P2 : Prop
#[test]
fn imp_prop() {
    let mut checker = Checker::default();
    let p1 = Var::new("P1");
    let p2 = Var::new("P2");
    // push (P1: Prop)
    let (der, b) = checker.push(p1.clone(), Exp::Sort(Sort::Prop));
    println!("{}", der);
    assert!(b);
    // push (P2: Prop)
    let (der, b) = checker.push(p2.clone(), Exp::Sort(Sort::Prop));
    println!("{}", der);
    assert!(b);
    // check P1 -> P2 : Prop without proof
    let (der, b) = checker.check(
        &Exp::Prod {
            var: Var::new("_"),
            ty: Box::new(Exp::Var(p1.clone())),
            body: Box::new(Exp::Var(p2.clone())),
        },
        &Exp::Sort(Sort::Prop),
    );
    println!("{}", der);
    assert!(b);
}

// (P: Prop) |- (p: P)  => p: (p: P) -> P
#[test]
fn lam_prod() {
    // push (P: Prop)
    let mut checker = Checker::default();
    let pp = Var::new("P");
    let (der, b) = checker.push(pp.clone(), Exp::Sort(Sort::Prop));
    println!("{}", der);
    assert!(b);
    // check (p: P)  => p: (p: P) -> P without proof
    let p = Var::new("p");
    let (der, b) = checker.check(
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
    println!("{}", der);
    assert!(b);
}

// |- (P: Prop) -> (p: P) -> P: Prop
#[test]
fn impredicative_true() {
    let mut checker = Checker::default();
    let pp = Var::new("P");
    let p = Var::new("p");
    let (der, b) = checker.check(
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
    println!("{}", der);
    assert!(b);
}

// modus ponens test
// (A: Prop), (B: Prop), (f: A -> B), (a: A) |- f a : B
#[test]
fn modusponens_ctx() {
    let mut checker = Checker::default();
    let a = Var::new("A");
    let b = Var::new("B");
    let f = Var::new("f");
    let aa = Var::new("a");
    // push (A: Prop)
    let (_, b1) = checker.push(a.clone(), Exp::Sort(Sort::Prop));
    assert!(b1);
    // push (B: Prop)
    let (_, b2) = checker.push(b.clone(), Exp::Sort(Sort::Prop));
    assert!(b2);
    // push (f: A -> B)
    let (_, b3) = checker.push(
        f.clone(),
        Exp::Prod {
            var: Var::new("_"),
            ty: Box::new(Exp::Var(a.clone())),
            body: Box::new(Exp::Var(b.clone())),
        },
    );
    assert!(b3);
    // push (a: A)
    let (_, b4) = checker.push(aa.clone(), Exp::Var(a.clone()));
    assert!(b4);
    // check f a : B without proof
    let (der, b5) = checker.check(
        &Exp::App {
            func: Box::new(Exp::Var(f.clone())),
            arg: Box::new(Exp::Var(aa.clone())),
        },
        &Exp::Var(b.clone()),
    );
    println!("{}", der);
    assert!(b5);
}

// modus ponens test2
// |- (A: Prop) => (B: Prop) => (f: A -> B) => (a: A) => f a
//      : (A: Prop) -> (B: Prop) -> (f: A -> B) -> (a: A) -> B
#[test]
fn modusponens_popped() {
    let mut checker = Checker::default();
    let a = Var::new("A");
    let b = Var::new("B");
    let f = Var::new("f");
    let aa = Var::new("a");
    let telescope: Vec<(Var, Exp)> = vec![
        (a.clone(), Exp::Sort(Sort::Prop)),
        (b.clone(), Exp::Sort(Sort::Prop)),
        (
            f.clone(),
            Exp::Prod {
                var: Var::new("_"),
                ty: Box::new(Exp::Var(a.clone())),
                body: Box::new(Exp::Var(b.clone())),
            },
        ),
        (aa.clone(), Exp::Var(a.clone())),
    ];
    for (var, ty) in telescope.iter() {
        let (_, b) = checker.push(var.clone(), ty.clone());
        assert!(b);
    }

    let term = utils::assoc_lam(
        telescope.clone(),
        Exp::App {
            func: Box::new(Exp::Var(f.clone())),
            arg: Box::new(Exp::Var(aa.clone())),
        },
    );
    let ty = utils::assoc_prod(telescope, Exp::Var(b.clone()));

    let (der, b) = checker.check(&term, &ty);
    println!("{}", der);
    assert!(b);
}

// alpha equivalence test
// A: Prop |- (a: A) => a: (b: A) -> A
#[test]
fn alpha_equiv() {
    let mut checker = Checker::default();
    let a = Var::new("A");
    let aa = Var::new("a");
    let bb = Var::new("b");
    // push (A: Prop)
    let (_, b1) = checker.push(a.clone(), Exp::Sort(Sort::Prop));
    assert!(b1);
    // check (a: A) => a: (b: A) -> A without proof
    let (der, b2) = checker.check(
        &Exp::Lam {
            var: aa.clone(),
            ty: Box::new(Exp::Var(a.clone())),
            body: Box::new(Exp::Var(aa.clone())),
        },
        &Exp::Prod {
            var: bb.clone(),
            ty: Box::new(Exp::Var(a.clone())),
            body: Box::new(Exp::Var(a.clone())),
        },
    );
    println!("{}", der);
    assert!(b2);
}

// type level reduction
// X: Prop, x: X |- x: ((Y: Prop) => Y) X
#[test]
fn type_leve_reduction() {
    let mut checker = Checker::default();
    let x = Var::new("X");
    let xx = Var::new("x");
    let y = Var::new("Y");
    // push (X: Prop)
    let (_, b1) = checker.push(x.clone(), Exp::Sort(Sort::Prop));
    assert!(b1);
    // push (x: X)
    let (_, b2) = checker.push(xx.clone(), Exp::Var(x.clone()));
    assert!(b2);
    // check x: ((Y: Prop) => Y) X without proof
    let (der, b3) = checker.check(
        &Exp::Var(xx.clone()),
        &Exp::App {
            func: Box::new(Exp::Lam {
                var: y.clone(),
                ty: Box::new(Exp::Sort(Sort::Prop)),
                body: Box::new(Exp::Var(y.clone())),
            }),
            arg: Box::new(Exp::Var(x.clone())),
        },
    );
    println!("{}", der);
    assert!(b3);
}

// proof by construct proof term
// X: Prop, x: X |= X by construct x
#[test]
fn proof_by_exact() {
    let mut checker = Checker::default();
    let xx = Var::new("X");
    let x = Var::new("x");
    // push (X: Prop)
    let (_, b1) = checker.push(xx.clone(), Exp::Sort(Sort::Prop));
    assert!(b1);
    // push (x: X)
    let (_, b2) = checker.push(x.clone(), Exp::Var(xx.clone()));
    assert!(b2);
    // prove X by consrsuct x
    let (der, b3) = checker.prove_command(&ProveCommandBy::Construct {
        proof_term: Exp::Var(x.clone()),
    });
    println!("{}", der);
    assert!(b3);
}

// Power set
// X: Set(0) |- Power(X): Set(0)
#[test]
fn powerset() {
    let mut checker = Checker::default();
    let x = Var::new("X");
    // push (X: Set(0))
    let (_, b1) = checker.push(x.clone(), Exp::Sort(Sort::Set(0)));
    assert!(b1);
    // check P(X): Set(0) without proof
    let (der, b2) = checker.check(
        &Exp::PowerSet {
            set: Box::new(Exp::Var(x.clone())),
        },
        &Exp::Sort(Sort::Set(0)),
    );
    println!("{}", der);
    assert!(b2);
}
