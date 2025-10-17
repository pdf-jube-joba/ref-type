use crate::{
    checker::Checker,
    exp::{Exp, Var, Sort},
};

// check (P: Prop), (p: P) |- P : Prop ... success
#[test]
fn test1() {
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
    let (der, b) = checker.check(
        &Exp::Var(pp.clone()),
        &Exp::Sort(Sort::Prop),
        vec![],
    );
    println!("{}", der);
    assert!(b);
}

// check (P: Prop), (p: P) |- p : Prop ... fail
#[test]
fn test2() {
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
    // check p : Prop without proof
    let (der, b) = checker.check(
        &Exp::Var(p.clone()),
        &Exp::Sort(Sort::Prop),
        vec![],
    );
    println!("{}", der);
    assert!(!b);
}

// check (P: Prop) |- (p: P)  => p: (p: P) -> P ... success
#[test]
fn test3() {
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
        vec![],
    );
    println!("{}", der);
    assert!(b);
}

// check |- (P: Prop) -> (p: P) -> P: Prop ... success
#[test]
fn test4() {
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
        vec![],
    );
    println!("{}", der);
    assert!(b);
}

// modus ponens test
// (A: Prop), (B: Prop), (f: A -> B), (a: A) |- f a : B ... success
#[test]
fn test5() {
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
        vec![],
    );
    println!("{}", der);
    assert!(b5);
}
