use crate::{
    checker::Checker,
    exp::ProveCommandBy,
    exp::{Exp, Sort, Var},
    utils,
};

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

// P: Prop |- P: Prop
#[test]
fn p_prop() {
    let mut checker = Checker::default();
    let p = Var::new("P");
    push_var(&mut checker, &p, Exp::Sort(Sort::Prop));
    check_term(&checker, &Exp::Var(p), &Exp::Sort(Sort::Prop));
}

// (P: Prop), (p: P) |- P : Prop
#[test]
fn no_need_elem() {
    let mut checker = Checker::default();
    let pp = Var::new("P");
    push_var(&mut checker, &pp, Exp::Sort(Sort::Prop));
    let p = Var::new("p");
    push_var(&mut checker, &p, Exp::Var(pp.clone()));
    check_term(&checker, &Exp::Var(pp), &Exp::Sort(Sort::Prop));
}

// (P1: Prop), (P2: Prop) |- P1 -> P2 : Prop
#[test]
fn imp_prop() {
    let mut checker = Checker::default();
    let p1 = Var::new("P1");
    let p2 = Var::new("P2");
    push_var(&mut checker, &p1, Exp::Sort(Sort::Prop));
    push_var(&mut checker, &p2, Exp::Sort(Sort::Prop));
    check_term(
        &checker,
        &Exp::Prod {
            var: Var::new("_"),
            ty: Box::new(Exp::Var(p1.clone())),
            body: Box::new(Exp::Var(p2.clone())),
        },
        &Exp::Sort(Sort::Prop),
    );
}

// (P: Prop) |- (p: P) => p: (p: P) -> P
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

// |- (P: Prop) -> (p: P) -> P: Prop
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
#[test]
fn modusponens_ctx() {
    let mut checker = Checker::default();
    let a = Var::new("A");
    let b = Var::new("B");
    let f = Var::new("f");
    let aa = Var::new("a");
    push_var(&mut checker, &a, Exp::Sort(Sort::Prop));
    push_var(&mut checker, &b, Exp::Sort(Sort::Prop));
    push_var(
        &mut checker,
        &f,
        Exp::Prod {
            var: Var::new("_"),
            ty: Box::new(Exp::Var(a.clone())),
            body: Box::new(Exp::Var(b.clone())),
        },
    );
    push_var(&mut checker, &aa, Exp::Var(a.clone()));
    check_term(
        &checker,
        &Exp::App {
            func: Box::new(Exp::Var(f.clone())),
            arg: Box::new(Exp::Var(aa.clone())),
        },
        &Exp::Var(b.clone()),
    );
}

// Modus ponens test with abstraction
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
        push_var(&mut checker, var, ty.clone());
    }
    let term = utils::assoc_lam(
        telescope.clone(),
        Exp::App {
            func: Box::new(Exp::Var(f.clone())),
            arg: Box::new(Exp::Var(aa.clone())),
        },
    );
    let ty = utils::assoc_prod(telescope, Exp::Var(b.clone()));
    check_term(&checker, &term, &ty);
}

// Alpha equivalence test
#[test]
fn alpha_equiv() {
    let mut checker = Checker::default();
    let a = Var::new("A");
    let aa = Var::new("a");
    let bb = Var::new("b");
    push_var(&mut checker, &a, Exp::Sort(Sort::Prop));
    check_term(
        &checker,
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
}

// Type-level reduction
#[test]
fn type_level_reduction() {
    let mut checker = Checker::default();
    let x = Var::new("X");
    let xx = Var::new("x");
    let y = Var::new("Y");
    push_var(&mut checker, &x, Exp::Sort(Sort::Prop));
    push_var(&mut checker, &xx, Exp::Var(x.clone()));
    check_term(
        &checker,
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
}

// Proof by construct proof term
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

// Power set
#[test]
fn powerset() {
    let mut checker = Checker::default();
    let x = Var::new("X");
    push_var(&mut checker, &x, Exp::Sort(Sort::Set(0)));
    check_term(
        &checker,
        &Exp::PowerSet {
            set: Box::new(Exp::Var(x.clone())),
        },
        &Exp::Sort(Sort::Set(0)),
    );
}
