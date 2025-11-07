use crate::{
    calculus::exp_is_alpha_eq,
    exp::{Context, DerivationSuccess, Exp, ProveCommandBy, ProveGoal, Sort, Var},
    inductive::CtorBinder,
    utils::{self, app, lam, prod, prooflater, var},
};
// rustfmt doens not allow us variable starts with Uppercase letter
// ... => we use double lowercase letters
// e.g. A -> aa, P -> pp, P1 -> pp1 etc.

#[derive(Debug, Default)]
pub struct Checker {
    context: Context,
    derivations: Vec<DerivationSuccess>,
}

impl Checker {
    fn history(&self) -> &Vec<DerivationSuccess> {
        &self.derivations
    }
    fn check(&mut self, term: &Exp, ty: &Exp) -> bool {
        let derivation = crate::derivation::check(&self.context, term, ty).unwrap();
        self.derivations.push(derivation);
        true
    }
    fn infer(&mut self, term: &Exp) -> Option<Exp> {
        let derivation = crate::derivation::infer(&self.context, term).unwrap();
        let ty = {
            if let DerivationSuccess::TypeJudgement { ty, .. } = &derivation {
                ty.clone()
            } else {
                panic!("Expected TypeJudgement");
            }
        };
        self.derivations.push(derivation);
        Some(ty)
    }
    fn prove_command(&self, command: &ProveCommandBy) {
        crate::derivation::prove_command(&self.context, command).unwrap();
    }
    fn chk_indspec(
        &mut self,
        params: Vec<(Var, Exp)>,
        indices: Vec<(Var, Exp)>,
        sort: crate::exp::Sort,
        constructors: Vec<crate::inductive::CtorType>,
    ) -> Result<crate::inductive::InductiveTypeSpecs, String> {
        let indspecs = crate::inductive::InductiveTypeSpecs {
            names: (String::new(), vec![String::new(); constructors.len()]),
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

// Proof by construct proof term
// X: \Prop, x: X |= X by ctx |- x: X
#[test]
fn proof_by_construct() {
    let mut checker = Checker::default();
    let xx = var!("X");
    let x = var!("x");
    checker.push(xx.clone(), Exp::Sort(Sort::Prop));
    checker.push(x.clone(), Exp::Var(xx.clone()));
    checker.prove_command(&ProveCommandBy::Construct(Exp::Var(x.clone())));
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

    checker.infer(&proof_term).unwrap();
    for der in checker.history().iter() {
        println!("{:?}", der);
    }
}

// // same but in Exp::Cast and solve all goals
// // P1: \Prop, P2: \Prop, p1: P1, pm: P1 -> P2 |- (ProofLater(P1 -> P2) ProofLater(P1)): P2
// #[test]
// fn solvegoals() {
//     let mut checker = Checker::default();
//     let pp1 = var!("P1");
//     let pp2 = var!("P2");
//     let p1 = var!("p1");
//     let pm = var!("pm");
//     let p1impp2 = prod! {
//         var: var!("_"),
//         ty: Exp::Var(pp1.clone()),
//         body: Exp::Var(pp2.clone()),
//     };
//     push_var(&mut checker, &pp1, Exp::Sort(Sort::Prop));
//     push_var(&mut checker, &pp2, Exp::Sort(Sort::Prop));
//     push_var(&mut checker, &p1, Exp::Var(pp1.clone()));
//     push_var(&mut checker, &pm, p1impp2.clone());

//     let proof_term = {
//         // ProofLater(P1 -> P2) ProofLater(P1))
//         let exp = app! {
//             func: prooflater!(
//                 prod!{
//                     var: var!("_"),
//                     ty: Exp::Var(pp1.clone()),
//                     body: Exp::Var(pp2.clone()),
//                 }
//             ),
//             arg: prooflater!(Exp::Var(pp1.clone())),
//         };
//         let goals: Vec<_> = vec![
//             ProveGoal {
//                 extended_ctx: vec![],
//                 goal_prop: p1impp2.clone(),
//                 command: ProveCommandBy::Construct(Exp::Var(pm.clone())),
//             },
//             ProveGoal {
//                 extended_ctx: vec![],
//                 goal_prop: Exp::Var(pp1.clone()),
//                 command: ProveCommandBy::Construct(Exp::Var(p1.clone())),
//             },
//         ];

//         Exp::ProveHere {
//             exp: Box::new(exp),
//             goals,
//         }
//     };

//     infer_term(&mut checker, &proof_term, &Exp::Var(pp2.clone()));
// }

// /*
// inductive Nat : Set 0 :=
// | Zero : Nat
// | Succ : Nat -> Nat
// */
// #[test]
// fn nat_test() {
//     let params = vec![];
//     let indices = vec![];
//     let sort = Sort::Set(0);
//     let constructors = vec![
//         crate::inductive::CtorType {
//             telescope: vec![],
//             indices: vec![],
//         },
//         crate::inductive::CtorType {
//             telescope: vec![
//                 (CtorBinder::StrictPositive {
//                     binders: vec![],
//                     self_indices: vec![],
//                 }),
//             ],
//             indices: vec![],
//         },
//     ];

//     let mut checker = Checker::default();
//     let _indspecs = std::rc::Rc::new(
//         checker
//             .chk_indspec(params, indices, sort, constructors)
//             .unwrap(),
//     );

//     checker.history().iter().for_each(|der| {
//         println!("{}", der);
//         assert!(der.is_success());
//     });
// }
