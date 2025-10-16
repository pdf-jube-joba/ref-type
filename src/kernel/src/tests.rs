use crate::{checker::Checker, exp::{Exp, Var}};

#[test]
fn test1() {
    let mut checker = Checker::default();
    let (der, b) = checker.push(Var::new("x"), Exp::Sort(crate::exp::Sort::Prop));
    assert!(b);
    println!("{der}");
}