use crate::{elaborator::GlobalEnvironment, parse};

#[test]
fn subset_intro_construction_and_reuse() {
    let source = r#"
        \module NamedSubset(A: \Set(0)) {
            \definition XSet: \Power(A) := \Subset(x, A, x = x);
            \definition X: \Set(0) := \Ty(A, XSet);
            \definition make: (x: A) -> X :=
                (x: A) => \subsetinto(A, XSet, x, \refl(x));
            \definition reuse: (x: X) -> X := (x: X) => x;
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();

    environment.add_new_module_to_root(&modules[0]).unwrap();
}

#[test]
fn subset_intro_rejects_wrong_membership_proof() {
    let source = r#"
        \module NamedSubset(A: \Set(0)) {
            \definition XSet: \Power(A) := \Subset(x, A, x = x);
            \definition X: \Set(0) := \Ty(A, XSet);
            \definition bad: (x: A) -> X :=
                (x: A) => \subsetinto(A, XSet, x, x);
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();

    assert!(environment.add_new_module_to_root(&modules[0]).is_err());
}

#[test]
fn subset_intro_syntax_requires_an_explicit_proof() {
    let source = r#"
        \module NamedSubset(A: \Set(0)) {
            \definition XSet: \Power(A) := \Subset(x, A, x = x);
            \definition X: \Set(0) := \Ty(A, XSet);
            \definition bad: (x: A) -> X :=
                (x: A) => \subsetinto(A, XSet, x);
        }
    "#;
    assert!(parse::str_parse_modules(source).is_err());
}
