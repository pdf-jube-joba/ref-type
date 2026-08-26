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

#[test]
fn general_recursion_surface_typechecks_and_normalizes() {
    let source = r#"
        \module GeneralRecursion(
            A: \VType,
            B: \VType,
            f: \U(\CFun(A, \F(\RunStep(A, B)))),
            a: A,
            p: \Acc(A, B, f, \RfTerm(A, a))
        ) {
            \definition result: \F(B) := \run(A, B, f, a, p);
            \normalize \run(A, B, f, a, p);
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();

    environment.add_new_module_to_root(&modules[0]).unwrap();
}

#[test]
fn accessibility_proof_constructor_syntax_is_reserved_and_parsed() {
    let source = r#"
        \module AccSyntax(
            A: \VType,
            B: \VType,
            f: \U(\CFun(A, \F(\RunStep(A, B)))),
            a: \RfType(A),
            b: \RfType(A),
            p: \Prop,
            q: \Prop,
            e: \Prop
        ) {
            \infer \accintro(A, B, f, a, q);
            \infer \accdescent(A, B, f, a, b, p, e);
        }
    "#;

    parse::str_parse_modules(source).unwrap();
}

#[test]
fn accessibility_intro_and_descent_follow_the_system_premises() {
    let source = r#"
        \module AccProofs(
            A: \VType,
            B: \VType,
            f: \U(\CFun(A, \F(\RunStep(A, B)))),
            a: \RfType(A),
            b: \RfType(A),
            predecessors:
                (next: \RfType(A)) ->
                ((\RfTerm(\U(\CFun(A, \F(\RunStep(A, B)))), f)) a =
                 (\RfTerm(\U(\CFun(A, \F(\RunStep(A, B)))),
                     \thunk(\clam(x, A, \return(\continue(A, B, x)))))) next) ->
                \Acc(A, B, f, next),
            p: \Acc(A, B, f, a),
            edge:
                (\RfTerm(\U(\CFun(A, \F(\RunStep(A, B)))), f)) a =
                (\RfTerm(\U(\CFun(A, \F(\RunStep(A, B)))),
                    \thunk(\clam(x, A, \return(\continue(A, B, x)))))) b
        ) {
            \definition introduced: \Acc(A, B, f, a) :=
                \accintro(A, B, f, a, predecessors);
            \definition descended: \Acc(A, B, f, b) :=
                \accdescent(A, B, f, a, b, p, edge);
        }
    "#;
    let modules = parse::str_parse_modules(source).unwrap();
    let mut environment = GlobalEnvironment::default();

    environment.add_new_module_to_root(&modules[0]).unwrap();
}
