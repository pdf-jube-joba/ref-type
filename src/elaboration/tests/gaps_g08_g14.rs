use elaboration::Checker;

fn check(source: &str) -> Result<(), String> {
    let modules = syntax::parse::str_parse_modules(source).expect("valid syntax");
    let project = resolve::resolve(&modules).map_err(|error| error.to_string())?;
    Checker::default()
        .check(&project)
        .map(|_| ())
        .map_err(|error| error.to_string())
}

#[test]
fn imported_front_definitions_infer_internal_annotations() {
    for source in [
        include_str!("fixtures/gaps_g08_g14/08-01-contextual-argument.ref"),
        include_str!("fixtures/gaps_g08_g14/08-02-explicit-argument.ref"),
        include_str!("fixtures/gaps_g08_g14/08-03-bound-argument.ref"),
    ] {
        check(source).unwrap();
    }
}

#[test]
fn contextual_applications_infer_function_arguments_in_their_declared_scope() {
    for source in [
        include_str!("fixtures/gaps_g08_g14/14-01-contextual-inference.ref"),
        include_str!("fixtures/gaps_g08_g14/14-02-lambda-inference.ref"),
        include_str!("fixtures/gaps_g08_g14/14-03-explicit-inference.ref"),
    ] {
        check(source).unwrap();
    }
}

#[test]
fn contextual_applications_refine_function_types_with_repeated_arguments() {
    check(
        r"\module Repro(A: \Set) {
          \macro congr($A, $B) :=
            (\fun (law: \forall (f: $A -> $B) -> \forall (a, b: $A) -> a = b -> f a = f b) => law)
            (\fun (f: $A -> $B) => \fun (a, b: $A) => \fun (e: a = b) =>
              \idelim a = b \with x: $A => f a = f x \by { base: \refl(f a), equality: e });
          \definition identity(n: A): A := n;
          \definition mapping: A -> A -> A := \fun (n, m: A) => n;
          \definition Binary: \Set := A -> A -> A;
          \definition matches(n: A): identity (mapping n n) = identity (mapping n n) :=
            congr!{Binary A} (\fun (f: _) => identity (f n n)) _ _ (\refl(mapping));
        }",
    )
    .unwrap();
}

#[test]
fn module_argument_holes_are_checked_before_definition_expansion() {
    for argument in ["_", r"\fun (x: _) => x"] {
        let source = format!(
            r"\module Repro {{
              \inductive Unit: \Set := | unit: Unit;
              \module Pass(f: Unit -> Unit) {{}}
              \import \root.Repro[].Pass[f := {argument}] \as P;
            }}"
        );
        let error = check(&source).unwrap_err();
        assert!(
            error.contains("module arguments do not allow inference holes"),
            "{error}"
        );
    }
}

#[test]
fn imported_front_definitions_still_check_argument_types() {
    let error = check(
        r"\module Repro {
          \structure Carrier { A: \Set, }
          \definition identity(C: Carrier): C.A -> C.A := \fun (x: _) => x;
          \inductive Unit: \Set := | unit: Unit;
          \inductive Other: \Set := | other: Other;
          \definition C: Carrier := Carrier { A := Unit };
          \module Pass(f: Other -> Other) {}
          \import \root.Repro[].Pass[f := identity C] \as P;
        }",
    )
    .unwrap_err();
    assert!(
        error.contains("convertible") || error.contains("incompatible rigid"),
        "{error}"
    );
}
