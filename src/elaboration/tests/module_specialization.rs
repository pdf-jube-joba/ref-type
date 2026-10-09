use elaboration::Checker;

fn check(source: &str) -> Result<(), String> {
    let modules = syntax::parse::str_parse_modules(source).map_err(|error| error.to_string())?;
    let project = resolve::resolve(&modules).map_err(|error| error.to_string())?;
    Checker::default()
        .check(&project)
        .map(|_| ())
        .map_err(|error| error.to_string())
}

#[test]
fn temporary_namespace_structure_fields() {
    check(include_str!(
        "fixtures/module_specialization/temporary-field.ref"
    ))
    .unwrap();
    check(include_str!(
        "fixtures/module_specialization/named-field.ref"
    ))
    .unwrap();
}

#[test]
fn structure_family_substitutes_function_arguments() {
    check(include_str!(
        "fixtures/module_specialization/structure-family.ref"
    ))
    .unwrap();
    check(include_str!(
        "fixtures/module_specialization/named-piece.ref"
    ))
    .unwrap();
}

#[test]
fn structure_family_preserves_distinct_indices_and_local_binders() {
    let source = r"\module Shapes {
        \structure Bundle { Carrier: \Set, }
    }
    \module Family(I: \Set, types: I -> \Set) {
        \import \root.Shapes[] \as Shapes;
        \module At(i: I) {
            \definition Carrier: \Set := types i;
            \definition bundle: Shapes.Bundle := Shapes.Bundle { Carrier := Carrier };
        }
        \definition bundle(i: I): Shapes.Bundle := At[i := i].bundle;
        \module Client(j, k: I, x: types j, y: types k) {
            \definition left: (bundle j).Carrier := x;
            \definition right: (bundle k).Carrier := y;
            \definition local(i: I)(value: types i): (bundle i).Carrier := value;
            \definition underLambda: \forall (i: I) -> (bundle i).Carrier -> types i :=
                \fun (i: I) (value: (bundle i).Carrier) => value;
        }
    }
    \module Consumer(J: \Set, family: J -> \Set) {
        \import \root.Family[I := J, types := family] \as F;
        \definition identity(j: J)(x: family j): (F.bundle j).Carrier := x;
    }";
    check(source).unwrap();
    let wrong = source.replace("(bundle k).Carrier := y", "(bundle k).Carrier := x");
    let error = check(&wrong).unwrap_err();
    assert!(error.contains("types are not convertible"), "{error}");
}

#[test]
fn selected_namespace_classifiers_follow_carriers_and_record_fields() {
    check(
        r"\module Structures {
        \structure Topology[Carrier: \Set]: \Set { openSets: \Pow (\Pow Carrier), }
    }
    \module Topology(Carrier: \Set) {
        \definition Topology: \Set := \root.Structures[].Topology[Carrier];
        \definition Good(space: Topology): \Prop := space = space;
    }
    \module Chart(M: \Set, space: \root.Topology[Carrier := M].Topology) {
        \definition Chart: \Set := M;
    }
    \module Example {
        \definition ChartType(M: \Set)(space: \root.Structures[].Topology[M]): \Set :=
            \root.Chart[M := M, space := space].Chart;
        \structure Manifold {
            Point: \Set,
            space: \root.Topology[Carrier := Point].Topology,
            good: \root.Topology[Carrier := Point].Good space,
        }
        \definition manifold(A: \Set)(s: \root.Structures[].Topology[A]): Manifold :=
            Manifold { Point := A, space := s, good := \refl(s) };
        \definition identity(A: \Set)(s: \root.Structures[].Topology[A])(x: A):
            (manifold A s).Point := x;
    }",
    )
    .unwrap();
}

#[test]
fn selected_namespace_functions_preserve_degree_under_lambdas() {
    check(
        r"\module Repro {
        \inductive Nat: \Set := | zero: Nat | succ: Nat -> Nat;
        \module At(n: Nat) {
            \definition Carrier: \Set := \Cast[Nat] ({ k: Nat \where k = n });
            \definition identity(x: Carrier): Carrier := x;
        }
        \definition apply(n: Nat)(x: At[n := n].Carrier): At[n := n].Carrier :=
            At[n := n].identity x;
        \definition underLambda: \forall (n: Nat) -> At[n := n].Carrier -> At[n := n].Carrier :=
            \fun (n: Nat) (x: At[n := n].Carrier) => At[n := n].identity x;
    }",
    )
    .unwrap();
}

#[test]
fn structure_families_preserve_nested_named_import_arguments() {
    check(
        r"\module Shapes { \structure Bundle { Carrier: \Set, } }
    \module Family(I: \Set, types: I -> \Set) {
        \import \root.Shapes[] \as Shapes;
        \module At(i: I) {
            \definition Carrier: \Set := types i;
            \definition bundle: Shapes.Bundle := Shapes.Bundle { Carrier := Carrier };
        }
        \module From(i: I) {
            \import \parent.At[i := i] \as Chosen;
            \definition bundle: Shapes.Bundle := Chosen.bundle;
        }
        \definition bundle(i: I): Shapes.Bundle := From[i := i].bundle;
    }
    \module Consumer(J: \Set, family: J -> \Set) {
        \import \root.Family[I := J, types := family] \as F;
        \definition identity(j: J)(x: family j): (F.bundle j).Carrier := x;
    }",
    )
    .unwrap();
}

#[test]
fn degree_indexed_structure_results_preserve_declaration_arguments() {
    check(
        r"\module Repro(A: \Set) {
        \inductive Nat: \Set := | zero: Nat | succ: Nat -> Nat;
        \structure Operator[k: Nat] { apply: A -> A, }
        \module At(k: Nat) {
            \definition step(previous: Operator[k]): Operator[Nat::succ k] :=
                Operator[Nat::succ k] { apply := previous.apply };
        }
        \definition step(k: Nat)(previous: Operator[k]): Operator[Nat::succ k] :=
            At[k := k].step previous;
        \definition identity(k: Nat)(x: A): (step k (Operator[k] {
            apply := \fun (y: A) => y,
        })).apply x = x := \refl(x);
    }",
    )
    .unwrap();
}
