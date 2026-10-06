use elaboration::Checker;

fn check(source: &str) -> Result<(), String> {
    let modules = syntax::parse::str_parse_modules(source).expect("valid syntax");
    let project = resolve::resolve(&modules).expect("resolved names");
    Checker::default()
        .check(&project)
        .map(|_| ())
        .map_err(|errors| format!("{errors:?}"))
}

#[test]
fn constant_motives_keep_parameters_indices_and_outer_variables_scoped() {
    check(
        r"\module Scoped(A: \Set, a: A) {
        \inductive Family[B: \Set]: \forall (x: B) -> \Set :=
            | member: \forall (x: B) -> Family x;
        \definition value(x: A) (h: Family[A] x): A :=
            \match h \in Family \return A \with { | member y: y };
        \definition same(x: A) (h: Family[A] x): x = x :=
            \match h \in Family \return x = x \with { | member y: \refl(x) };
        \definition dependent(x: A) (h: Family[A] x): Family[A] x :=
            \match h \in Family
                \return (\fun (y: A) (_: Family[A] y) => Family[A] y)
                \with { | member y: Family[A]::member y };
        \definition computes: value a (Family[A]::member a) = a := \refl(a);
        \definition function(x: A) (h: Family[A] x): A -> A :=
            \match h \in Family \return A -> A \with {
            | member y: \fun (z: A) => z
            };
        \definition functionComputes:
            function a (Family[A]::member a) a = a := \refl(a);
        \inductive Witness[B: \Set]: \forall (x, y: B) -> \Set :=
            | witness: \forall (x, y: B) -> Witness x y;
        \definition witnessValue(x, y: A) (h: Witness[A] x y): A :=
            \match h \in Witness \return A \with { | witness y q: y };
        \definition witnessComputes:
            witnessValue a a (Witness[A]::witness a a) = a :=
            \refl(a);
        \inductive Pair[B, C: \Set]: \Set := | pair: B -> C -> Pair;
        \definition first (p: Pair[A, A]): A :=
            \match p \in Pair \return A \with { | pair x y: x };
        \definition firstComputes: first (Pair[A, A]::pair a a) = a := \refl(a);
    }",
    )
    .unwrap();
}

#[test]
fn constant_return_types_check_every_branch() {
    let error = check(
        r"\module Wrong(A, B: \Set, a: A, b: B) {
        \inductive Choice: \Set := | left: Choice | right: Choice;
        \definition choose(c: Choice): A :=
            \match c \in Choice \return A \with { | left: a | right: b };
    }",
    )
    .unwrap_err();
    assert!(error.contains("types are not convertible"), "{error}");
}

#[test]
fn parameterized_list_matches_with_a_constant_return_type() {
    check(
        r"\module Example {
        \inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List;
        \inductive Bool: \Set := | false: Bool | true: Bool;
        \definition List(A: \Set)::isEmpty(xs: List[A]): Bool :=
            \match xs \in List \return Bool \with {
            | nil: Bool::true
            | cons x rest: Bool::false
            };
        \definition empty: List[Bool]::isEmpty (List[Bool]::nil) = Bool::true :=
            \refl(Bool::true);
        \definition nonempty: List[Bool]::isEmpty
            (List[Bool]::cons Bool::true List[Bool]::nil) = Bool::false :=
            \refl(Bool::false);
    }",
    )
    .unwrap();
}
