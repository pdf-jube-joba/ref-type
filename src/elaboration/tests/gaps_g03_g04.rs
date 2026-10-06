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
fn current_g03_and_g04_minimal_examples() {
    for source in [
        include_str!("../../../_plans/fix-md/cases/03-01-infer-projection.ref"),
        include_str!("../../../_plans/fix-md/cases/03-02-explicit-projection.ref"),
        include_str!("../../../_plans/fix-md/cases/03-03-infer-take-continuation.ref"),
        include_str!("../../../_plans/fix-md/cases/03-04-explicit-take-continuation.ref"),
        include_str!("../../../_plans/fix-md/cases/03-05-infer-take.ref"),
        include_str!("../../../_plans/fix-md/cases/03-06-infer-subset.ref"),
        include_str!("../../../_plans/fix-md/cases/04-01-alias-constructor.ref"),
        include_str!("../../../_plans/fix-md/cases/04-02-direct-constructor.ref"),
        include_str!("../../../_plans/fix-md/cases/04-03-alias-induction.ref"),
        include_str!("../../../_plans/fix-md/cases/04-04-direct-induction.ref"),
    ] {
        check(source).unwrap();
    }
}

#[test]
fn expected_types_reach_grouped_dependent_local_and_record_bodies() {
    check(
        r"\module Expected(A: \Set, P: A -> \Prop) {
        \structure Pair: \Set { first: A, second: A }
        \definition first: Pair -> A := \block {
            \fun (pair: _) \then
            \let project: Pair -> A := \fun (p: _) => p #first \then
            \return project pair
        };
        \definition grouped: Pair -> Pair -> A :=
            \fun (left, right: _) => left #first;
        \definition dependent: \forall (p: Pair) -> p #first = p #first :=
            \fun (p: _) => \refl(p #first);
        \definition nested: \forall (X: \Set) -> X -> X -> X :=
            \fun (X: _) (x, y: _) => x;
        \definition ascribed: Pair -> A :=
            (\fun (p: _) => p #first) \of Pair -> A;
        \structure Maps: \Set { get: Pair -> A }
        \definition maps: Maps := Maps { get := \block {
            \fun (p: _) \then \return p #second
        } };
        \definition Sub: \Set := \Cast[A] ({ x: A \where P x });
        \definition property: \forall (x: Sub) -> P x :=
            \fun (x: _) => \bysub(A, Sub, x);
    }",
    )
    .unwrap();
}

#[test]
fn inferred_annotations_do_not_accept_wrong_proofs_or_escaping_witnesses() {
    for source in [
        r"\module Wrong(P, Q: \Prop) {
            \definition bad: P -> Q := \fun (p: _) => p;
        }",
        r"\module Wrong(P, Q: \Prop) {
            \definition bad: P -> P := \fun (p: Q) => p;
        }",
        r"\module Escape(A: \Set) {
            \definition bad: (\exists A) -> A := \fun (e: _) => \block {
                \takefrom x: A \by e \then \return x
            };
        }",
        r"\module Wrong(A: \Set, P: A -> \Prop) {
            \definition Sub: \Set := \Cast[A] ({ x: A \where P x });
            \definition bad: A -> Sub := \fun (x: _) => x;
        }",
    ] {
        assert!(check(source).is_err(), "unexpected acceptance: {source}");
    }
}

#[test]
fn chained_and_instantiated_aliases_keep_parameters_and_reduce() {
    check(
        r"\module Lists(A: \Set) {
        \inductive List[B: \Set]: \Set := | nil: List | cons: B -> List -> List;
        \definition Values: \Set := List[A];
        \definition Alias: \Set := Values;
        \definition Generic(B: \Set): \Set := List[B];
        \definition empty: Values := Alias::nil;
        \definition generic: Values := Generic[A]::nil;
        \definition copy: Alias -> Alias :=
            \induction (xs: Alias) \return Alias \with {
                | cons: \fun (x: A) (xs, previous: Alias) => Alias::cons x previous
                | nil: Alias::nil
            };
        \definition onNil: copy empty = empty := \refl(empty);
    }
    \module Use {
        \inductive Unit: \Set := | unit: Unit;
        \import \root.Lists[A := Unit] \as L;
        \definition Values: \Set := L.Alias;
        \definition singleton: Values := Values::cons Unit::unit Values::nil;
        \definition onCons: L.copy singleton = singleton := \refl(singleton);
    }",
    )
    .unwrap();
}

#[test]
fn indexed_alias_induction_preserves_its_motive_telescope() {
    check(
        r"\module Indexed(A: \Set) {
        \inductive Family[B: \Set]: \forall (x: B) -> \Set := | intro: \forall (x: B) -> Family x;
        \definition Alias(x: A): \Set := Family[A] x;
        \definition copy: \forall (x: A) -> Alias x -> Alias x :=
            \induction (x: A) (value: Alias x) \return Alias x \with {
                | intro: \fun (x: A) => Family[A]::intro x
            };
        \definition law(x: A): copy x (Family[A]::intro x) = Family[A]::intro x :=
            \refl(Family[A]::intro x);
    }",
    )
    .unwrap();
}

#[test]
fn aliases_do_not_bypass_constructor_or_eliminator_checks() {
    for (body, diagnostic) in [
        (
            r"\definition bad: Alias := Alias::cons Unit::unit Alias::nil;",
            "convertible",
        ),
        (
            r"\definition bad: Alias := Alias::missing;",
            "Associated item missing",
        ),
        (
            r"\definition bad: Alias -> Alias :=
            \induction (xs: Alias) \return Alias \with { | nil: Alias::nil };",
            "branches",
        ),
        (
            r"\definition bad: Alias -> Alias :=
            \induction (xs: Alias) \return Alias \with {
                | nil: Alias::nil | nil: Alias::nil
            };",
            "Duplicate inductive branch",
        ),
        (
            r"\definition bad: Alias -> Unit :=
            \induction (xs: Alias) \return Unit \with {
                | nil: Alias::nil
                | cons: \fun (x: Bit) (xs: Alias) (ih: Unit) => ih
            };",
            "convertible",
        ),
        (
            r"\definition Refined: \Set := \Cast[Alias] ({ xs: Alias \where xs = xs });
            \definition bad: Refined := Refined::nil;",
            "Expected inductive type",
        ),
        (
            r"\definition Function: \Set := Unit -> Unit;
            \definition bad: Function := Function::unit;",
            "Expected inductive type",
        ),
        (
            r"\definition Discard(x: Unit): \Set := List[Bit];
            \definition bad: Alias := Discard[Bit::zero]::nil;",
            "convertible",
        ),
    ] {
        let source = format!(
            r"\module Negative {{
            \inductive Unit: \Set := | unit: Unit;
            \inductive Bit: \Set := | zero: Bit | one: Bit;
            \inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List;
            \definition Alias: \Set := List[Bit];
            {body}
        }}"
        );
        let error = check(&source).expect_err(&source);
        assert!(error.contains(diagnostic), "{error}");
    }
    let error = check(
        r"\module LargeElimination {
        \inductive Either: \Prop := | left: Either | right: Either;
        \definition Alias: \Prop := Either;
        \definition bad: Alias -> \Prop :=
            \induction (p: Alias) \return \Prop \with { | left: Either | right: Either };
    }",
    )
    .unwrap_err();
    assert!(error.contains("forbidden large elimination"), "{error}");
}
