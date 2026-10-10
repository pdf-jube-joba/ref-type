use elaboration::Checker;

fn check(source: &str) -> Result<(), String> {
    let modules = syntax::parse::str_parse_modules(source).map_err(|e| e.to_string())?;
    let project = resolve::resolve(&modules).map_err(|e| e.to_string())?;
    Checker::default()
        .check(&project)
        .map(|_| ())
        .map_err(|e| e.to_string())
}

#[test]
fn set_transport_and_identity_infer_binder_types() {
    check(
        r"\module Transport(A: \Set, F: A -> \Set, a, b: A) {
      \definition cast(value: F a)(same: a = b): F b :=
        \idelim a = b \with x: _ => F x \by { base: value, equality: same };
      \definition identity: \forall (value: F a)(same: a = a) ->
        (\idelim a = a \with x: _ => F x \by { base: value, equality: same }) = value :=
        \fun (value: F a)(same: a = a) =>
          \transporteq a \with x: _ => F x \by { base: value };
      \definition certificate: \forall (value: F a)(p, q: a = b) ->
        cast value p = cast value q := \fun (value: F a)(p, q: a = b) => \refl(cast value p);
    }",
    )
    .unwrap();
}

#[test]
fn transport_specialization_and_macro_binders() {
    check(
        r"\module T(A: \Set, a: A, F: A -> \Set(1)) {
      \macro move($v) := \idelim a = a \with x: _ => F x \by { base: $v, equality: \refl a };
      \definition law: \forall (value: F a) -> move!{value} = value :=
        \fun (value: _) => \transporteq a \with x: _ => F x \by { base: value };
    }
    \module U(A: \Set, a: A, F: A -> \Set(1)) {
      \import \root.T[A := A, a := a, F := F] \as T;
      \definition law: \forall (value: F a) ->
        (\idelim a = a \with x: _ => F x \by { base: value, equality: \refl a }) = value := T.law;
    }",
    )
    .unwrap();
}

#[test]
fn transport_checks_base_and_equality_certificates() {
    for source in [
        r"\module T(A: \Set, F: A -> \Set, a, b: A, v: F b, e: a = b) {
          \definition bad: F b := \idelim a = b \with x: _ => F x \by { base: v, equality: e }; }",
        r"\module T(A: \Set, F: A -> \Set, a, b: A, v: F a, e: b = a) {
          \definition bad: F b := \idelim a = b \with x: _ => F x \by { base: v, equality: e }; }",
        r"\module T(A: \Set, F: A -> \Set, a, b: A, v: F a) {
          \definition bad: F b := \idelim a = b \with x: _ => F x \by { base: v, equality: _ }; }",
    ] {
        assert!(check(source).is_err(), "{source}");
    }
}

#[test]
fn neutral_transport_supports_subsets_functions_projections_and_induction() {
    check(
        r"\module T(A: \Set, a, b: A) {
      \inductive Nat: \Set := | zero: Nat | succ: Nat -> Nat;
      \structure Pair: \Set { first: Nat, second: Nat }
      \definition moveNat(value: Nat)(same: a = b): Nat :=
        \idelim a = b \with x: _ => Nat \by { base: value, equality: same };
      \definition count: Nat -> Nat := \induction (n: Nat) \return Nat \with {
        | zero: Nat::zero | succ: \fun (n, previous: Nat) => Nat::succ previous
      };
      \definition countMoved(value: Nat)(same: a = b): Nat := count (moveNat value same);
      \definition apply(f: Nat -> Nat)(same: a = b): Nat :=
        (\idelim a = b \with x: _ => Nat -> Nat \by { base: f, equality: same }) Nat::zero;
      \definition project(p: Pair)(same: a = b): Nat :=
        (\idelim a = b \with x: _ => Pair \by { base: p, equality: same }) #first;
      \definition Sub: \Set := \Cast[Nat] ({ n: Nat \where n = n });
      \definition subset(value: Sub)(same: a = b): Sub :=
        \idelim a = b \with x: _ => Sub \by { base: value, equality: same };
      \definition law: \forall (value: Sub) ->
        (\idelim a = a \with x: _ => Sub \by { base: value, equality: \refl a }) = value :=
        \fun (value: _) => \transporteq a \with x: _ => Sub \by { base: value };
    }",
    )
    .unwrap();
}

#[test]
fn transport_substitutes_through_nested_family_binders() {
    check(r"\module T(A: \Set(1), F: A -> A -> \Set, a, b: A) {
      \definition cast(value: \forall (y: A) -> F a y)(same: a = b): \forall (y: A) -> F b y :=
        \idelim a = b \with x: _ => \forall (y: A) -> F x y \by { base: value, equality: same };
      \definition identity: \forall (value: \forall (y: A) -> F a y) ->
        (\idelim a = a \with x: _ => \forall (y: A) -> F x y \by { base: value, equality: \refl a }) = value :=
        \fun (value: _) => \transporteq a \with x: _ => \forall (y: A) -> F x y \by { base: value };
    }").unwrap();
    let error = check(
        r"\module T(A: \Set, a: A, P: A -> \Prop, p: P a) {
      \infer \transporteq a \with x: _ => P x \by { base: p };
    }",
    )
    .unwrap_err();
    assert!(error.contains("expected Set"), "{error}");
}
