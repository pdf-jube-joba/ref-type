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
fn module_expression_returns_carrier() {
    check(
        r"\module Family { \module Dimension(A: \Set) { \definition Carrier: \Set := A; } }
        \module Consumer {
            \import \root.Family[] \as F;
            \definition Carrier(A: \Set): \Set := F.Dimension[A := A].Carrier;
        }",
    )
    .unwrap();
}

#[test]
fn temporary_modules_follow_local_binders_and_nested_routes() {
    check(
        r"\module Family {
        \module Dimension(A: \Set) {
            \definition Carrier: \Set := A;
            \definition identity(x: A): A := x;
            \module Inner(B: \Set) { \definition second(x: B): B := x; }
        }
        \module Consumer {
            \import \root.Family[] \as F;
            \definition local(A: \Set)(x: A): A := F.Dimension[A := A].identity x;
            \definition nested(A: \Set)(x: A): A := F.Dimension[A := A].Inner[B := A].second x;
            \definition rooted(A: \Set)(x: A): A := \root.Family[].Dimension[A := A].identity x;
            \definition parent(A: \Set)(x: A): A := \parent.Dimension[A := A].identity x;
            \definition beta(A: \Set)(x: A): local A x = x := \refl(x);
            \definition underLambda: \forall (A: \Set) -> A -> A :=
                \fun (A: \Set) (x: A) => F.Dimension[A := A].identity x;
            \definition shadow(A: \Set): \forall (A: \Set) -> A -> A :=
                \fun (A: \Set) (x: A) => F.Dimension[A := A].identity x;
        }
        \definition direct(A: \Set)(x: A): A := Dimension[A := A].identity x;
    }",
    )
    .unwrap();
}

#[test]
fn temporary_module_arguments_can_use_record_fields() {
    check(
        r"\module M {
        \inductive Nat: \Set := | zero: Nat | succ: Nat -> Nat;
        \structure Cell: \Set { dimension: Nat, }
        \module Dimension(n: Nat) { \definition dimension: Nat := n; }
        \definition dimension(c: Cell): Nat := Dimension[n := c.dimension].dimension;
        \definition beta(c: Cell): dimension c = c.dimension := \refl(c.dimension);
    }",
    )
    .unwrap();
}

#[test]
fn temporary_nominal_types_match_repeated_instances() {
    check(
        r"\module M {
        \module Family(A: \Set) {
            \inductive Box: \Set := | box: A -> Box;
        }
        \inductive Unit: \Set := | unit: Unit;
        \definition box(x: Unit): Family[A := Unit].Box := Family[A := Unit].Box::box x;
        \definition id(x: Family[A := Unit].Box): Family[A := Unit].Box := x;
    }",
    )
    .unwrap();
}

#[test]
fn temporary_program_modules_support_type_and_value_arguments() {
    check(
        r"\module M {
        \inductive Unit: \VType := | unit: Unit;
        \module Family(A: \VType) {
            \definition Type: \VType := A;
            \definition id(x: A): \F(A) := \return x;
        }
        \module Value(A: \VType, x: A) { \definition value: A := x; }
        \definition identity[A: \VType](x: A): A := Value[A := A, x := x].value;
        \definition Type: \VType := Family[A := Unit].Type;
        \definition value: Unit := Value[A := Unit, x := Unit::unit].value;
        \definition run: \F(Unit) := Family[A := Unit].id Unit::unit;
    }",
    )
    .unwrap();
}

#[test]
fn module_expressions_preserve_macro_hygiene_and_argument_checks() {
    check(
        r"\module M {
        \module Family(A: \Set) { \definition identity(x: A): A := x; }
        \macro identity($A, $x) := Family[A := $A].identity $x;
        \definition use(A: \Set)(x: A): A := identity!{A x};
        \definition beta(A: \Set)(x: A): use A x = x := \refl(x);
    }",
    )
    .unwrap();
    for arguments in ["A := _", "B := Unit", "A := Unit::unit", ""] {
        let source = format!(
            r"\module M {{
            \inductive Unit: \Set := | unit: Unit;
            \module Family(A: \Set) {{ \definition Carrier: \Set := A; }}
            \definition bad: \Set := Family[{arguments}].Carrier;
        }}"
        );
        assert!(check(&source).is_err(), "accepted {arguments}");
    }
}

#[test]
fn temporary_module_types_can_depend_on_earlier_record_fields() {
    check(
        r"\module M {
        \inductive Nat: \Set := | zero: Nat | succ: Nat -> Nat;
        \module Dimension(n: Nat) {
            \definition Carrier: \Set := \Cast[Nat] ({ m: Nat \where m = n });
        }
        \structure Cell: \Set { dimension: Nat, point: Dimension[n := dimension].Carrier, }
        \definition point(c: Cell): Dimension[n := c.dimension].Carrier := c.point;
    }",
    )
    .unwrap();
}

#[test]
fn temporary_module_macros_retain_their_definition_scope() {
    check(
        r"\module Library {
        \module Family(A: \Set) { \definition identity(x: A): A := x; }
        \macro identity($A, $x) := Family[A := $A].identity $x;
    }
    \module Consumer {
        \import \root.Library[] \as L;
        \use L.identity;
        \definition use(A: \Set)(x: A): A := identity!{A x};
        \definition beta(A: \Set)(x: A): use A x = x := \refl(x);
    }",
    )
    .unwrap();
}

#[test]
fn temporary_inductives_capture_local_arguments() {
    check(
        r"\module M {
        \module Family(A: \Set) {
            \inductive Box: \Set := | box: A -> Box;
        }
        \definition box(A: \Set)(x: A): Family[A := A].Box := Family[A := A].Box::box x;
        \definition id(A: \Set)(x: Family[A := A].Box): Family[A := A].Box := x;
        \definition underLambda: \forall (A: \Set) -> A -> Family[A := A].Box :=
            \fun (A: \Set) (x: A) => Family[A := A].Box::box x;
        \inductive Unit: \Set := | unit: Unit;
        \definition closed(x: Unit): Family[A := Unit].Box := box Unit x;
    }",
    )
    .unwrap();
}

#[test]
fn temporary_program_values_capture_local_arguments() {
    check(
        r"\module M {
        \inductive Unit: \VType := | unit: Unit;
        \module Value(A: \VType, x: A) { \definition value: A := x; }
        \definition identity(x: Unit): \F(Unit) := \return Value[A := Unit, x := x].value;
        \definition lambda: Unit ~> \F(Unit) :=
            \cfun (x: _) => \return Value[A := Unit, x := x].value;
    }",
    )
    .unwrap();
}

#[test]
fn temporary_modules_follow_inferred_lambda_binders() {
    check(
        r"\module M {
        \module Family(A: \Set) { \inductive Box: \Set := | box: A -> Box; }
        \definition make: \forall (A: \Set) -> A -> Family[A := A].Box :=
            \fun (A: _) (x: _) => Family[A := A].Box::box x;
    }",
    )
    .unwrap();
}

#[test]
fn temporary_modules_follow_program_blocks_and_reflection() {
    check(
        r"\module M {
        \inductive Unit: \VType := | unit: Unit;
        \module Value(A: \VType, x: A) { \definition value: A := x; }
        \definition identity(x: Unit): \F(Unit) := \return Value[A := Unit, x := x].value;
        \definition beta(x: Unit^): identity^ x = x := \refl(x);
        \definition nested(x: Unit): Unit ~> \F(Unit) :=
            \cfun (y: Unit) => \return Value[A := Unit, x := x].value;
        \definition nestedBeta(x, y: Unit^): nested^ x y = x := \refl(x);
        \definition sequence(x: Unit): \F(Unit) := \program {
            \bind y: _ <- \return x \then
            \return Value[A := Unit, x := y].value
        };
    }",
    )
    .unwrap();
}

#[test]
fn temporary_program_datatypes_and_reflections_agree() {
    check(r"\module M {
        \inductive Unit: \VType := | unit: Unit;
        \module Family(A: \VType) { \inductive Box: \VType := | box: A -> Box; }
        \definition make(x: Unit): \F(Family[A := Unit].Box) := \return Family[A := Unit].Box::box x;
        \definition reflected(x: Unit^): Family[A := Unit].Box^ := make^ x;
    }").unwrap();
}

#[test]
fn temporary_record_fields_retain_module_arguments() {
    check(
        r"\module M {
        \module Family(A: \Set) { \structure Box: \Set { value: A, } }
        \definition make(A: \Set)(x: A): Family[A := A].Box := Family[A := A].Box { value := x };
        \definition get(A: \Set)(x: Family[A := A].Box): A := x.value;
        \definition beta(A: \Set)(x: A): get A (make A x) = x := \refl(x);
    }",
    )
    .unwrap();
}

#[test]
fn temporary_nominal_types_preserve_unused_module_parameters() {
    let source = r"\module M {
        \module Family(A: \Set) { \inductive Ghost: \Set := | ghost: Ghost; }
        \definition mix(A, B: \Set)(x: Family[A := A].Ghost): Family[A := B].Ghost := x;
    }";
    assert!(
        check(source).is_err(),
        "different module instances lost their nominal identity"
    );
}

#[test]
fn temporary_modules_preserve_case_branch_binders() {
    check(
        r"\module M {
        \inductive Unit: \VType := | unit: Unit;
        \inductive Box: \VType := | box: Unit -> Box;
        \module Value(x: Unit) { \definition value: Unit := x; }
        \definition get(x: Box): \F(Unit) := \match x \in Box \with {
            | box y : \return Value[x := y].value
        };
    }",
    )
    .unwrap();
}

#[test]
fn temporary_modules_capture_macro_local_binders() {
    check(
        r"\module M {
        \inductive Unit: \VType := | unit: Unit;
        \module Value(x: Unit) { \definition value: Unit := x; }
        \macro identity() := \cfun (x: Unit) => \return Value[x := x].value;
        \definition identity: Unit ~> \F(Unit) := identity!{};
        \definition beta(x: Unit^): identity^ x = x := \refl(x);
    }",
    )
    .unwrap();
}

#[test]
fn specialized_records_resolve_definition_arguments() {
    check(
        r"\module M {
        \module Family(A: \Set) {
            \structure Box: \Set { value: A, }
            \definition get(x: Box): A := x.value;
            \definition beta(x: A): get (Box { value := x }) = x := \refl(x);
        }
        \inductive Unit: \Set := | unit: Unit;
        \definition Carrier: \Set := Unit;
        \definition beta(x: Carrier): Family[A := Carrier].get
            (Family[A := Carrier].Box { value := x }) = x := Family[A := Carrier].beta x;
    }",
    )
    .unwrap();
}

#[test]
fn nominal_arguments_materialize_lazy_definitions() {
    check(
        r"\module M {
        \module Family(A: \Set) { \inductive Ghost: \Set := | ghost: Ghost; }
        \module Outer(A: \Set) {
            \definition Carrier: \Set := A;
            \import \parent.Family[A := Carrier] \as F;
            \definition Ghost: \Set := F.Ghost;
            \definition value: Ghost := F.Ghost::ghost;
        }
        \inductive Unit: \Set := | unit: Unit;
        \definition value: Outer[A := Unit].Ghost := Outer[A := Unit].value;
    }",
    )
    .unwrap();
}

#[test]
fn specialized_record_elimination_captures_actual_parameters() {
    check(
        r"\module M {
        \module Family(A: \Set, a: A) {
            \structure Box: \Set { value: A, }
        }
        \module Wrapper(A: \Set, a: A) {
            \import \parent.Family[A := A, a := a] \as F;
            \structure Outer: \Set { inner: F.Box, }
            \definition get(x: Outer): A := x.inner.value;
            \definition value: Outer := Outer { inner := F.Box { value := a } };
            \definition beta: get value = a := \refl(a);
        }
        \inductive Unit: \Set := | unit: Unit;
        \definition beta: Wrapper[A := Unit, a := Unit::unit].get
            Wrapper[A := Unit, a := Unit::unit].value = Unit::unit :=
            Wrapper[A := Unit, a := Unit::unit].beta;
    }",
    )
    .unwrap();
}
