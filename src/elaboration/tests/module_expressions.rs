use elaboration::Checker;

fn check(source: &str) -> Result<(), String> {
    let modules = syntax::parse::str_parse_modules(source).map_err(|error| format!("{error:?}"))?;
    let project = resolve::resolve(&modules).map_err(|errors| format!("{errors:?}"))?;
    Checker::default().check(&project).map(|_| ()).map_err(|errors| format!("{errors:?}"))
}

#[test]
fn g05_module_expression() {
    check(include_str!("../../../_plans/fix-md/cases/05-01-module-expression.ref")).unwrap();
}

#[test]
fn temporary_modules_follow_local_binders_and_nested_routes() {
    check(r"\module Family {
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
    }").unwrap();
}

#[test]
fn temporary_module_arguments_can_use_record_fields() {
    check(r"\module M {
        \inductive Nat: \Set := | zero: Nat | succ: Nat -> Nat;
        \structure Cell: \Set { dimension: Nat, }
        \module Dimension(n: Nat) { \definition dimension: Nat := n; }
        \definition dimension(c: Cell): Nat := Dimension[n := c.dimension].dimension;
        \definition beta(c: Cell): dimension c = c.dimension := \refl(c.dimension);
    }").unwrap();
}

#[test]
fn temporary_nominal_types_match_repeated_instances() {
    check(r"\module M {
        \module Family(A: \Set) {
            \inductive Box: \Set := | box: A -> Box;
        }
        \inductive Unit: \Set := | unit: Unit;
        \definition box(x: Unit): Family[A := Unit].Box := Family[A := Unit].Box::box x;
        \definition id(x: Family[A := Unit].Box): Family[A := Unit].Box := x;
    }").unwrap();
}

#[test]
fn temporary_program_modules_support_type_and_value_arguments() {
    check(r"\module M {
        \inductive Unit: \VType := | unit: Unit;
        \module Family(A: \VType) {
            \definition Type: \VType := A;
            \definition id(x: A): \F(A) := \return x;
        }
        \module Value(A: \VType, x: A) { \definition value: A := x; }
        \definition Type: \VType := \root.M[].Family[A := Unit].Type;
        \definition value: Unit := \root.M[].Value[A := Unit, x := Unit::unit].value;
        \definition run: \F(Unit) := \root.M[].Family[A := Unit].id Unit::unit;
    }").unwrap();
}

#[test]
fn module_expressions_preserve_macro_hygiene_and_argument_checks() {
    check(r"\module M {
        \module Family(A: \Set) { \definition identity(x: A): A := x; }
        \macro identity($A, $x) := Family[A := $A].identity $x;
        \definition use(A: \Set)(x: A): A := identity!{A x};
        \definition beta(A: \Set)(x: A): use A x = x := \refl(x);
    }").unwrap();
    for arguments in ["A := _", "B := Unit", "A := Unit::unit", ""] {
        let source = format!(r"\module M {{
            \inductive Unit: \Set := | unit: Unit;
            \module Family(A: \Set) {{ \definition Carrier: \Set := A; }}
            \definition bad: \Set := Family[{arguments}].Carrier;
        }}");
        assert!(check(&source).is_err(), "accepted {arguments}");
    }
}

#[test]
fn temporary_module_types_can_depend_on_earlier_record_fields() {
    check(r"\module M {
        \inductive Nat: \Set := | zero: Nat | succ: Nat -> Nat;
        \module Dimension(n: Nat) {
            \definition Carrier: \Set := \Cast[Nat] ({ m: Nat \where m = n });
        }
        \structure Cell: \Set { dimension: Nat, point: Dimension[n := dimension].Carrier, }
        \definition point(c: Cell): Dimension[n := c.dimension].Carrier := c.point;
    }").unwrap();
}
