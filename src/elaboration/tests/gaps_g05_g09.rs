use elaboration::Checker;

fn check(source: &str) -> Result<(), String> {
    let modules = syntax::parse::str_parse_modules(source).expect("valid syntax");
    let project = resolve::resolve(&modules).map_err(|errors| format!("{errors:?}"))?;
    Checker::default()
        .check(&project)
        .map(|_| ())
        .map_err(|errors| format!("{errors:?}"))
}

macro_rules! case {
    ($name:ident, $file:literal) => {
        #[test]
        fn $name() {
            check(include_str!(concat!("fixtures/gaps_g05_g09/", $file))).unwrap();
        }
    };
}

case!(dependent_type, "05-01-dependent-type-minimal.ref");
case!(independent_type, "05-02-independent-type.ref");
case!(dependent_quotient, "05-03-dependent-quotient.ref");
case!(independent_quotient, "05-04-independent-quotient.ref");
case!(forward_value_context, "05-05-forward-context.ref");
case!(inner_inductive, "06-01-inner-inductive-minimal.ref");
case!(outer_inductive, "06-02-outer-inductive.ref");
case!(direct_identity, "06-03-direct-identity.ref");
case!(forward_type_context, "06-04-forward-context.ref");
case!(signature_index, "07-01-signature-index-minimal.ref");
case!(flattened_index, "07-02-flattened-argument.ref");
case!(block_lambda_projection, "09-01-block-minimal.ref");
case!(block_hash_projection, "09-02-block-hash-projection.ref");
case!(lambda_outside_block, "09-03-lambda-outside.ref");
case!(block_let_projection, "09-04-block-let.ref");
case!(block_let_hash_projection, "09-05-block-let-hash.ref");

#[test]
fn dependent_structure_indices_expand_whole_arguments() {
    check(
        r"\module Algebra {
        \structure A[Carrier: \Set] {
            unit: Carrier, op: Carrier -> Carrier -> Carrier, inv: Carrier -> Carrier,
        }
        \structure ALaw[Carrier: \Set, data: A[Carrier]] {
            unitLaw: data.op data.unit data.unit = data.unit,
        }
        \structure Algebra[Carrier: \Set] { data: A[Carrier], law: ALaw[Carrier, data], }
        \structure Holder[Carrier: \Set, data: A[Carrier]]: \Set { value: Carrier, }
        \definition Type(Carrier: \Set, data: A[Carrier]): \Set := Holder[Carrier, data];
        \inductive Unit: \Set := | unit: Unit;
        \definition data: A[Unit] := A[Unit]{
            unit := Unit::unit, op := \fun (x, y: Unit) => x, inv := \fun (x: Unit) => x,
        };
        \definition law: ALaw[Unit, data] := ALaw[Unit, data]{ unitLaw := \refl(Unit::unit), };
        \definition algebra: Algebra[Unit] := Algebra[Unit]{ data := data, law := law, };
        \definition holder: Holder[Unit, data] := Holder[Unit, data] { value := Unit::unit };
        \definition inline: \Set := Holder[Unit, A[Unit] {
            unit := Unit::unit, op := \fun (x, y: Unit) => x, inv := \fun (x: Unit) => x,
        }];
    }",
    )
    .unwrap();
}

#[test]
fn structure_arity_errors_are_reported_before_program_type_elaboration() {
    for arguments in ["Carrier", "Carrier, data, data, data"] {
        let source = format!(
            r"\module Algebra {{
            \structure A[Carrier: \Set] {{ unit: Carrier, op: Carrier -> Carrier, }}
            \structure ALaw[Carrier: \Set, data: A[Carrier]] {{}}
            \structure Bad[Carrier: \Set] {{ data: A[Carrier], law: ALaw[{arguments}], }}
        }}"
        );
        let error = check(&source).unwrap_err();
        assert!(error.contains("argument count mismatch"), "{error}");
        assert!(!error.contains("Program value type"), "{error}");
    }
}

#[test]
fn imported_definitions_use_remapped_types_through_aliases_and_import_chains() {
    check(
        r"\module Repro {
        \module Pass(A: \Set) {
            \definition Type: \Set := A;
            \definition identity(x: A): A := x;
        }
        \module Outer(K: \Set) {
            \inductive Unit: \Set := | unit: Unit;
            \definition Alias: \Set := Unit;
            \import \root.Repro[].Pass[A := Alias] \as P;
            \import \root.Repro[].Pass[A := P.Type] \as Q;
            \definition identity(x: Unit): Unit := Q.identity (P.identity x);
        }
        \inductive Scalar: \Set := | zero: Scalar;
        \import \root.Repro[].Outer[K := Scalar] \as O;
        \import \root.Repro[].Outer[K := Scalar] \as O2;
        \definition identity(x: O.Unit): O2.Unit := O2.identity (O.identity x);
    }",
    )
    .unwrap();
}

#[test]
fn different_outer_arguments_keep_distinct_nominal_types() {
    let error = check(
        r"\module Repro {
        \module Pass(A: \Set) { \definition identity(x: A): A := x; }
        \module Outer(K: \Set) {
            \inductive Unit: \Set := | unit: Unit;
            \import \root.Repro[].Pass[A := Unit] \as P;
            \definition identity(x: Unit): Unit := P.identity x;
        }
        \inductive Scalar: \Set := | zero: Scalar;
        \import \root.Repro[].Outer[K := Scalar] \as O;
        \import \root.Repro[].Outer[K := Scalar -> Scalar] \as Other;
        \definition bad(x: O.Unit): Other.Unit := O.identity x;
    }",
    )
    .unwrap_err();
    assert!(error.contains("convertible"), "{error}");
}

#[test]
fn block_projection_obeys_shadowing_and_sequential_let_bindings() {
    check(
        r"\module Repro {
        \inductive Unit: \Set := | unit: Unit;
        \module x { \definition field: \Set := Unit; }
        \structure Box: \Set { field: Unit, }
        \definition get: Box -> Unit := \block {
            \fun (x: Box) \then
            \let y: Box := x \then
            \let x: Box := y \then
            \return x.field
        };
        \import \root.Repro[].x[] \as X;
        \definition Type: \Set := X.field;
    }",
    )
    .unwrap();
}

#[test]
fn signature_indices_apply_to_records_inductives_and_nested_structures() {
    check(
        r"\module Repro {
        \structure Carrier { A: \Set, }
        \structure Nested { carrier: Carrier, unit: carrier.A, }
        \structure Witness[C: Carrier]: \Prop { witness: \forall (x: C.A) -> x = x, }
        \inductive Family[C: Carrier]: \Set := | intro: C.A -> Family;
        \structure Holder[N: Nested]: \Set { value: N.carrier.A, }
        \definition Type(N: Nested): \Set := Holder[N];
        \definition proof(C: Carrier)(x: C.A): Witness[C] :=
            Witness[C] { witness := \fun (x: C.A) => \refl(x) };
        \definition element(C: Carrier)(x: C.A): Family[C] := Family[C]::intro x;
    }",
    )
    .unwrap();
}

#[test]
fn expanded_structure_arguments_preserve_index_type_checks() {
    let error = check(
        r"\module Repro {
        \inductive Unit: \Set := | unit: Unit;
        \inductive Bit: \Set := | zero: Bit | one: Bit;
        \structure A[Carrier: \Set] { unit: Carrier, }
        \structure ALaw[Carrier: \Set, data: A[Carrier]] {}
        \definition data: A[Bit] := A[Bit] { unit := Bit::zero };
        \definition bad: ALaw[Unit, data] := ALaw[Unit, data] {};
    }",
    )
    .unwrap_err();
    assert!(error.contains("convertible"), "{error}");
}

#[test]
fn imported_nominal_types_share_convertible_arguments_after_remapping() {
    check(
        r"\module Repro {
        \module Pass(A: \Set) { \inductive Token: \Set := | token: Token; }
        \module Outer(K: \Set) {
            \inductive Unit: \Set := | unit: Unit;
            \definition Alias: \Set := Unit;
            \import \root.Repro[].Pass[A := Alias] \as P;
            \import \root.Repro[].Pass[A := Unit] \as Q;
            \definition Token: \Set := P.Token;
            \definition convert(x: P.Token): Q.Token := x;
        }
        \inductive Scalar: \Set := | zero: Scalar;
        \import \root.Repro[].Outer[K := Scalar] \as O;
        \definition identity(x: O.Token): O.Token := O.convert x;
    }",
    )
    .unwrap();
}
