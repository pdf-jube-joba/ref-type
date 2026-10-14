# module の引数と record の射影

## forward value context

親の値引数で定まる subset を import 先へ渡し、再び外側から利用できる。

```toml case
id = "module_arguments_and_projections.forward-value-context"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Repro {
  \inductive Unit: \Set := | unit: Unit;
  \module Pass(u: Unit, A: \Set) { \definition identity(x: A): A := x; }
  \module Outer(u: Unit) {
    \definition Representation: \Set := \Cast[Unit] ({ x: Unit \where x = u });
    \import \root.Repro[].Pass[u := u, A := Representation] \as P;
    \definition identity(x: Representation): Representation := P.identity x;
  }
  \import \root.Repro[].Outer[u := Unit::unit] \as O;
  \definition identity(x: O.Representation): O.Representation := O.identity x;
}
```

## forward type context

親の型引数と子の帰納型を import 先へ渡し、外側の特殊化に対応する型を返せる。

```toml case
id = "module_arguments_and_projections.forward-type-context"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Repro {
  \module Pass(K: \Set, A: \Set) { \definition identity(x: A): A := x; }
  \module Outer(K: \Set) {
    \inductive Unit: \Set := | unit: Unit;
    \import \root.Repro[].Pass[K := K, A := Unit] \as P;
    \definition identity(x: Unit): Unit := P.identity x;
  }
  \inductive Scalar: \Set := | zero: Scalar;
  \import \root.Repro[].Outer[K := Scalar] \as O;
  \definition identity(x: O.Unit): O.Unit := O.identity x;
}
```

## dependent quotient

親の値引数に依存する subset から quotient の要素を作り、外側から同じ型として利用できる。

```toml case
id = "module_arguments_and_projections.dependent-quotient"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Repro {
  \inductive Unit: \Set := | unit: Unit;
  \module Quotient(A: \Set, Equivalent: A -> A -> \Prop) {
    \definition ClassOf(x: A): \Pow A := { y: A \where Equivalent x y };
    \definition Representative(C: \Pow A): \Set := \Cast[A] ({ x: A \where C = ClassOf x });
    \definition IsClass(C: \Pow A): \Prop := \exists Representative C;
    \definition Carrier: \Set := \Cast[\Pow A] ({ C: \Pow A \where IsClass C });
    \definition class(x: A): Carrier :=
      \into[\Pow A](ClassOf x, Carrier) \by {
      \exact(\into[A](x, Representative (ClassOf x)) \by { \refl(ClassOf x) }, Representative (ClassOf x))
    };
  }
  \module Lebesgue(interval: Unit) {
    \definition Representation: \Set := \Cast[Unit] ({ x: Unit \where x = interval });
    \definition Equivalent(x, y: Representation): \Prop := x = y;
    \import \root.Repro[].Quotient[A := Representation, Equivalent := Equivalent] \as Q;
    \definition Function: \Set := Q.Carrier;
    \definition class(x: Representation): Function := Q.class x;
  }
  \import \root.Repro[].Lebesgue[interval := Unit::unit] \as L;
  \definition point: L.Representation := \into[Unit](Unit::unit, L.Representation) \by { \refl(Unit::unit) };
  \definition value: L.Function := L.class point;
}
```

## flattened argument

structure 引数を構成する Carrier を直接渡しても、型の展開後に同じ field 型を持つ。

```toml case
id = "module_arguments_and_projections.flattened-argument"
scope = "module"
expect = "accept"
name = "Repro"
```

```ref
\structure Carrier { A: \Set, }
\structure Holder[C: Carrier]: \Set { value: C.A, }
\definition Type(C: Carrier): \Set := Holder[C.A];
```

## block hash projection

block 内の関数引数から field を型に従って射影できる。

```toml case
id = "module_arguments_and_projections.block-hash-projection"
scope = "module"
expect = "accept"
name = "Repro"
parameters = '''A: \Set'''
```

```ref
\structure Box: \Set { field: A, }
\definition get: Box -> A := \block {
  \fun (x: Box) \then
  \return x #field
};
```

## block let

block 内の let で保存した record から field を射影できる。

```toml case
id = "module_arguments_and_projections.block-let"
scope = "module"
expect = "accept"
name = "Repro"
parameters = '''A: \Set'''
```

```ref
\structure Box: \Set { field: A, }
\definition get(x: Box): A := \block {
  \let y: Box := x \then
  \return y.field
};
```

## dependent structure indices expand whole arguments

前の structure 引数の field に依存する index を、構成した値から展開できる。

```toml case
id = "dependent_structure_indices_expand_whole_arguments"
scope = "module"
expect = "accept"
name = "Algebra"
```

```ref
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
```

## imported definitions use remapped types through aliases and import chains

同じ引数の import を重ねても、帰納型と関数の型は一致する。

```toml case
id = "imported_definitions_use_remapped_types_through_aliases_and_import_chains"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Repro {
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
}
```

## different outer arguments keep distinct nominal types

親 module の引数が異なる特殊化の帰納型を混用するため拒否される。

```toml case
id = "different_outer_arguments_keep_distinct_nominal_types"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Repro {
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
}
```

## block projection obeys shadowing and sequential let bindings

module と同名の局所変数でも、let の順序に従って record の field を射影できる。

```toml case
id = "block_projection_obeys_shadowing_and_sequential_let_bindings"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Repro {
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
}
```

## signature indices apply to records inductives and nested structures

signature の field を、record、帰納型と入れ子の structure の index から利用できる。

```toml case
id = "signature_indices_apply_to_records_inductives_and_nested_structures"
scope = "module"
expect = "accept"
name = "Repro"
```

```ref
\structure Carrier { A: \Set, }
\structure Nested { carrier: Carrier, unit: carrier.A, }
\structure Witness[C: Carrier]: \Prop { witness: \forall (x: C.A) -> x = x, }
\inductive Family[C: Carrier]: \Set := | intro: C.A -> Family;
\structure Holder[N: Nested]: \Set { value: N.carrier.A, }
\definition Type(N: Nested): \Set := Holder[N];
\definition proof(C: Carrier)(x: C.A): Witness[C] :=
  Witness[C] { witness := \fun (x: C.A) => \refl(x) };
\definition element(C: Carrier)(x: C.A): Family[C] := Family[C]::intro x;
```

## expanded structure arguments preserve index type checks

Unit を要求する index に Bit の structure を渡すため拒否される。

```toml case
id = "expanded_structure_arguments_preserve_index_type_checks"
scope = "module"
expect = "reject"
name = "Repro"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\inductive Bit: \Set := | zero: Bit | one: Bit;
\structure A[Carrier: \Set] { unit: Carrier, }
\structure ALaw[Carrier: \Set, data: A[Carrier]] {}
\definition data: A[Bit] := A[Bit] { unit := Bit::zero };
\definition bad: ALaw[Unit, data] := ALaw[Unit, data] {};
```

## imported nominal types share convertible arguments after remapping

型 alias とその元の型を引数にした import は、同じ nominal type として利用できる。

```toml case
id = "imported_nominal_types_share_convertible_arguments_after_remapping"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Repro {
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
}
```

## structure 引数の個数 / few

structure の宣言と渡した引数の個数が違うため拒否される。

```toml case
id = "structure-arity-few"
scope = "module"
expect = "reject"
name = "Algebra"
```

```ref
\structure A[Carrier: \Set] { unit: Carrier } \structure ALaw[Carrier: \Set, data: A[Carrier]] {} \structure Bad[Carrier: \Set] { data: A[Carrier], law: ALaw[Carrier] }
```

## structure 引数の個数 / many

structure の宣言と渡した引数の個数が違うため拒否される。

```toml case
id = "structure-arity-many"
scope = "module"
expect = "reject"
name = "Algebra"
```

```ref
\structure A[Carrier: \Set] { unit: Carrier } \structure ALaw[Carrier: \Set, data: A[Carrier]] {} \structure Bad[Carrier: \Set] { data: A[Carrier], law: ALaw[Carrier, data, data, data] }
```
