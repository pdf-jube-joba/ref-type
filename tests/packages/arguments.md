# Module arguments and record projections

## Forward value context

A subset determined by a parent's value argument can be passed to an import and used again from outside.

```toml case
id = "forward-value-context"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module ForwardValueContext {
  \inductive Unit: \Set := | unit: Unit;
  \module Pass(u: Unit, A: \Set) {
    \definition identity[x: A]: A := x;
  }
  \module Outer(u: Unit) {
    \definition Representation: \Set := \Cast[Unit] ({ x: Unit \where x = u });
    \import \root.ForwardValueContext[].Pass[u := u, A := Representation] \as P;
    \definition identity[x: Representation]: Representation := P.identity x;
  }
  \import \root.ForwardValueContext[].Outer[u := Unit::unit] \as O;
  \definition identity[x: O.Representation]: O.Representation := O.identity x;
}
```

## Forward type context

A parent's type argument and a child's inductive type can be passed to an import, returning a type matching the outer specialization.

```toml case
id = "forward-type-context"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module ForwardTypeContext {
  \module Pass(K: \Set, A: \Set) {
    \definition identity[x: A]: A := x;
  }
  \module Outer(K: \Set) {
    \inductive Unit: \Set := | unit: Unit;
    \import \root.ForwardTypeContext[].Pass[K := K, A := Unit] \as P;
    \definition identity[x: Unit]: Unit := P.identity x;
  }
  \inductive Tag: \Set := | zero: Tag;
  \import \root.ForwardTypeContext[].Outer[K := Tag] \as O;
  \definition identity[x: O.Unit]: O.Unit := O.identity x;
}
```

## Dependent quotient

A quotient element can be constructed from a subset depending on a parent's value argument and used as the same type from outside.

```toml case
id = "dependent-quotient"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module DependentClasses {
  \inductive Unit: \Set := | unit: Unit;
  \module Quotient(A: \Set, Equivalent: A -> A -> \Prop) {
    \definition ClassOf[x: A]: \Pow A := { y: A \where Equivalent x y };
    \definition Representative[C: \Pow A]: \Set := \Cast[A] ({ x: A \where C = ClassOf x });
    \definition IsClass[C: \Pow A]: \Prop := \exists Representative C;
    \definition Carrier: \Set := \Cast[\Pow A] ({ C: \Pow A \where IsClass C });
    \definition class[x: A]: Carrier :=
      \into[\Pow A](ClassOf x, Carrier) \by {
      \exact(\into[A](x, Representative (ClassOf x)) \by { \refl(ClassOf x) }, Representative (ClassOf x))
    };
  }
  \module Selected(point: Unit) {
    \definition Representation: \Set := \Cast[Unit] ({ x: Unit \where x = point });
    \definition Equivalent[x, y: Representation]: \Prop := x = y;
    \import \root.DependentClasses[].Quotient[A := Representation, Equivalent := Equivalent] \as Q;
    \definition Classes: \Set := Q.Carrier;
    \definition class[x: Representation]: Classes := Q.class x;
  }
  \import \root.DependentClasses[].Selected[point := Unit::unit] \as Selected;
  \definition point: Selected.Representation := \into[Unit](Unit::unit, Selected.Representation) \by { \refl(Unit::unit) };
  \definition value: Selected.Classes := Selected.class point;
}
```

## Flattened argument

Passing the Carrier used to construct a structure argument directly yields the same field type after type expansion.

```toml case
id = "flattened-argument"
scope = "module"
expect = "accept"
```

```ref
\structure Carrier := { A: \Set, };
\structure Holder[C: Carrier]: \Set := { value: C.A, };
\definition Type[C: Carrier]: \Set := Holder[C.A];
```

## Projecting fields from block arguments

Fields can be projected from function arguments inside a block according to their types.

```toml case
id = "block-argument-field-projection"
scope = "module"
expect = "accept"
parameters = '''A: \Set'''
```

```ref
\structure Box: \Set := { field: A, };
\definition get: Box -> A := \block {
  \fun (x: Box) \then
  \return x.field
};
```

## Block let

Fields can be projected from a record stored with let inside a block.

```toml case
id = "block-let"
scope = "module"
expect = "accept"
parameters = '''A: \Set'''
```

```ref
\structure Box: \Set := { field: A, };
\definition get[x: Box]: A := \block {
  \let y: Box := x \then
  \return y.field
};
```

## Dependent structure indices expand whole arguments

An index depending on a previous structure argument's field can be expanded from the constructed value.

```toml case
id = "dependent-structure-indices-expand-whole-arguments"
scope = "module"
expect = "accept"
```

```ref
\structure Operations[Carrier: \Set] := {
  unit: Carrier, op: Carrier -> Carrier -> Carrier, inv: Carrier -> Carrier,
};
\structure Witness[Carrier: \Set, data: Operations[Carrier]] := {
  unitLaw: data.op data.unit data.unit = data.unit,
};
\structure LawfulOperations[Carrier: \Set] := { data: Operations[Carrier], law: Witness[Carrier, data], };
\structure Holder[Carrier: \Set, data: Operations[Carrier]]: \Set := { value: Carrier, };
\definition Type[Carrier: \Set, data: Operations[Carrier]]: \Set := Holder[Carrier, data];
\inductive Unit: \Set := | unit: Unit;
\definition data: Operations[Unit] := Operations[Unit]{
  unit := Unit::unit, op := \fun (x, y: Unit) => x, inv := \fun (x: Unit) => x,
};
\definition law: Witness[Unit, data] := Witness[Unit, data]{ unitLaw := \refl(Unit::unit), };
\definition lawful: LawfulOperations[Unit] := LawfulOperations[Unit]{ data := data, law := law, };
\definition holder: Holder[Unit, data] := Holder[Unit, data] { value := Unit::unit };
\definition inline: \Set := Holder[Unit, Operations[Unit] {
  unit := Unit::unit, op := \fun (x, y: Unit) => x, inv := \fun (x: Unit) => x,
}];
```

## Imported definitions preserve types through alias chains

Repeated imports with the same arguments preserve agreement between inductive types and function types.

```toml case
id = "imported-definitions-preserve-types-through-aliases"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module ImportedDefinitionsPreserveTypesThrough {
  \module Pass(A: \Set) {
    \definition Type: \Set := A;
    \definition identity[x: A]: A := x;
  }
  \module Outer(K: \Set) {
    \inductive Unit: \Set := | unit: Unit;
    \definition Alias: \Set := Unit;
    \import \root.ImportedDefinitionsPreserveTypesThrough[].Pass[A := Alias] \as P;
    \import \root.ImportedDefinitionsPreserveTypesThrough[].Pass[A := P.Type] \as Q;
    \definition identity[x: Unit]: Unit := Q.identity (P.identity x);
  }
  \inductive Tag: \Set := | zero: Tag;
  \import \root.ImportedDefinitionsPreserveTypesThrough[].Outer[K := Tag] \as O;
  \import \root.ImportedDefinitionsPreserveTypesThrough[].Outer[K := Tag] \as O2;
  \definition identity[x: O.Unit]: O2.Unit := O2.identity (O.identity x);
}
```

## Different outer arguments keep distinct nominal types

Inductive types from specializations with different parent module arguments are mixed.

```toml case
id = "different-outer-arguments-keep-distinct-nominal-types"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module DifferentOuterArgumentsKeepDistinct {
  \module Pass(A: \Set) {
    \definition identity[x: A]: A := x;
  }
  \module Outer(K: \Set) {
    \inductive Unit: \Set := | unit: Unit;
    \import \root.DifferentOuterArgumentsKeepDistinct[].Pass[A := Unit] \as P;
    \definition identity[x: Unit]: Unit := P.identity x;
  }
  \inductive Tag: \Set := | zero: Tag;
  \import \root.DifferentOuterArgumentsKeepDistinct[].Outer[K := Tag] \as O;
  \import \root.DifferentOuterArgumentsKeepDistinct[].Outer[K := Tag -> Tag] \as Other;
  \definition bad[x: O.Unit]: Other.Unit := O.identity x;
}
```

## Block projection obeys shadowing and sequential let bindings

A local variable sharing a module's name still supports record field projection according to let order.

```toml case
id = "block-projection-obeys-shadowing-and-sequential-let-bindings"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module BlockProjectionObeysShadowingAnd {
  \inductive Unit: \Set := | unit: Unit;
  \module x {
    \definition field: \Set := Unit;
  }
  \structure Box: \Set := { field: Unit, };
  \definition get: Box -> Unit := \block {
    \fun (x: Box) \then
    \let y: Box := x \then
    \let x: Box := y \then
    \return x.field
  };
  \import \root.BlockProjectionObeysShadowingAnd[].x[] \as X;
  \definition Type: \Set := X.field;
}
```

## Signature arguments in records and inductive types

Signature fields can be used through records, inductive types, and nested structure indices.

```toml case
id = "signature-arguments-in-records-and-inductives"
scope = "module"
expect = "accept"
```

```ref
\structure Carrier := { A: \Set, };
\structure Nested := { carrier: Carrier, unit: carrier.A, };
\structure Witness[C: Carrier]: \Prop := { witness: \forall (x: C.A) -> x = x, };
\inductive Family[C: Carrier]: \Set := | intro: C.A -> Family;
\structure Holder[N: Nested]: \Set := { value: N.carrier.A, };
\definition Type[N: Nested]: \Set := Holder[N];
\definition proof[C: Carrier][x: C.A]: Witness[C] :=
  Witness[C] { witness := \fun (x: C.A) => \refl(x) };
\definition element[C: Carrier][x: C.A]: Family[C] := Family[C]::intro x;
```

## Expanded structure arguments preserve index type checks

A Bit structure is passed to an index requiring Unit.

```toml case
id = "expanded-structure-arguments-preserve-index-type-checks"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\inductive Bit: \Set := | zero: Bit | one: Bit;
\structure Operations[Carrier: \Set] := { unit: Carrier, };
\structure Witness[Carrier: \Set, data: Operations[Carrier]] := {};
\definition data: Operations[Bit] := Operations[Bit] { unit := Bit::zero };
\definition bad: Witness[Unit, data] := Witness[Unit, data] {};
```

## Nominal types share convertible import arguments

Imports taking a type alias or its original type can be used as the same nominal type.

```toml case
id = "nominal-types-share-convertible-import-arguments"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module NominalTypesShareConvertibleImport {
  \module Pass(A: \Set) {
    \inductive Token: \Set := | token: Token;
  }
  \module Outer(K: \Set) {
    \inductive Unit: \Set := | unit: Unit;
    \definition Alias: \Set := Unit;
    \import \root.NominalTypesShareConvertibleImport[].Pass[A := Alias] \as P;
    \import \root.NominalTypesShareConvertibleImport[].Pass[A := Unit] \as Q;
    \definition Token: \Set := P.Token;
    \definition convert[x: P.Token]: Q.Token := x;
  }
  \inductive Tag: \Set := | zero: Tag;
  \import \root.NominalTypesShareConvertibleImport[].Outer[K := Tag] \as O;
  \definition identity[x: O.Token]: O.Token := O.convert x;
}
```

## Structure argument count / few

The argument count differs from the structure declaration.

```toml case
id = "structure-arity-few"
scope = "module"
expect = "reject"
```

```ref
\structure Operations[Carrier: \Set] := { unit: Carrier };
\structure Witness[Carrier: \Set, data: Operations[Carrier]] := {};
\structure Bad[Carrier: \Set] := { data: Operations[Carrier], law: Witness[Carrier] };
```

## Structure argument count / many

The argument count differs from the structure declaration.

```toml case
id = "structure-arity-many"
scope = "module"
expect = "reject"
```

```ref
\structure Operations[Carrier: \Set] := { unit: Carrier };
\structure Witness[Carrier: \Set, data: Operations[Carrier]] := {};
\structure Bad[Carrier: \Set] := { data: Operations[Carrier], law: Witness[Carrier, data, data, data] };
```
