# modules / cases

## distinct namespace arguments

異なる引数で具体化した nominal な型を同一視している。

```toml case
id = "reject-modules.distinct-namespace-arguments"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Source(A: \Set) {
  \inductive Token: \Set := | token: Token;
}
\module Consumer(A, B: \Set) {
  \import \root.Source[A := A] \as Left;
  \import \root.Source[A := B] \as Right;
  \definition invalid: Right.Token := Left.Token::token;
}
```

## distinct namespace sources

異なる module の nominal な型を同一視している。

```toml case
id = "reject-modules.distinct-namespace-sources"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module First {
  \inductive Token: \Set := | token: Token;
}
\module Second {
  \inductive Token: \Set := | token: Token;
}
\module Consumer {
  \import \root.First[] \as Left;
  \import \root.Second[] \as Right;
  \definition invalid: Right.Token := Left.Token::token;
}
```

## param free

宣言されていない名前を module parameter として使っている。

```toml case
id = "reject-param_free"
scope = "module"
expect = "reject"
name = "Hello"
parameters = '''A: B,'''
```

```ref

```

## module nested

子 module が親の parameter と宣言を参照できる。

```toml case
id = "accept-modules.module_nested"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Test1 (A: \Set) {
  \module Child1 (B: \Set) {
    \definition A_to: \Set := A;
    \definition B_to: \Set := B;
  }
}
```

## module reference

module の具体化で parameter を置換して member を参照できる。

```toml case
id = "accept-modules.module_reference"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Test1{
  \definition i: \forall (X: \Set) -> \Set := \fun (X: \Set) => X;
}

\module Test2(
  A: \Set,
){
  \definition a1: \Set := (\fun (X: \Set) => X) A;
  \import \root.Test1[] \as T;
  \definition i2: \forall (X: \Set) -> \Set := T.i;
  \definition a2: \Set := i2 A;
  \definition a3: \Set := T.i A;
}
```

## module reference2

具体化した module の member を対応する型で利用できる。

```toml case
id = "accept-modules.module_reference2"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Test1{
  \definition ity: \SetKind := \forall (X: \Set) -> \Set;
  \definition i: ity := \fun (X: \Set) => X;
}

\module Test2(
  A: \Set,
){
  \definition a1: \Set := (\fun (X: \Set) => X) A;
  \import \root.Test1[] \as T;
  \definition i2: T.ity := T.i;
  \definition i3: \forall (X: \Set) -> \Set := T.i;
  \definition a2: \Set := i3 A;
  \definition a3: \Set := T.i A;
}
```

## parent import scope

子 module が親の import alias と macro を利用できる。

```toml case
id = "accept-modules.parent_import_scope"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Source(A: \Set, value: A) {
  \definition get: A := value;
  \macro get_macro() := value;

  \module Nested {
    \definition get: A := value;
  }
}

\module Parent(A: \Set, value: A) {
  \import \root.Source[A := A, value := value] \as Shared;

  \module Child {
    /* The parent's import alias is in scope for ordinary name resolution. */
    \definition direct: A := Shared.get;

    /* It can also be used as the base of another module import. */
    \import Shared.Nested[] \as Nested;
    \definition nested: A := Nested.get;

    /* Imported macro lookup follows the same parent scope. */
    \use Shared.get_macro;
    \definition from_macro: A := get_macro!{};
  }
}

\module Consumer {
  \inductive Unit: \Set :=
  | unit: Unit
  ;

  \import \root.Parent[A := Unit, value := Unit::unit] \as Parent;
  \import Parent.Child[] \as Child;
  \definition direct: Unit := Child.direct;
  \definition nested: Unit := Child.nested;
  \definition from_macro: Unit := Child.from_macro;
}
```

## program inductive instance

具体化した Program module の帰納型を区別して使える。

```toml case
id = "accept-modules.program_inductive_instance"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module ProgramSource {
  \inductive Box[X: \VType]: \VType :=
  | box: X -> Box
  ;
}

\module ProgramConsumer {
  \import \root.ProgramSource[] \as Source;
  \inductive Unit: \VType :=
  | unit: Unit
  ;
  \definition boxed: Source.Box[Unit] := Source.Box[Unit]::box Unit::unit;
  \definition package: \Box[\F(Source.Box[Unit])] :=
    \box[_](\return(boxed));
  \normalize \squash[_](package);
  \infer Source.Box^[Unit^]::box Unit^::unit;
}
```

## structure instance

具体化した module 内の structure を対応する field で構築できる。

```toml case
id = "accept-modules.structure_instance"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module StructureSource(A: \Set, a: A) {
  \structure Box: \Set := {
    value: A,
  };
  \definition Box::get(box: Box): A := Box::value box;
  \definition boxed: Box := Box { value := a };
}

\module StructureConsumer(B: \Set, b: B) {
  \import \root.StructureSource[A := B, a := b] \as Source;
  \check Source.Box::get Source.boxed: B;
  \check Source.Box::value Source.boxed: B;
}
```

## substitution identity

module の置換で同じ引数を再利用すると型の同一性を保つ。

```toml case
id = "accept-modules.substitution-identity"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Source(A: \Set, a: A, proof: a = a) {
  \structure Box: \Set := { value: A };
  \definition boxed: Box := Box { value := a };
  /* This declaration must not require a proof-to-Set product rule. */
  \definition Carrier: \Set := A;
}
\module Outer(A: \Set, a: A) {
  \import \root.Source[A := A, a := a, proof := \refl(a)] \as S;
  \definition Box: \Set := S.Box;
  \definition boxed: Box := S.boxed;
}
\module Consumer(B: \Set, b: B) {
  \definition alias: B := (\fun (x: B) => x) b;
  \import \root.Source[A := B, a := b, proof := \refl(b)] \as Left;
  \import \root.Source[A := B, a := alias, proof := \refl(alias)] \as Right;
  \import \root.Outer[A := B, a := b] \as Nested;
  \definition same: Right.Box := Left.boxed;
  \definition through_outer: Nested.Box := Right.boxed;
  \definition from_outer: Left.Box := Nested.boxed;
  \definition carrier: Right.Carrier := b;
}
```

## parameter dependent

後続の module parameter が先行する parameter の型に依存できる。

```toml case
id = "accept-parameter_dependent"
scope = "module"
expect = "accept"
name = "DependParam"
parameters = '''P1: \Prop,
  p1: P1,'''
```

```ref

```

## parameter dependent2

依存 parameter を具体化すると後続の型も置換される。

```toml case
id = "accept-parameter_dependent2"
scope = "module"
expect = "accept"
name = "DependParam"
parameters = '''X, Y: \Set,
  f, g: X -> Y,'''
```

```ref

```

