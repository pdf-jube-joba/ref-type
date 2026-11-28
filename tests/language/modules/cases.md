# Modules and instantiation

## Distinct namespace arguments

A value from one instantiation cannot be used at the nominal type from different module arguments.

```toml case
id = "distinct-namespace-arguments"
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

## Distinct namespace sources

A value from one module cannot be used at the nominal type declared by another module.

```toml case
id = "distinct-namespace-sources"
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

## Module parameter types must be in scope

An undeclared name is used as a module parameter.

```toml case
id = "module-parameter-unknown-type"
scope = "module"
expect = "reject"
parameters = '''A: B,'''
```

```ref

```

## Module nested

Child modules can reference parent parameters and declarations.

```toml case
id = "module-nested"
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

## Applying imported type functions

Module instantiation can substitute parameters and reference members.

```toml case
id = "imported-type-function-application"
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

## Imported function types through aliases

Instantiated module members can be used at corresponding types.

```toml case
id = "imported-function-type-alias"
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

## Parent import scope

Child modules can use their parent's import aliases and macros.

```toml case
id = "parent-import-scope"
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

## Program inductive instance

Inductive types from instantiated Program modules can be distinguished and used.

```toml case
id = "program-inductive-instance"
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

## Structure instance

Structures inside instantiated modules can be constructed with corresponding fields.

```toml case
id = "structure-instance"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module StructureSource(A: \Set, a: A) {
  \structure Box: \Set := {
    value: A,
  };
  \definition Box::get[box: Box]: A := Box::value box;
  \definition boxed: Box := Box { value := a };
}

\module StructureConsumer(B: \Set, b: B) {
  \import \root.StructureSource[A := B, a := b] \as Source;
  \check Source.Box::get Source.boxed: B;
  \check Source.Box::value Source.boxed: B;
}
```

## Substitution identity

Reusing the same arguments in module substitution preserves type identity.

```toml case
id = "substitution-identity"
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

## Proof parameters use earlier propositions

Later module parameters can depend on earlier parameters' types.

```toml case
id = "proof-parameters-use-earlier-propositions"
scope = "module"
expect = "accept"
name = "DependParam"
parameters = '''P1: \Prop,
  p1: P1,'''
```

```ref

```

## Function parameters use earlier domain and codomain types

Function parameters can use the domain and codomain types declared earlier in the same module header.

```toml case
id = "function-parameters-use-earlier-types"
scope = "module"
expect = "accept"
name = "DependParam"
parameters = '''X, Y: \Set,
  f, g: X -> Y,'''
```

```ref

```

## Convertible index alias in a nested module argument

A nested import accepts a structure argument when the index in its type is convertible to the index expected by the imported module. Here both indices come from the same definition after specializing the enclosing module. See [issue #118](https://github.com/pdf-jube-joba/ref-type/issues/118).

```toml case
id = "convertible-index-alias-in-nested-import"
scope = "package"
entry = "alias.ref"
expect = "accept"
```

```ref file=alias.ref
\module Repro {
\inductive Nat: \VType := | zero: Nat | succ: Nat -> Nat ;
\module Models(n: Nat^) {
  \structure Model := { index: Nat^, };
}
\module Library(n: Nat^) {
  \definition dimension: Nat^ := n;
  \import \root.Repro[].Models[n := dimension] \as Source;
  \module Between(M: Source.Model) {
    \module Level {
      \definition answer: Nat^ := M.index;
    }
  }
}
\module Caller(n: Nat^) {
  \import \root.Repro[].Library[n := n] \as Lib;
  \import \root.Repro[].Models[n := Lib.dimension] \as Source;
  \module Between(M: Source.Model) {
    \module Level {
      \import Lib.Between[M := M].Level[] \as Value;
      \definition answer: Nat^ := Value.answer;
    }
  }
}
}
```
