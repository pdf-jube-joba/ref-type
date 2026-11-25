# Checking with type ascriptions

## Logic type ascriptions

Lambda arguments are inferred from expected types, and type ascriptions survive macro expansion and module specialization.

```toml case
id = "ascription_infers_types_and_works_through_macros_and_modules"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Annotated(A: \Set, a: A) {
  \macro typed($x) := $x \of A;
  \definition value: A := typed!{a};
  \definition inferred: A := a \of _;
  \definition identity: A -> A := (\fun (x: _) => x) \of A -> A;
  \definition applied: A := (identity \of A -> A) a;
  \definition kind: \SetKind := \Set \of \SetKind;
  \definition local: A := \block {
    \let x: A := a \of A \then
    \return x
  };
}
\module Use {
  \inductive Unit: \Set := | unit: Unit;
  \import \root.Annotated[A := Unit, a := Unit::unit] \as M;
  \definition value: Unit := M.value;
  \definition equal: M.value = Unit::unit := \refl(Unit::unit);
}
```

## Program type ascriptions

Values and computations can be ascribed the types of their respective judgments and used in application and reflection.

```toml case
id = "ascription_supports_program_values_computations_and_reflection"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module AnnotatedProgram(A: \VType, a: A) {
  \definition value: A := a \of A;
  \definition inferred: A := a \of _;
  \definition computation: \F A := (\return a) \of \F A;
  \definition identity: A -> A := (\fun (x: _) => \return x) \of A -> A;
  \definition applied: \F A := (identity \of A -> A) (a \of A);
  \definition explicit: \F A := (identity \of A ~> \F A) a;
  \definition thunk: \U(A ~> \F A) := \thunk identity;
  \definition forced: \F A := \force (thunk \of \U(A ~> \F A)) a;
  \definition reflected: value^ = a^ := \refl(a^);
  \check computation: \F A;
  \check a \of A: A;
}
\module ProgramUse {
  \inductive Bool: \VType := | yes: Bool;
  \import \root.AnnotatedProgram[A := Bool, a := Bool::yes] \as M;
  \definition value: Bool := M.value;
  \definition computation: \F Bool := M.forced;
}
```

## Mismatched Logic types

The original term's type does not match the ascription.

```toml case
id = "wrong-ascription-0"
scope = "module"
expect = "reject"
name = "Wrong"
parameters = '''A: \Set, B: \Set, a: A'''
```

```ref
\definition value: A := a \of B;
```

## Mismatched Program value types

The original term's type does not match the ascription.

```toml case
id = "wrong-ascription-1"
scope = "module"
expect = "reject"
name = "Wrong"
parameters = '''A: \VType, B: \VType, a: A'''
```

```ref
\definition value: A := a \of B;
```

## Mismatched Program computation types

The original term's type does not match the ascription.

```toml case
id = "wrong-ascription-2"
scope = "module"
expect = "reject"
name = "Wrong"
parameters = '''A: \VType, B: \VType, a: A'''
```

```ref
\definition value: \F A := (\return a) \of \F B;
```

## Ascribing a subset element with its base type

A subset element can be ascribed its base type and used as a value of that type.

```toml case
id = "subset-ascription-0"
scope = "module"
expect = "accept"
name = "Widen"
parameters = '''A: \Set, S: \Pow A, s: \Cast[A] S'''
```

```ref
\definition value: A := s \of A;
\definition equal: value = s := \refl(s);
```

## Returning to a subset after ascription

A value ascribed its base type is used as a subset value without a membership proof.

```toml case
id = "subset-ascription-1"
scope = "module"
expect = "reject"
name = "Narrow"
parameters = '''A: \Set, S: \Pow A, s: \Cast[A] S'''
```

```ref
\definition value: \Cast[A] S := s \of A;
```
