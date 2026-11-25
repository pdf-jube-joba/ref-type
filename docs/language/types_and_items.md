# Type-associated items and projections

Use `::` to refer to constructors and type-associated items, and `.` to access fields.
See [structures](structure.md) for declarations and the treatment of laws.

## Declarations and access

```text
\inductive List[A: \Set]: \Set :=
| nil: List
| cons: A -> List -> List
;
\definition List[A: \Set]::singleton[x: A]: List[A] :=
  List[A]::cons x List[A]::nil;
```

A type-associated definition belongs to the same module as its owner and binds the owner's parameters first.
Constructors, projections, and associated definitions must have distinct names.

```text
List[A]::nil
List[A]::singleton x
Import.List[A]::singleton x
```

A type named by `\definition` can also be used for constructor access and induction if it unfolds to an inductive type.

```text
\definition Values: \Set := List[A];
\definition empty: Values := Values::nil;
\definition copy: Values -> Values :=
  \induction (xs: Values) \return Values \with {
    | nil: Values::nil
    | cons: \fun (x: A) (xs, previous: Values) => Values::cons x previous
  };
```

Aliases preserve the parameters and induction indices of the underlying type.
A refinement type remains distinct from the inductive type of its carrier.

## Program records

Records of sort `\VType` have nondependent, nonrecursive value fields, which may include thunk types `\U C`.

```text
\structure Pair[A: \VType]: \VType := {
  first: A,
  second: A,
};
\definition Pair[A: \VType]::swap[p: Pair[A]]: \F(Pair[A]) :=
  \program {
    \bind x: A <- Pair[A]::first p \then
    \bind y: A <- Pair[A]::second p \then
    \return Pair[A] { first := y, second := x }
  };
```

A projection is a computation of type `Pair[A] ~> \F A`; receive its result with `\bind` before using the value.
Program type arguments may be omitted or written as `_` when the context determines them.
`Type[A]::item^` refers to the reflection of a type-associated item.

## Type-directed projections

`p.first` resolves the projection from the type of `p`.
Set records with laws expose both data and law fields; Program record projections return computations.
Projections also work on variables introduced by `\fun` and `\let` inside blocks.
