# Structures

Structures bundle related types, values, operations, and laws.
A field's type may depend on preceding fields in declaration order.

## Declaration bundles

```text
\structure Relation := {
  A: \Set,
  R: A -> A -> \Prop,
};
\definition Equality[A: \Set]: Relation := Relation {
  A := A,
  R := \fun(x, y: A) => x = y,
};
\definition diagonal[r: Relation][x: r.A]: \Prop := r.R x x;
```

A signature without an explicit sort expands into a dependent context of fields.
Signatures can appear as arguments, results, and nested fields; each member of a literal is checked against its instantiated type.
Fixed types and values can be parameters.

```text
\structure BasedRelation[A: \Set] := {
  relation: Relation,
  base: relation.A,
  map: A -> relation.A,
};
```

Passing a structure as a module parameter uses the same field substitution.
Taking a definition that returns a structure as an argument forms a function type for each member and checks it against the ordinary product rules.

## Defaults and Program fields

A field with a default body may be omitted from a literal.
Overridden values are also substituted into the types and bodies of later dependent fields.

```text
\structure Duplicate[A: \Set] := {
  value: A,
  copy: A := value,
  same: copy = value := \refl(value),
};
\definition duplicate[A: \Set][a: A]: Duplicate[A] := Duplicate[A] { value := a };

\structure ProgramData := {
  T: \VType,
  value: T,
  result: \F T := \return value,
};
\definition run[d: ProgramData]: \F(d.T) := d.result;
```

Program value types, values, and computations are checked according to their respective categories.
Computation fields are passed internally as thunks; accessing a field returns the original computation.
`std.Program.Correspondence` and `Machine` also use this form of signature.

Records with an explicit sort support defaults for proof fields when the record's sort is `\Prop`.

```text
\structure Reflexive[A: \Set, a: A]: \Prop := {
  same: a = a := \refl(a),
};
\definition reflexive[A: \Set][a: A]: Reflexive[A, a] := Reflexive[A, a] {};
```

## Records with explicit sorts

Specify a sort to make the entire bundle available for equality or induction.
The declaration expands into an inductive type with one constructor and projections, with fields checked for compatibility with the sort.

```text
\structure EqualPair[A: \Set]: \Set := {
  first: A,
  second: A,
  same: first = second,
};
\definition equalPair[A: \Set][a: A]: EqualPair[A] := EqualPair[A] {
  first := a,
  second := a,
  same := \refl(a),
};
```

Proofs of propositions are classified as laws; other fields are data.
If laws are present, the implementation generates an inductive type for the data, a proposition for the laws, and a refinement of values satisfying those laws.
Both data and law fields can be accessed from a value.
To handle them separately, define the data and laws explicitly.

```text
\structure PairData[A: \Set]: \Set := { first: A, second: A };
\structure PairLaws[A: \Set, p: PairData[A]]: \Prop := { same: p.first = p.second };
\definition EqualPairs[A: \Set]: \Set :=
  \Cast[PairData[A]] ({ p: PairData[A] \where PairLaws[A, p] });
```

See [type-associated items](types_and_items.md#program-records) for Program record restrictions and projections.

## Quantification

Universal quantification over a declaration bundle expands into a dependent product binding each field in order.
Existential quantification over a bundle with associated types expands into
`\forall(P: \Prop) -> (\forall(r: Relation) -> P) -> P`, expressing elimination into propositions.

```text
\definition existsRelation: \Prop := \exists(r: Relation);
\definition witness[A: \Set]: existsRelation := \exact(Equality A, Relation);
\definition repack[e: existsRelation]: existsRelation := \block {
  \takefrom r: Relation \by e \then
  \return \exact(r, Relation)
};
```

`\exact` checks member compatibility.
`\take` and `\takefrom` expand the witness's fields into the local context to prove a proposition that does not depend on the witness.
Records of sort `\Set` use ordinary existential quantification over sets.
