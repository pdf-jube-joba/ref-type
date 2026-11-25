# Binders and local definitions

## Structure arguments and local scopes

Structure fields can be used from local binders and subset definitions and reduce to the same values.

```toml case
id = "shared_definitions_preserve_subset_and_local_scopes"
scope = "module"
expect = "accept"
name = "Sharing"
```

```ref
\structure Bundle := { Carrier: \Set, seed: Carrier };
\definition identity[B: Bundle][x: B.Carrier]: B.Carrier := x;
\definition Fixed[B: Bundle]: \Pow B.Carrier :=
  { b: B.Carrier \where identity B b = b };
\inductive Unit: \Set := | unit: Unit;
\definition bundle: Bundle := Bundle { Carrier := Unit, seed := Unit::unit };
\definition delayed: Unit -> Unit := \fun (_: _) => bundle.seed;
\definition delayedLaw: delayed Unit::unit = Unit::unit := \refl(Unit::unit);
\definition local[B: Bundle][x: B.Carrier][unused: x = x]: B.Carrier := identity B x;
\definition localLaw[B: Bundle][x: B.Carrier]: local B x (\refl(x)) = x := \refl(x);
```

## Functions inside blocks

A stored value is not captured by a later binder with the same name and agrees with a directly written function.

```toml case
id = "logical_block_fun_preserves_binder_order_and_scope"
scope = "module"
expect = "accept"
name = "BlockFunctions"
parameters = '''A: \Set, P: A -> \Set'''
```

```ref
\definition direct: \forall (x, y: A) (h: P x) -> A -> P x :=
  \fun (x, y: A) (h: P x) (z: A) => h;
\definition blocked: \forall (x, y: A) (h: P x) -> A -> P x := \block {
  \fun (x, y: A) (h: P x) \then
  \let saved: P x := h \then
  \fun (x: A) \then
  \return saved
};
\definition same: blocked = direct := \refl(direct);
```

## Let expansion and shadowing

Let values and type aliases expand transparently and retain original references through nesting and same-named binders.

```toml case
id = "logical_let_definitions_are_transparent_and_capture_avoiding"
scope = "module"
expect = "accept"
name = "LocalDefinitions"
parameters = '''A: \Set, a: A'''
```

```ref
\macro equality($x, $y) := $x = $y;
\definition simple: a = a := \block {
  \let x: A := a \then
  \let h: x = a := \refl(a) \then
  \return h
};
\definition nested: \forall (x: A) -> \forall (y: A) -> x = x :=
  \fun (x: A) => \block {
  \let saved: A := x \then
  \let alias: A := saved \then
  \fun (x: A) \then
  \let x: A := alias \then
  \let h: equality!{x saved} := \refl(saved) \then
  \return h
};
\definition shadowed: \forall (x: A) -> x = x := \block {
  \let x: A := a \then
  \return \fun (x: A) => \refl(x)
};
\definition restored: a = a := \block {
  \let x: A := a \then
  \let f: A -> A := \fun (x: A) => \block {
    \let x: A := x \then
    \return x
  } \then
  \return \refl(f x)
};
\definition inferred: a = a := \block {
  \let x: _ := a \then
  \let h: x = a := \refl(x) \then
  \return h
};
\definition inferred_later: a = a := \block {
  \let x: A := _ \then
  \let h: x = a := \refl(a) \then
  \return h
};
\definition type_alias: a = a := \block {
  \let T: \Set := A \then
  \let x: T := a \then
  \let P: \Prop := x = a \then
  \let h: P := \refl(a) \then
  \return h
};
\definition unused_proof: A := \block {
  \let h: a = a := \refl(a) \then
  \return a
};
```

## Goals after enough

After supplying an implication from P to Q, proving P yields a proof of Q.

```toml case
id = "logical_enough_changes_the_remaining_goal"
scope = "module"
expect = "accept"
name = "Enough"
parameters = '''P, Q: \Prop, p: P, implication: P -> Q'''
```

```ref
\definition result: Q := \block {
  \enough P \by { implication } \then
  \return p
};
```

## Let type annotations

A let annotation makes x a value of the base type A, so returning it as a subset value without a membership proof is rejected.

```toml case
id = "logical_let_preserves_the_declared_type"
scope = "module"
expect = "reject"
name = "LocalAnnotation"
parameters = '''A: \Set, S: \Pow (A), s: \Cast[A] (S)'''
```

```ref
\definition invalid: \Cast[A] (S) := \block {
  \let x: A := s \then
  \return x
};
```

## Grouped product binders

The variables p, q, and r are all bound as proofs of the outer P.

```toml case
id = "grouped_product_binders_keep_the_outer_type"
scope = "module"
expect = "accept"
name = "Grouped"
```

```ref
\definition last: \forall (P: \Prop) -> \forall (p, q, r: P) -> P :=
  \fun (P: \Prop) => \fun (p: P) => \fun (q: P) => \fun (r: P) => r;
```

## Grouped lambda binders

A declaration's grouped binders share the type annotation from before a same-named P is bound.

```toml case
id = "grouped_lambda_binders_keep_the_outer_type"
scope = "module"
expect = "accept"
name = "Grouped"
```

```ref
\definition last: \forall (P: \Prop) -> P -> P -> P -> P :=
  \fun (P: \Prop) => \fun (p, q, r: P) => r;
\definition shadowed: \forall (P: \Prop) -> P -> P -> P :=
  \fun (P: \Prop) => \fun (P, p: P) => p;
```

## Grouped declaration arguments

The inductive type's x, y, and z all have the same outer type A.

```toml case
id = "grouped_declaration_binders_keep_the_outer_type"
scope = "module"
expect = "accept"
name = "Grouped"
```

```ref
\inductive Witness[A: \Set, x, y, z: A]: \Prop :=
  | intro: Witness
;
```

## Membership and Cast as function values

Membership and Cast can be bound to names as functions and applied to subsets.

```toml case
id = "membership_and_cast_are_first_class_functions"
scope = "module"
expect = "accept"
name = "SetOperators"
parameters = '''A: \Set, subset: \Pow A'''
```

```ref
\definition membership: \Pow A -> A -> \Prop := \In[A];
\definition cast: \Pow A -> \Set := \Cast[A];
\definition Specialized: \Set := cast subset;
```

## Unused let / 1

A proposition proof is passed where a set value is required; definitions unused in the result are also checked.

```toml case
id = "unused-let-0"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set, a: A, P: \Prop, p: P'''
```

```ref
\definition example: a = a := \block { \let unused: A := p \then \return \refl(a) };
```

## Unused let / 2

A set value is passed where a proposition proof is required; definitions unused in the result are also checked.

```toml case
id = "unused-let-1"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set, a: A, P: \Prop, p: P'''
```

```ref
\definition example: a = a := \block { \let unused: P := a \then \return \refl(a) };
```

## Unused let / 3

No constraints determine the type or value; definitions unused in the result are also checked.

```toml case
id = "unused-let-2"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set, a: A, P: \Prop, p: P'''
```

```ref
\definition example: a = a := \block { \let unused: _ := _ \then \return \refl(a) };
```

## Unused let / 4

The definition references itself before being bound; definitions unused in the result are also checked.

```toml case
id = "unused-let-3"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set, a: A, P: \Prop, p: P'''
```

```ref
\definition example: a = a := \block { \let unused: A := unused \then \return \refl(a) };
```
