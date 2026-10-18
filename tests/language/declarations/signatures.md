# declarations / signatures

## ambient signature parameter

空の signature でも外側の module を異なる引数で具体化すると同一にはならない。

```toml case
id = "reject-declarations.ambient_signature_parameter"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module AmbientSignature {
  \inductive Unit: \Set := | unit: Unit;
  \inductive Other: \Set := | other: Other;
  \module Parameter(A: \Set) { \structure Marker := {}; }
  \import .Parameter[A := Unit] \as First;
  \import .Parameter[A := Other] \as Second;
  \definition marker: First.Marker := First.Marker {};
  \definition bad: Second.Marker := marker;
}
```

## contextual unused argument

contextual definition の未使用引数にも型の不一致がある。

```toml case
id = "reject-declarations.contextual_unused_argument"
scope = "module"
expect = "reject"
name = "Guard"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\structure Relation := { A: \Set, R: A -> A -> \Prop, };
\definition make[A: \Set][unused: A]: Relation := Relation { A := A, R := \fun(x,y:A) => x = y, };
\definition bad: Relation := make Unit \Set;
```

## empty signature import

import の parameter が Empty[Unit] を要求するのに、Empty[Other] の値を渡している。

```toml case
id = "reject-declarations.empty_signature_import"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module EmptyImport {
  \inductive Unit: \Set := | unit: Unit;
  \inductive Other: \Set := | other: Other;
  \structure Empty[A: \Set] := {};
  \definition other: Empty[Other] := Empty[Other] {};
  \module Use(t: Empty[Unit]) {}
  \import .Use[t := other] \as Bad;
}
```

## existence signature

Tag[Other] の存在証明に Tag[Unit] の witness を渡している。

```toml case
id = "reject-declarations.existence_signature"
scope = "module"
expect = "reject"
name = "ExistentialSignature"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\inductive Other: \Set := | other: Other;
\structure Tag[A: \Set] := {};
\definition wrong: \exists Tag[Other] := \exact(Tag[Unit] {}, Tag[Other]);
```

## forward member

通常の member が宣言位置より後の member を参照する。

```toml case
id = "reject-declarations.forward_member"
scope = "module"
expect = "reject"
name = "Forward"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\structure Signature := { later: earlier = Unit::unit, earlier: Unit };
```

## kind field

field の型として classifier を持たない上位 sort `\SetKind` を使っている。

```toml case
id = "reject-declarations.kind_field"
scope = "module"
expect = "reject"
name = "KindField"
```

```ref
\structure Bad := { A: \SetKind, };
```

## private helper

子 module の helper を import や修飾なしで親の scope から参照している。

```toml case
id = "reject-declarations.private_helper"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Private {
  \inductive Unit: \VType := | unit: Unit;
  \module Implementation {
    \definition helper: Unit ~> \F(Unit) := \cfun(x: Unit) => \return x;
  }
  \definition escaped: Unit ~> \F(Unit) := helper;
}
```

## signature parameter

異なる引数で具体化した空の signature の値を同一視している。

```toml case
id = "reject-declarations.signature_parameter"
scope = "module"
expect = "reject"
name = "Parameter"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\inductive Other: \Set := | other: Other;
\structure Empty[A: \Set] := {};
\definition bad: Empty[Unit] := Empty[Other] {};
```

## contextual definitions

局所文脈を保った definition の引数置換が型を保つ。

```toml case
id = "accept-declarations.contextual_definitions"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module ContextualDefinitions(A: \Set, a: A, P: \Prop, p: P) {
  \definition choose[h: P][x: A]: A := x;
  \definition chosen: A := choose p a;
  \definition partiallyApplied: A -> A := choose p;
  \definition computes: partiallyApplied a = a := \refl(a);
  \definition dependent[B: \Set][x: B]: B := x;
  \definition dependentComputes: dependent A a = a := \refl(a);
  \definition Inferred[x: _]: A := x;
  \definition inferredComputes: Inferred a = a := \refl(a);
  \definition predicate[R: A -> \Prop]: \Prop := R a;
  \definition predicateProof: predicate (\fun(x: A) => x = x) := \refl(a);

  \structure Holder[B: \Set]: \Set := { value: B, };
  \definition Holder[B: \Set]::choose[h: P][x: B]: B := x;
  \definition Holder[B: \Set]::Relation: \PropKind := B -> B -> \Prop;
  \definition associatedPartial: A -> A := Holder[A]::choose p;
  \definition associatedComputes: Holder[A]::choose p a = a := \refl(a);
  \definition associatedInferred: Holder::choose p a = a := \refl(a);
  \definition equality: Holder[A]::Relation := \fun(x, y: A) => x = y;
  \definition equalityProof: equality a a := \refl(a);

  \definition Restricted: \Set := \Cast[\Pow A] ({ S: \Pow A \where P });
  \definition forget[S: Restricted]: \Pow A := S;
  \definition extensional[S: Restricted]: forget S = forget S :=
    \axiom:setext(forget S, forget S,
      \fun(x: A)(h: \In[A] (forget S) x) => h,
      \fun(x: A)(h: \In[A] (forget S) x) => h);

  \structure Relation := { Carrier: \Set, relation: Carrier -> Carrier -> \Prop, };
  \definition Equality[B: \Set]: Relation := Relation {
    Carrier := B, relation := \fun(x, y: B) => x = y,
  };
  \definition withStructure[h: P][r: Relation][x: r.Carrier]: r.Carrier := x;
  \definition structureComputes: withStructure p (Equality A) a = a := \refl(a);
}

\module ContextualImports(A: \Set, a: A, P: \Prop, p: P) {
  \import \root.ContextualDefinitions[A := A, a := a, P := P, p := p] \as D;
  \definition chosen: A := D.choose p a;
  \definition partiallyApplied: A -> A := D.choose p;
  \definition computes: partiallyApplied a = a := \refl(a);
  \definition associated: D.Holder[A]::choose p a = a := \refl(a);
  \definition family: D.Holder[A]::Relation := \fun(x, y: A) => x = y;
  \definition familyProof: family a a := \refl(a);
}
```

## signatures

signature の引数と実装の field が一致する。

```toml case
id = "accept-declarations.signatures"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module StructureSignatures {

  \inductive RelSet: \PropKind :=
  | ctor: \forall (A: \Set) -> \forall (R: A -> A -> \Prop) -> RelSet;

  \inductive Unit: \Set := | unit: Unit;
  \definition retain[A: \Set][R: A -> A -> \Prop][a: A]: A := a;
  \check retain Unit (\fun (x, y: Unit) => x = y) Unit::unit: Unit;
  \structure Relation := {
    A: \Set,
    R: A -> A -> \Prop,
  };
  \definition carrier[r: Relation]: \Set := r.A;
  \check carrier (Relation { A := Unit, R := \fun (x, y: Unit) => x = y, }): \Set;
  \definition Equality[A: \Set]: Relation := Relation { A := A, R := \fun (x, y: A) => x = y, };
  \check carrier (Equality Unit): \Set;
  \check (Equality Unit).R Unit::unit Unit::unit: \Prop;
  \structure Outer := { inner: Relation, element: inner.A, };
  \definition related[o: Outer]: \Prop := o.inner.R o.element o.element;
  \check related (Outer { inner := Equality Unit, element := Unit::unit, }): \Prop;
  \inductive PUnit: \VType := | unit: PUnit;
  \structure ProgramData := { T: \VType, value: T, };
  \definition Data: ProgramData := ProgramData { T := PUnit, value := PUnit::unit, };
  \check Data.value: PUnit;
  \definition getValue[d: ProgramData]: d.T := d.value;
  \check getValue Data: PUnit;
  \definition makeData[T: \VType][value: T]: ProgramData := ProgramData { T := T, value := value, };
  \check (makeData PUnit PUnit::unit).value: PUnit;
  \check Data.T^: \Set;
  \check Data.value^: PUnit^;
  \definition carrierRelated: \forall (r: Relation) -> \forall (x: r.A) -> r.R x x -> r.R x x :=
    \fun(r: Relation)(x: r.A)(h: r.R x x) => h;
  \structure Defaults := {
   A: \Set, a: A, copy: A := a, equal: copy = a := \refl(a), other: A,
  };
  \definition defaults: Defaults := Defaults { A := Unit, a := Unit::unit, other := Unit::unit, };
  \check defaults.equal: defaults.copy = defaults.a;
  \structure Calc := { T: \VType, result: \F(T), };
  \definition calc: Calc := Calc { T := PUnit, result := \return PUnit::unit, };
  \normalize calc.result;
  \definition use[c: Calc]: \F(c.T) := c.result;
  \normalize use calc;
  \check calc.result^: PUnit^;


  \definition choose[f: \forall (A: \Set) -> Relation][A: \Set]: Relation := f A;
  \check (choose Equality Unit).R Unit::unit Unit::unit: \Prop;
  \definition WithEquality: \forall (A: \Set) -> Relation := Equality;
  \check (WithEquality Unit).R Unit::unit Unit::unit: \Prop;
  \definition param[A: \Set][x: A]: Relation := Equality A;
  \definition part: \forall (x: Unit) -> Relation := param Unit;
  \check (part Unit::unit).R Unit::unit Unit::unit: \Prop;

  \structure Tag[A: \Set] := { value: A, };
  \definition tag: Tag[Unit] := Tag[Unit] { value := Unit::unit, };
  \module UseTag(t: Tag[Unit]) { \definition value: Unit := t.value; }
  \import .UseTag[t := tag] \as Used;
  \definition tagProof: Used.value = Unit::unit := \refl(Unit::unit);
  \definition choiceProof: (choose Equality Unit).R Unit::unit Unit::unit := \refl(Unit::unit);
  \definition identity[d: ProgramData]: d.T := d.value;
  \definition partialScalar: PUnit := identity Data;

  \definition retainElement[r: Relation][a, b: r.A]: r.A := b;
  \definition selected: Unit := retainElement (Equality Unit) Unit::unit Unit::unit;
  \definition elementOfUnit: Unit -> Unit -> Unit := retainElement (Equality Unit);
  \definition selectedAgain: elementOfUnit Unit::unit Unit::unit = Unit::unit := \refl(Unit::unit);
  \structure NestedCalc := { calculation: Calc, };
  \definition nestedCalc: NestedCalc := NestedCalc { calculation := calc, };
  \definition calculate[n: NestedCalc]: \F(n.calculation.T) := n.calculation.result;
  \normalize calculate nestedCalc;
  \module AbstractTag(A: \Set, t: Tag[A]) { \definition value: A := t.value; }
  \import .AbstractTag[A := Unit, t := tag] \as AbstractUsed;
  \definition abstractTagProof: AbstractUsed.value = Unit::unit := \refl(Unit::unit);
  \structure Witness[A: \Set]: \Set := { value: A, };
  \definition witnessExists: \exists Witness[Unit] := \exact(Witness[Unit] { value := Unit::unit, }, Witness[Unit]);

  \definition chooseOn[f: \forall(A: \Set) -> Tag[A]][A: \Set]: Tag[A] := f A;
  \definition singleton[A: \Set][x: A]: Tag[A] := Tag[A] { value := x, };
  \definition chooseFixed[f: Unit -> Tag[Unit]][x: Unit]: Tag[Unit] := f x;
  \definition chosenTag: Tag[Unit] := chooseFixed (singleton Unit) Unit::unit;
  \definition chosenValue: chosenTag.value = Unit::unit := \refl(Unit::unit);
  \definition chooseAnonymous[f: \Set -> Relation][A: \Set]: Relation := f A;
  \definition anonymousProof: (chooseAnonymous Equality Unit).R Unit::unit Unit::unit := \refl(Unit::unit);

  \module Parametric(A: \Set) { \structure Marker := {}; }
  \import .Parametric[A := Unit] \as First;
  \import .Parametric[A := Unit] \as Second;
  \definition firstMarker: First.Marker := First.Marker {};
  \definition secondMarker: Second.Marker := firstMarker;
}
```

