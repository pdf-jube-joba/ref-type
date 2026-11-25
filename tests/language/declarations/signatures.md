# Declaration signatures

## Ambient signature parameter

Even empty signatures differ when their outer modules are instantiated with different arguments.

```toml case
id = "ambient-signature-parameter"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module AmbientSignature {
  \inductive Unit: \Set := | unit: Unit;
  \inductive Other: \Set := | other: Other;
  \module Parameter(A: \Set) {
    \structure Marker := {};
  }
  \import .Parameter[A := Unit] \as First;
  \import .Parameter[A := Other] \as Second;
  \definition marker: First.Marker := First.Marker {};
  \definition bad: Second.Marker := marker;
}
```

## Contextual unused argument

An unused argument of a contextual definition also has a type mismatch.

```toml case
id = "contextual-unused-argument"
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

## Empty signature import

An import parameter requires Empty[Unit], but a value of Empty[Other] is passed.

```toml case
id = "empty-signature-import"
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

## Existence signature

A Tag[Unit] witness is passed to an existential proof of Tag[Other].

```toml case
id = "existence-signature"
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

## Forward member

An ordinary member references a member declared later.

```toml case
id = "forward-member"
scope = "module"
expect = "reject"
name = "Forward"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\structure Signature := { later: earlier = Unit::unit, earlier: Unit };
```

## Kind field

A field type uses the higher sort `\SetKind`, which has no classifier.

```toml case
id = "kind-field"
scope = "module"
expect = "reject"
name = "KindField"
```

```ref
\structure Bad := { A: \SetKind, };
```

## Private helper

A child module's helper is referenced from the parent's scope without importing or qualifying it.

```toml case
id = "private-helper"
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

## Signature parameter

Even an empty signature retains its arguments, so values from different instantiations cannot be mixed.

```toml case
id = "signature-parameter"
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

## Contextual definitions

Substituting definition arguments while retaining the local context preserves types.

```toml case
id = "contextual-definitions"
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

## Logical and Program signature expansion

Signature expansion preserves logical and Program fields through nested bundles, defaults, function results, partial applications, module arguments, and existential witnesses. The declarations share a small set of fixtures to exercise agreement across those contexts.

```toml case
id = "logical-and-program-signature-expansion"
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
  \module UseTag(t: Tag[Unit]) {
    \definition value: Unit := t.value;
  }
  \import .UseTag[t := tag] \as Used;
  \definition tagProof: Used.value = Unit::unit := \refl(Unit::unit);
  \definition choiceProof: (choose Equality Unit).R Unit::unit Unit::unit := \refl(Unit::unit);
  \definition identity[d: ProgramData]: d.T := d.value;
  \definition extractedProgramValue: PUnit := identity Data;

  \definition retainElement[r: Relation][a, b: r.A]: r.A := b;
  \definition selected: Unit := retainElement (Equality Unit) Unit::unit Unit::unit;
  \definition elementOfUnit: Unit -> Unit -> Unit := retainElement (Equality Unit);
  \definition selectedAgain: elementOfUnit Unit::unit Unit::unit = Unit::unit := \refl(Unit::unit);
  \structure NestedCalc := { calculation: Calc, };
  \definition nestedCalc: NestedCalc := NestedCalc { calculation := calc, };
  \definition calculate[n: NestedCalc]: \F(n.calculation.T) := n.calculation.result;
  \normalize calculate nestedCalc;
  \module AbstractTag(A: \Set, t: Tag[A]) {
    \definition value: A := t.value;
  }
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

  \module Parametric(A: \Set) {
    \structure Marker := {};
  }
  \import .Parametric[A := Unit] \as First;
  \import .Parametric[A := Unit] \as Second;
  \definition firstMarker: First.Marker := First.Marker {};
  \definition secondMarker: Second.Marker := firstMarker;
}
```

## Different carriers in re-exported families

Even through structure aliases, maps before and after conversion retain their respective domain and codomain type arguments.

```toml case
id = "signature-reexport-distinct-carriers"
scope = "module"
expect = "accept"
```

```ref
\module Families {
  \inductive Nat: \Set := | zero: Nat | succ: Nat -> Nat;
  \structure Family := { Carrier: Nat -> \Set };
  \structure FamilyGroup := { family: Family };
  \module Extend(C: FamilyGroup) {
    \definition family: Family := Family { Carrier := C.family.Carrier };
    \definition group: FamilyGroup := FamilyGroup { family := family };
  }
  \module Maps(C, D: FamilyGroup) {
    \definition Map: \Set := \forall (n: Nat) -> C.family.Carrier n -> D.family.Carrier n;
    \module Child(f: Map) {
      \import \parent.\parent.Extend[C := C] \as Source;
      \import \parent.\parent.Extend[C := D] \as Target;
      \import \parent.\parent.Maps[C := Source.group, D := Target.group] \as Result;
      \definition copy: Result.Map := f;
    }
  }
}
\module Make(A: \Set) {
  \import \parent.Families[] \as Types;
  \module At(n: Types.Nat) {
    \definition Carrier: \Set := A;
  }
  \definition Carrier[n: Types.Nat]: \Set := At[n := n].Carrier;
  \definition family: Types.Family := Types.Family { Carrier := Carrier };
  \definition group: Types.FamilyGroup := Types.FamilyGroup { family := family };
  \import Types.Extend[C := group] \as Extended;
  \definition extended: Types.FamilyGroup := Extended.group;
}
\module Use(A, B: \Set) {
  \import \parent.Families[] \as Types;
  \import \parent.Make[A := A] \as Source;
  \import \parent.Make[A := B] \as Target;
  \import Types.Maps[C := Source.group, D := Target.group] \as Maps;
  \import Types.Maps[C := Source.extended, D := Target.extended] \as Result;
  \definition direct[f: A -> B]: Maps.Map := \fun (n: Types.Nat) => f;
  \definition copied[f: A -> B]: Result.Map := Maps.Child[f := direct f].copy;
}
```
