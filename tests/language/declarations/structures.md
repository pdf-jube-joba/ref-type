# Structures and record fields

## Callback product

A callback product taking a proof and returning a signature does not satisfy the permitted sort relation.

```toml case
id = "callback-product"
scope = "module"
expect = "reject"
name = "Callback"
```

```ref
\structure Relation := { A: \Set, R: A -> A -> \Prop, };
\definition bad[f: \forall(P: \Prop)(h: P) -> Relation]: \Prop := \forall(P: \Prop) -> P -> P;
```

## Coherence

The structure's coherence proof does not establish the required equality.

```toml case
id = "coherence"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module BundleSignatures {
\structure Correspondence := {
  T: \VType,
  program: T,
  specification: T^,
  coherence: program^ = specification,
};


}
\module Coherence {
  \import \root.BundleSignatures[] \as Signatures;
  \inductive Bit: \VType := | zero: Bit | one: Bit;
  \definition different: Signatures.Correspondence := Signatures.Correspondence {
    T := Bit, program := Bit::zero, specification := Bit^::one, coherence := \refl(Bit^::zero),
  };
}
```

## Default override

Overriding copy with a value different from a prevents the default same from proving copy = a.

```toml case
id = "default-override"
scope = "module"
expect = "reject"
name = "Override"
```

```ref
\inductive Bool: \Set := | no: Bool | yes: Bool;
\structure Value := { a: Bool, copy: Bool := a, same: copy = a := \refl(a), };
\definition bad: Value := Value { a := Bool::no, copy := Bool::yes, };
```

## Duplicate field

The same field name occurs twice.

```toml case
id = "duplicate-field"
scope = "module"
expect = "reject"
name = "Duplicate"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\structure Duplicate: \Set := { value: Unit, value: Unit::unit = Unit::unit };
```

## Structure law

A structure law does not prove the required proposition.

```toml case
id = "structure-law"
scope = "module"
expect = "reject"
name = "Law"
```

```ref
\inductive Bit: \Set := | zero: Bit | one: Bit;
 \structure Zero: \Set := { value: Bit, isZero: value = Bit::zero };
 \definition invalid: Zero :=
   Zero { value := Bit::one,
isZero := \refl(Bit::one) };
```

## Field classification

Values and proofs can be classified according to field types and sorts.

```toml case
id = "field-classification"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module FieldClassification(A: \Set, a: A, P: \Prop, p: P) {
  \definition Reflexive[B: \Set, x: B]: \Prop := x = x;
  \structure Mixed: \Set := {
    first: A,
    evidence: P,
    second: A,
    same: Reflexive[A, first],
  };
  \definition mixed: Mixed := Mixed {
    second := a,
    same := \refl(a),
    evidence := p,
    first := a,
  };
  \definition evidence[s: Mixed]: P := s.evidence;
  \definition first[s: Mixed]: A := s.first;
  \definition law[s: Mixed]: Reflexive[A, s.first] := s.same;

  \structure OnlyProof: \Set := { evidence: P, };
  \definition onlyProof: OnlyProof := OnlyProof { evidence := p, };
  \definition extract[s: OnlyProof]: P := s.evidence;

  \structure Plain: \Set := { value: A, };
  \definition plain: Plain := Plain { value := a, };
  \definition viaProjection[s: Plain]: A := Plain::value s;
  \definition identity[s: Plain]: Plain := s;
}

\module StructureSource(A: \Set) {
  \structure Plain: \Set := { value: A, };
  \structure Checked: \Set := { value: A, same: value = value, };
}

\module StructureImports {
  \inductive Unit: \Set := | unit: Unit;
  \import \root.StructureSource[A := Unit] \as First;
  \import \root.StructureSource[A := Unit] \as Second;
  \definition checked: First.Checked := First.Checked {
    value := Unit::unit,
    same := \refl(Unit::unit),
  };
  \definition plain: First.Plain := First.Plain { value := Unit::unit, };
  \definition shared[p: First.Plain]: Second.Plain := p;
  \definition projected: plain.value = Unit::unit := \refl(Unit::unit);
}
```

## Law dependency

A later law can use a preceding law's proof.

```toml case
id = "law-dependency"
scope = "module"
expect = "accept"
name = "Dependency"
parameters = '''A: \Set, a: A'''
```

```ref
\structure Witness: \Set := { value: A,
   same: value = value,
   witness: value = (\into[A](value, { x: A \where x = x }) \by { same }),
 };
 \definition w: Witness :=
   Witness { value := a,
same := \refl(a), witness := \refl(a) };
 \definition get[s: Witness]: s.value = s.value := s.witness;
 \check get w: a = a;
```

## Structure fields

Dependent structure fields and projection types agree.

```toml case
id = "structure-fields"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module StructureFieldNames {
  \inductive Unit: \Set := | unit: Unit;
  \structure A := {
    Raw: \Set,
    Law: \Set,
    Set: \Set,
    raw: Raw,
    law: Law,
    Predicate: Set,
  };
  \definition a: A := A {
    Raw := Unit, Law := Unit, Set := Unit,
    raw := Unit::unit, law := Unit::unit, Predicate := Unit::unit,
  };
  \definition selected: \Set := a.Raw;
  \definition field: a.Set := a.Predicate;
  \definition copy[s: A]: A := A {
    Raw := s.Raw, Law := s.Law, Set := s.Set,
    raw := s.raw, law := s.law, Predicate := s.Predicate,
  };
  \check (copy a).raw: Unit;

  \structure Sorted: \Set := {
    Raw: Unit, Law: Unit, Set: Unit, raw: Unit, Predicate: Unit,
    law: raw = Raw,
  };
  \definition sorted: Sorted := Sorted {
    Raw := Unit::unit, Law := Unit::unit, Set := Unit::unit,
    raw := Unit::unit, Predicate := Unit::unit, law := \refl(Unit::unit),
  };
  \check sorted.law: sorted.raw = sorted.Raw;
  \definition computes: sorted.Set = Unit::unit := \refl(Unit::unit);

  \structure Data: \Set := { value: Unit, };
  \structure Laws[d: Data]: \Prop := { same: d.value = d.value, };
  \definition Refined: \Set := \Cast[Data] ({ d: Data \where Laws[d] });
  \definition refined: Refined := Refined {
    value := Unit::unit, same := \refl(Unit::unit),
  };
  \check refined.same: refined.value = refined.value;
  \definition alias: \Set := Refined;
  \definition viaAlias: alias := alias { value := Unit::unit, same := \refl(Unit::unit), };
  \check viaAlias.same: viaAlias.value = viaAlias.value;
}

\module ImportedStructureFields {
  \import \root.StructureFieldNames[] \as S;
  \definition value: S.Unit := S.sorted.Set;
  \check S.a.Raw: \Set;
  \check S.refined.same: S.refined.value = S.refined.value;
}
```

## Dependent record fields and laws

A value satisfying the structure's fields and laws can be constructed.

```toml case
id = "dependent-records-with-laws"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Structures {
  \inductive Unit: \Set := | unit: Unit;
  \structure EqualPair[A: \Set]: \Set := {
    first: A,
    second: A,
    same: first = second,
  };
  \definition pair: EqualPair[Unit] :=
    EqualPair[Unit] { second := Unit::unit, first := Unit::unit,
 same := \refl(Unit::unit) };
  \definition law[p: EqualPair[Unit]]: p.first = p.second := p.same;
  \definition get[p: EqualPair[Unit]]: Unit := p.first;
  \definition compute: get pair = Unit::unit := \refl(Unit::unit);
  \definition repack[p: EqualPair[Unit]]: EqualPair[Unit] :=
    EqualPair[Unit] { first := p.first, second := p.second,
 same := p.same };

  \structure Dependent[A: \Set, Family: A -> \Set]: \Set := {
    index: A,
    item: Family index,
    stable: index = index,
  };
  \definition family[x: Unit]: \Set := Unit;
  \definition dependent: Dependent[Unit, family] :=
    Dependent[Unit, family] { index := Unit::unit, item := Unit::unit,
 stable := \refl(Unit::unit) };
  \definition extract[p: Dependent[Unit, family]]: family (p.index) := p.item;
  \definition dependentComputes: extract dependent = Unit::unit := \refl(Unit::unit);
  \structure Empty: \Set := {};
  \definition empty: Empty := Empty {
};
  \check empty: Empty;
}

\module Consumer {
  \import \root.Structures[] \as S;
  \definition p: S.EqualPair[S.Unit] := S.pair;
  \definition proof: p.first = p.second := p.same;
  \check p.same: p.first = p.second;
}
```

## Record construction, projections, and sorts

A value satisfying the structure's fields and laws can be constructed.

```toml case
id = "record-construction-and-sorts"
scope = "module"
expect = "accept"
name = "Structures"
```

```ref
\inductive Nat: \Set :=
| zero: Nat
| succ: Nat -> Nat
;

\structure Pair[A: \Set]: \Set := {
  first: A,
  second: A,
};

\definition Pair[A: \Set]::swap[p: Pair[A]]: Pair[A] := Pair[A] {
  first := Pair[A]::second p,
  second := Pair[A]::first p,
};

\definition pair: Pair[Nat] := Pair[Nat] {
  second := Nat::succ Nat::zero,
  first := Nat::zero,
};
\check Pair::first pair: Nat;
\normalize Pair[Nat]::second (Pair::swap pair);

\structure Packed: \SetKind := {
  carrier: \Set,
  value: carrier,
};
\definition packed: Packed := Packed {
  carrier := Nat,
  value := Nat::zero,
};
\check Packed::value packed: Packed::carrier packed;

\structure Conjunction[P, Q: \Prop]: \Prop := {
  left: P,
  right: Q,
};
\definition duplicate[P: \Prop][p: P]: Conjunction[P, P] :=
  Conjunction[P, P] { left := p, right := p };

\structure Theory: \PropKind := {
  proposition: \Prop,
};
```


## Type-directed projections and inferred constructors

Generic constructors, nested and alias projections, Program associated definitions, and reflection can all use the same record type.

```toml case
id = "type-directed-projections-and-inferred-constructors"
scope = "module"
expect = "accept"
name = "Records"
```

```ref
\inductive Bit: \Set :=
  | zero: Bit
| one: Bit
;
\structure Pair[A: \Set, B: \Set]: \Set := {
  first: A,
  second: B,
};
\definition pair: Pair[Bit, Bit] := Pair::# Bit::zero Bit::one;
\definition first: Bit := pair.first;
\definition swap: \forall (A, B: \Set) -> Pair[A, B] -> Pair[B, A] :=
  \fun (A, B: \Set) => \fun (pair: Pair[A, B]) =>
Pair::# pair.second pair.first;
\definition nestedFirst:
  \forall (A, B, C: \Set) -> Pair[Pair[A, B], C] -> A :=
  \fun (A, B, C: \Set) => \fun (pair: Pair[Pair[A, B], C]) =>
pair.first.first;
\definition BitPair: \Set := Pair[Bit, Bit];
\definition aliasedFirst[pair: BitPair]: Bit := pair.first;
\definition hasFirst[A: \Set][a: A]: \Prop :=
  \exists ( pair: Pair[A, A] \where pair.first = a );
\inductive Wrapped: \Set := | wrap: BitPair -> Wrapped;
\definition unwrapFirst[value: Wrapped]: Bit :=
  \match value \in Wrapped \return \fun (_: _) => Bit \with {
    | wrap pair: pair.first
  };


\inductive VBit: \VType :=
  | zero: VBit
| one: VBit
;
\definition VBit::default: VBit := VBit::zero;
\structure VPair[A: \VType]: \VType := {
  first: A,
  second: A,
};
\definition VPair[A: \VType]::getFirst[pair: VPair[A]]: \F(A) :=
  pair.first;
\definition vpair: VPair[VBit] :=
  VPair::# VBit::zero VBit::one;
\definition vfirst: \F(VBit) := vpair.first;
\definition reflectedPair: VPair^[VBit^] :=
  VPair[VBit]::#^ VBit^::zero VBit^::one;
\definition reflectedFirst: VBit^ :=
  VPair[VBit]::first^ reflectedPair;
\definition reflectedGetFirst: VBit^ :=
  VPair[VBit]::getFirst^ reflectedPair;
\definition reflectedDefault: VBit^ := VBit::default^;
```

## Proof defaults follow parameters and supplied fields

Default fields of a propositional structure can reference specialized arguments and previously specified fields.

```toml case
id = "proof-defaults-follow-parameters-and-overrides"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Defaults {
  \module Definitions(A: \Set) {
    \structure Data: \Set := { value: A };
    \structure Laws[data: Data]: \Prop := {
      required: data.value = data.value,
      copy: data.value = data.value := required,
      final: data.value = data.value := copy,
    };
    \definition Bundle: \Set :=
      \Cast[Data] ({ data: Data \where Laws[data] });
  }
  \module Use(A: \Set, a: A) {
    \import \parent.Definitions[A := A] \as D;
    \definition inferred: D.Bundle := D.Bundle {
      value := a,
      required := \refl(a),
    };
    \definition overridden: D.Bundle := D.Bundle {
      value := a,
      required := \refl(a),
      copy := \refl(a),
    };
    \definition result: a = a := overridden.final;
  }
}
```

## Proposition structure default is checked when declared

A mismatch between a declared default field's term and type is detected and rejected at declaration time rather than deferred until use.

```toml case
id = "proposition-structure-default-is-checked-when-declared"
scope = "module"
expect = "reject"
name = "InvalidDefault"
parameters = '''A: \Set, a: A'''
```

```ref
\structure Laws: \Prop := {
  invalid: a = a := a,
};
```
