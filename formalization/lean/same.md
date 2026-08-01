# Equivalence of the original and proof-oriented systems

## 1. Purpose and status

This document specifies what it should mean for the original presentation and
a proof-oriented presentation of the theory to be the same formal system.
Neither direction of the equivalence has yet been proved in Lean.

The original presentation is authoritative.  A proof-oriented presentation
may add annotations, auxiliary judgements, redundant formation premises, and
separate inversion-friendly rules, but it must not change which unannotated
judgements are derivable.

The current split `TyExpr`/`TmExpr` implementation should be regarded as an
experiment, not yet as the final proof-oriented system.  Section 7 explains
why its equivalence with the original system cannot currently be claimed.

## 2. The original system

The original system has one raw expression grammar and one de Bruijn
namespace.  In particular, sorts, object terms, proofs, types, predicates,
type operators, and kinds are all expressions.  Their role is determined by a
derivation, not by the raw syntax.

The two principal stratified judgements are

```text
Gamma |- A :: s
Gamma |- t : A :: s.
```

The second judgement records both `t : A` and the fact that `A` has sort `s`.
The ordinary PTS judgement can be recovered by forgetting the final sort:

```text
Gamma |-PTS t : A
    iff Gamma |- A :: s and Gamma |- t : A :: s for some s,
```

with the usual special treatment when `A` itself is a sort.  Conversely, the
classification and regularity theorems should recover the final sort from a
legal PTS derivation whenever that sort exists.

The original system contains no primitive carrier judgement. In
particular,

```text
Gamma |- C <= s
```

is not part of the source theory.

## 3. Permitted proof-oriented annotations

A proof-oriented derivation may contain information that is implicit or
admissible in the original derivation.  Examples include:

- whether an occurrence is being used as an object term, a type, a
  proposition, or a kind-level expression;
- the sort of a product carrier and the sort of elements bound from that
  carrier;
- explicit formation derivations for the target of an elimination rule;
- explicit evidence that a carrier may bind type-level variables;
- explicit namespace and lifting information for de Bruijn operations.

Such data are proof annotations.  Erasing them must produce an original
derivation.  Conversely, the classification, regularity, and generation
theorems for the original system must supply enough evidence to reconstruct
some annotated derivation.

The proof-oriented system may therefore have a judgement written

```text
Gamma |- C <= s,
```

but only if it is connected to an admissible property of original
derivations.  It must not be introduced as a new assumption about `C` that
cannot be recovered from the original system.

Its semantic soundness theorem will have the form

```text
Gamma |- C <= s  implies  [[C]]rho subseteq D(s).
```

This semantic statement does not by itself establish conservativity.  A
syntactic derivation of the carrier judgement from original classification data is also
required.

## 4. Erasure

Erasure removes proof-oriented annotations while preserving raw expressions,
contexts, and conclusions.  Write

```text
eraseExpr   : AnnotatedExpr -> OriginalExpr
eraseCtx    : AnnotatedContext -> OriginalContext
eraseSeq    : AnnotatedSequent -> OriginalSequent.
```

If the annotated representation uses multiple de Bruijn namespaces, erasure
must merge their indices according to the declaration order in the context.
This makes expression erasure context-dependent.  For a type binder, the
original binder annotation is the carrier sort; the annotated element sort is
proof data used to validate occurrences of the bound variable.

The main conservativity theorem is:

> **Erasure soundness.** If `D` is an annotated derivation of `J` in `Gamma`,
> then erasing every annotation in `D` gives an original derivation of
> `eraseSeq J` in `eraseCtx Gamma`.

This theorem is proved by induction on `D`.  Every annotated rule must map to
one original rule or to an admissible sequence of original rules.  In
particular, an annotated `Gamma |- C <= s` premise must disappear through a proved
admissibility lemma; it cannot survive as an extra original hypothesis.

## 5. Elaboration

Elaboration adds classification evidence to an original derivation.  It is in
general a relation rather than a deterministic function: an expression may
have several legal annotated derivations even when all of them erase to the
same original derivation.

The main completeness theorem is:

> **Elaboration completeness.** For every original derivation `D` of `J` in
> `Gamma`, there are an annotated context `Gamma+`, an annotated sequent `J+`,
> and an annotated derivation `D+` such that `Gamma+` and `J+` erase to
> `Gamma` and `J`.

The proof must be by induction on the original derivation, simultaneously with
the following metatheorems:

```text
context regularity,
typing regularity,
sort classification,
substitution,
product generation,
classification of variable occurrences.
```

Elaboration of conversion requires special care.  Untyped beta equivalence
does not by itself provide well-formed intermediate expressions.  Either the
elaboration theorem must reconstruct a well-formed conversion path, or the
proof-oriented system must keep the original conversion rule and postpone
semantic invariance to a separate theorem.  Replacing original conversion by
a strictly smaller typed conversion relation would prove only soundness of a
subsystem, not equivalence.

## 6. Equivalence theorem

After erasure soundness and elaboration completeness, derivability equivalence
is the immediate corollary:

```text
Original.Derives Gamma J
  iff
there exist Gamma+ and J+ such that
  Annotated.Derives Gamma+ J+
  and eraseCtx Gamma+ = Gamma
  and eraseSeq J+ = J.
```

For the empty context and `falseProp`, this gives

```text
Original:  not ([] |= falseProp)
    iff
Annotated: not ([] |= falseProp+).
```

Thus a consistency proof for the annotated system transfers to the original
system only through elaboration completeness.  Erasure soundness alone gives
the opposite implication and is insufficient for this transfer.

No uniqueness of elaboration is required for consistency.  It is enough that
every original derivation has at least one elaboration.  A later coherence
theorem may show that different elaborations have equal denotations.

## 7. Problems with the current split syntax

The present `TyExpr`/`TmExpr` syntax is not yet known to satisfy elaboration
completeness.  There are several concrete obstacles.

### 7.1 Type-level lambda and application

The original grammar is a PTS grammar.  A lambda or application may occur at
the type or kind level.  For example, a type family can be applied to a type:

```text
F : Pi X : Set_i, Set_i
A : Set_i
-----------------------
F A : Set_i.
```

The current `TyExpr` has no general lambda or application constructor.
Consequently an original derivation containing a type-level application need
not have an annotated expression to elaborate to.  This alone prevents a
proof of completeness for the current grammar.

### 7.2 Roles are properties of derivations

In the original system the same raw expression can occur in different roles.
The role cannot always be selected once and for all from syntax. This remains
a problem for general PTS-level lambda, application, and variables.

Subset formation is not an example of an implicit role crossing. In the
current proof-oriented syntax,

```text
subset s A P : TmExpr
typeLift A B  : TyExpr, when B : TmExpr
pred A B t    : TyExpr, when B : TmExpr.
take X T f    : TmExpr, when X T : TyExpr and f : TmExpr.
```

The judgement `Gamma |- B : Power A :: set i` is ordinary term typing. The
set-valued term `B` becomes a type only through the explicit constructor
`typeLift A B`; there is no rule that silently reclassifies `B` as a
`TyExpr`. This agrees with the `subset` and `Ty` rules in `system.md`.

Both systems make the hidden domain and codomain of choice explicit as
`take X T f`. Erasure preserves all three arguments. This avoids requiring a
typing-derivation coherence theorem merely to determine which domain controls
the denotation of a raw `take` expression.

A context that permanently declares a variable as either `tm` or `ty` may
therefore lose original derivations in which the same declaration is used in
both roles.  Two independent de Bruijn namespaces make this loss structural,
not merely notational.

### 7.3 Type binders carry two sorts

For a type-level binder, the following are different:

```text
Gamma |- C :: carrierSort
elements of C are usable at elementSort.
```

Product size is computed from `carrierSort`, while occurrences of the bound
variable are classified using `elementSort`.  The current annotated syntax
stores only one of these and recovers the other from a derivation.  Therefore
syntax erasure is necessarily relational or derivation-indexed.

This is not itself an inconsistency, but it must be represented explicitly in
the equivalence proof.

### 7.4 Redundant premises

The proof-oriented refinement and context rules contain formation premises
that are absent from the original rules.  These premises are acceptable only
after proving that they are admissible consequences of original regularity
and generation.  Until then, the annotated rules define a potentially
strictly smaller system.

### 7.5 Conversion

The current untyped symmetric conversion relation is difficult to validate
semantically, especially for reverse `predSubset` steps.  Strengthening it in
the annotated system may be useful for a model proof, but doing so changes the
system unless every original conversion derivation can be elaborated into the
strengthened relation.

This issue must be resolved as part of equivalence, not hidden inside the
soundness proof.

## 8. Recommended proof-oriented presentation

The safest proof-oriented presentation should initially share the following
with the original system:

```text
one raw Expr grammar,
one Context grammar,
one de Bruijn namespace,
the original reduction and conversion relations.
```

It should improve proof structure at the judgement level instead:

- retain separate `HasSort`, `HasType`, and `Provable` conclusions;
- add indexed derivation predicates describing how an occurrence is being
  used;
- package carrier formation and element classification as derivation evidence;
- include redundant formation premises where the original regularity theorem
  proves them admissible;
- define inversion-friendly views or recursors over original derivations;
- use derived predicates rather than changing raw syntax whenever possible.

This design makes erasure nearly the identity and moves the difficult work to
classification lemmas, where it belongs.  It also preserves type-level lambda
and application automatically.

An intrinsically stratified four-level syntax is another possible design, but
it would require explicit embeddings between levels and substantially more
complicated substitution.  It should be attempted only after the original
classification theorem identifies the exact levels and admissible crossings.

## 9. Required proof order

Before implementing a consistency model through the proof-oriented system,
the following order should be respected.

1. Freeze the original syntax and rules.
2. Prove original context regularity and typing regularity.
3. State and prove the original classification theorem.
4. Define `IsCarrier` as an admissible, derived property.
5. Define the proof-oriented derivation annotations without restricting raw
   expressions.
6. Prove erasure soundness.
7. Prove elaboration completeness.
8. Only then use the proof-oriented system for semantic soundness and
   consistency.

The set-theoretic restriction

```text
[[E]]_s = [[E]] intersect D(s)
```

and the carrier theorem

```text
Gamma |- C <= s -> [[C]] subseteq D(s)
```

belong to semantic soundness.  They explain why the annotations are useful,
but they do not replace the syntactic equivalence proof.
