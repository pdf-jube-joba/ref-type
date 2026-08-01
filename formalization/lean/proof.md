# Relative consistency proof

## 1. Status of this document

The intended final theorem is the following.

> **Relative consistency theorem.** Assume ZFC with a countable increasing
> sequence of Grothendieck universes and one Grothendieck universe above all of
> them. After the corrections in Section 2, there is no derivation of
> `[] |= falseProp`. Consequently there is no term `t` and sort `s` such that
> `[] |- t : falseProp :: s`.

This is a relative consistency result. It does not prove the consistency of
Lean, ZFC, or the universe assumptions inside themselves. A Lean theorem will
have the form

```lean
theorem consistency (M : UniverseTower) : not ([] |= falseProp) := ...
```

where `UniverseTower` packages the semantic assumptions described below.

The current files are a useful syntax prototype, but the theorem above is not
yet a theorem about the exact constructors currently in `Judgement.lean`.
Several of those constructors do not support the structural and semantic
lemmas needed by the proof. Section 2 lists the required changes explicitly.
The rest of this document gives the complete proof for the corrected rules. It
also identifies which arguments are independent of normalization and
confluence.

The notes under `doc/book/src/props` are used only as motivation. In
particular, the unproved claim that substitution is harmless is replaced here
by explicit substitution and semantic-substitution lemmas.

## 2. Corrections and remaining obligations

### 2.1 Total syntax operations

The four mutually recursive operations in `Subst.lean` must be total
definitions. They should be defined using a common size measure on `TyExpr`
and `TmExpr`, or replaced by simultaneous renaming and substitution functions.
Keeping them as `partial def` prevents the intended induction and rewriting
interface from being established cleanly.

### 2.2 Weakening must shift only the new namespace

For `k : VarKind`, define

```text
wk ty E = liftTyFrom 0 E
wk tm E = liftTmFrom 0 E.
```

The other namespace is left unchanged. In particular, adding a term variable
does not mean `liftTyFrom 1`, and adding a type variable does not mean
`liftTmFrom 1`. Those operations shift all indices greater than or equal to
one and are not identities.

The three weakening constructors must use `wk d.kind` on every expression in
their conclusions.

### 2.3 Lookup must transport declaration types

When lookup crosses a declaration, the type stored in the older declaration
is now under the new binder. It must therefore be weakened. The intended
lookup equations are

```text
lookup (d :: Gamma) d.kind 0 = wk d.kind d.ty,
lookup (d :: Gamma) k (n + 1) = wk d.kind A  if d.kind = k,
lookup (d :: Gamma) k n       = wk d.kind A  if d.kind != k,
```

where `A` is the result of the recursive lookup. One may instead make `here`
return the unshifted declaration type and shift only in the variable rule, but
exactly one consistent convention must be used. The present `thereSame` and
`thereOther` return the old `A` unchanged and therefore do not describe
dependent de Bruijn contexts.

### 2.4 Type and term declarations need different formation premises

The present `wfExtend` uses `Gamma |- d.ty :: d.sort` for both declaration
kinds. This does not validate the intended `falseProp`. Its binder has carrier
`sort prop`, whose sort is `propKind`, while the bound type variable `P` must
have sort `prop`. Consequently the current one-element context needed to derive
`P :: prop` is not well formed.

Use kind-indexed declarations, conceptually

```text
tyDecl  (carrier : TyExpr) (elemSort : USort)
tmDecl  (ty : TyExpr)      (sort : USort).
```

A term declaration requires `Gamma |- ty :: sort`. A type declaration requires
a carrier judgement

```text
Gamma |- carrier <= elemSort,
```

meaning that every semantic element of `carrier` is a type in
`D(elemSort)`. In particular, `sort s <= s`. This carrier evidence
is distinct from ordinary term typing of powerset elements in Section 2.7.

The corresponding variable rules are

```text
Gamma, X in C :: s |- X :: s,
Gamma, x : A :: s |- x : wk A :: s.
```

This distinction is essential: without it, consistency of the current code is
largely vacuous because its intended false proposition is not even known to be
a proposition.

### 2.5 Product formation must validate the binder annotation

In

```text
prod kind s A B
```

the annotation `s` describes the bound variable. For a term binder it must
equal the sort derived for `A`. For a type binder, `Gamma |- A <= s` must hold
in the sense of Section 2.4. Otherwise the context used to check `B` can
disagree with the actual elements of its domain.

### 2.6 Application must return the codomain sort

Suppose

```text
Gamma |- A :: s1
Gamma, x : A |- B :: s2
prodResult s1 s2 = s3.
```

A function of type `Pi x : A, B` has that type at sort `s3`, but its
application has type `B[a]` at sort `s2`. The present `appElim` uses the
function type's sort for both positions. It must instead conclude

```text
Gamma |- app f a : B[a] :: s2.
```

The codomain formation derivation may be an explicit premise, or may be
recovered by a regularity and product-generation theorem.

### 2.7 Formation and context conversion

The subset expression is a term, not a type expression. Its typing judgement
is the ordinary term judgement

```text
Gamma |- B : Power A :: set i.
```

Accordingly, `subset` belongs to `TmExpr`, while `typeLift A B` and `pred A B t`
belong to `TyExpr` and take `B : TmExpr`. The essential rules are:

```text
subsetForm  : Gamma |- subset A P : Power A :: set i
predForm    : Gamma |- B : Power A :: set i
              Gamma |- t : A :: set i
typeLiftForm : Gamma |- A :: set i
               Gamma |- B : Power A :: set i.
```

No rule turns `B` itself into a type. Only the explicit expression
`typeLift A B` crosses from the term-level powerset element to a type.

The `predSubset` redex should be

```text
pred A (subset A P) t -> P[t]tm.
```

The `base` in `pred` and the base stored by `subset` must be syntactically the
same in this reduction rule. Otherwise membership in the subset has an extra
base-membership condition not represented by `P[t]`.

Reduction under a lambda annotation also requires context conversion:

```text
Gamma, x : A |- J       Gamma |- A' :: s       A =typed-beta A'
----------------------------------------------------------
Gamma, x : A' |- J.
```

Without it, subject reduction for `TmReduces.lamTy` cannot be proved. Context
conversion is not needed by the direct consistency argument if reduction
under annotations is removed, but one of these two changes is required for
the subject-reduction phase of the roadmap.

### 2.8 The two binders in `takeSet`

Every apparently nondependent occurrence must still be transported through
the binders. In the function type `X -> T`, the codomain is `wk tm T`. In the
constancy proposition, the second domain is `wk tm X`, and `f` is below two
term binders. Its occurrence must therefore be shifted twice from cutoff zero.
`liftTmFrom 1 f` is not a shift by two. The proposition should contain the de
Bruijn equivalent of

```text
Pi x1 : X, Pi x2 : X, f x1 = f x2,
```

with every free occurrence from `Gamma` transported through the binders it
crosses. The function types in `takeProp` and `takeEq` need the same weakened
codomain. Without these shifts, a free term index in `X` or `T` is captured by
the newly introduced argument.

The syntax is therefore `take X T f`, with `X` and `T` explicit. The
`takeSet`, `takeProp`, and `takeEq` rules all use those same annotations. This
removes the need for a generation/coherence theorem that recovers a hidden
domain from the typing derivation.

### 2.9 Conversion requires a metatheoretic justification

`TyBetaEq` is currently the untyped symmetric-transitive closure of reduction.
This is not by itself nonstandard: PTS presentations commonly use a raw
definitional equality in conversion. Its safety then follows from regularity,
subject reduction, confluence or an equivalent well-formed-conversion theorem.
Lean likewise reconstructs typing derivations from terms and invokes
definitional equality while checking an already constrained expected type.

The nonstandard `predSubset` rule creates an additional obligation. A reverse
step can introduce
`pred A (subset A P) t` even when `t` is not an element of `A`. The two sides
do not have the same membership interpretation unless well-typedness supplies
that premise.

There are two acceptable proof strategies. One is to prove that every use of
raw conversion between well-formed endpoints can be replaced by a path of
well-formed steps, and then prove semantic invariance on that path. The other
is to use typed conversion steps directly. The latter can be presented as

```text
Gamma |- t : A :: s    Gamma |- A :: s    Gamma |- B :: s    A -> B
------------------------------------------------------------------- conv-forward
Gamma |- t : B :: s

Gamma |- t : A :: s    Gamma |- B :: s    B -> A
-------------------------------------------------- conv-backward
Gamma |- t : B :: s.
```

`sortConv` is not a rule of `system.md` and is therefore not included in either
Lean system. If sort formation is later shown to respect conversion, that
result must be added as an admissibility theorem derived from subject reduction
and well-formed conversion, not as a new primitive rule. Choosing typed term
conversion avoids semantically unjustified expansions but defines a smaller
system until equivalence with the original term-conversion rule is proved.

These corrections are proof obligations, not cosmetic improvements. Until
they are made, claiming a checked consistency proof for the current Lean
inductive would be inaccurate.

## 3. Corrected formal system

Write the judgements as

```text
WF(Gamma)
Gamma |- A :: s
Gamma |- C <= s
Gamma |- t : A :: s
Gamma |= P.
```

There are two de Bruijn namespaces. A valuation is correspondingly a pair
`rho = (rhoTy, rhoTm)`. Extending a context declaration extends exactly one of
these lists. Every binder operation is parameterized by its namespace.

The minimal new rules are:

```text
WF(Gamma)    Gamma |- C :: carrierSort    Gamma |- C <= s
---------------------------------------------------------------- wf-ty
WF(Gamma, X in C :: s)

WF(Gamma)    Gamma |- A :: s
------------------------------------ wf-tm
WF(Gamma, x : A :: s)

------------------------------ carrier-sort
Gamma |- sort s <= s

Gamma, X in C :: s |- X :: s

Gamma |- A :: set i    Gamma, x : A :: set i |- P :: prop
---------------------------------------------------------- subset
Gamma |- subset A P : Power A :: set i

Gamma |- A :: s1    Gamma |- A <= r
Gamma, X in A :: r |- B :: s2    prodResult s1 s2 = s3
----------------------------------------------------------- prod-ty
Gamma |- prod ty r A B :: s3

Gamma |- A :: r    Gamma, x : A :: r |- B :: s2
prodResult r s2 = s3
----------------------------------------------------------- prod-tm
Gamma |- prod tm r A B :: s3
```

The carrier judgement handles universe carriers such as `sort prop`, which
has sort `propKind` but has all its elements in `D(prop)`. It is used for
type-variable declarations. Powerset elements use ordinary term typing, so
subset formation is compatible with `predSubset` without a second membership
judgement.

We use `E[rho]` for simultaneous renaming, `E[sigma]` for simultaneous
substitution, and retain `E[u]tm` and `E[U]ty` for substitution at index zero.
These generalized operations make the binder proofs uniform.

## 4. De Bruijn metatheory

### Lemma 4.1: renaming identity and composition

For every type or term expression `E`,

```text
E[id] = E,
E[rho][tau] = E[tau o rho].
```

**Proof.** Use simultaneous structural induction on `TyExpr` and `TmExpr`.
Sorts and variables are immediate. Every nonbinding constructor follows by
the induction hypotheses for its children. At `prod`, extend the renaming in
the namespace selected by `kind`; the elementary equation

```text
up(tau) o up(rho) = up(tau o rho)
```

finishes the codomain. At `lam` and `subset`, use the corresponding equation
for the term namespace. The two namespaces commute because extending a type
renaming does not alter the term component and conversely. These are all
constructors. QED.

### Lemma 4.2: substitution identity and composition

For every expression `E`,

```text
E[idSub] = E,
E[sigma][tau] = E[x |-> sigma(x)[tau]].
```

The equation applies separately to each namespace and also to a pair of
substitutions.

**Proof.** Again use simultaneous structural induction. The variable case is
the definition of substitution composition. Under a binder, use

```text
up(sigma)(0) = var 0,
up(sigma)(n + 1) = wk (sigma n),
up(sigma) ; up(tau) = up(sigma ; tau).
```

The last equality follows by cases on the index. The `prod`, `lam`, and
`subset` cases then follow from their induction hypotheses. QED.

### Lemma 4.3: beta substitution equations

The following are the instances needed later:

```text
(wk tm E)[u]tm = E,
(wk ty E)[U]ty = E,
B[wk tm u]tm[v]tm = B[v, u]tm,
B[wk ty U]ty[V]ty = B[V, U]ty,
E[u]tm[U]ty = E[U]ty[u[U]ty]tm.
```

There are analogous equations with the two substitutions exchanged and with
renaming at arbitrary cutoffs.

**Proof.** Each equation is an instance of Lemma 4.2 after expanding the two
substitutions on indices. For example, the first composite maps index zero to
`u` and then removes it, while an old index `n + 1` is first shifted and then
mapped back to `n`. Equality on all indices implies equality after substitution
by Lemma 4.2. QED.

### Lemma 4.4: namespace independence

Type renaming and substitution leave term-variable indices unchanged, and
term renaming and substitution leave type-variable indices unchanged. If the
replacement in one namespace has no free variables in the other namespace,
the two operations commute literally; in general they commute with the
replacement transformed as in the last equation of Lemma 4.3.

**Proof.** Simultaneous induction. The only nontrivial cases are binders, where
the two components of `up` act on disjoint sums of indices. QED.

## 5. Structural metatheory

### Lemma 5.1: lookup weakening

If `Lookup Gamma k n A s`, then lookup in `d :: Gamma` returns
`wk d.kind A`, at index `n + 1` when `d.kind = k` and at index `n` otherwise.

**Proof.** This is exactly the corrected `thereSame` or `thereOther`
constructor. Iteration gives transport through any context prefix. QED.

### Lemma 5.2: weakening

If `D` derives one of these judgements in `Gamma` and `WF(d :: Gamma)`,
then applying `wk d.kind` to every expression in the conclusion gives the
same judgement in `d :: Gamma`.

**Proof.** Induct on `D`.

- The context cases use `wfExtend` and the induction hypothesis.
- The sort axiom is first available in the empty context and is transported by
  repeated weakening.
- Variable cases use Lemma 5.1.
- Product, lambda, application, power, subset, predicate, lift, equality, and
  existence cases rebuild the same constructor. Renaming composition under a
  binder is Lemma 4.1.
- Conversion uses the fact that renaming preserves one-step reduction. That
  fact is proved by induction on the reduction constructor, with Lemma 4.3 in
  the beta case, and then lifted to typed conversion.
- The `takeSet` constancy premise uses two lifted renamings. Lemma 4.1 moves the
  outer weakening through both binders.
- `takeProp` and `takeEq` are direct after the induction hypotheses.

Every constructor is covered. QED.

### Lemma 5.3: lookup substitution

Consider `Gamma2, d, Gamma1`, where `d.kind = k`, and a well-typed replacement
for `d` in `Gamma1`. Substitution through a lookup has three cases.

1. Looking up `d` itself returns the replacement.
2. Looking up an older variable decrements its `k`-index and substitutes in
   its transported declaration type.
3. Looking up the other namespace preserves its index and substitutes in its
   transported declaration type.

**Proof.** Induct on the lookup derivation and use Lemma 4.3 when crossing the
removed declaration. QED.

### Theorem 5.4: substitution

There are two versions, one for each namespace.

For a term declaration, assume

```text
WF(Gamma2, x(tm) : A, Gamma1)
Gamma1 |- u : A :: s.
```

If a judgement `J` is derivable in `Gamma2, x : A, Gamma1`, then `J[u]tm` is
derivable in `Gamma2[u]tm, Gamma1`. The theorem includes well-formedness,
sorting, carrier validity, typing, and provability conclusions simultaneously.

The type-namespace version cannot yet be stated from these five judgements.
Replacing `X in C :: s` by a `TyExpr U` requires both `Gamma |- U :: s` and
evidence that `[[U]]` belongs to the carrier `[[C]]`. This is not ordinary term
typing and must not be conflated with `B : Power A`. A derived,
derivation-indexed carrier-membership relation, together with its
admissibility from the original system, is still required before claiming the
full type-substitution theorem.

**Proof for the term namespace.** Induct on the derivation of `J`,
simultaneously for the five judgements.

- `wfEmpty`, `sortAxiom`, and unaffected variables are immediate.
- The substituted variable is exactly the replacement typing assumption;
  older variables use Lemma 5.3.
- `wfExtend` follows from the induction hypotheses for its context and type
  premises.
- Weakening has two subcases. If the weakened declaration is the one removed,
  Lemma 4.3 cancels the weakening. Otherwise commute substitution past the
  weakening using Lemma 4.2 and rebuild weakening.
- In `prodForm`, `lamIntro`, `subsetForm`, and the constancy proposition of
  `takeSet`, lift the replacement on entry to each binder. Lemma 4.2 identifies
  the resulting syntax with substitution in the constructor's conclusion.
- In `appElim`, apply the induction hypotheses to the function and argument.
  Lemma 4.2 gives
  `B[a]tm[u] = B[u][a[u]]tm`, so the rebuilt application has exactly the
  required type.
- Reduction is stable under substitution, by induction on one-step reduction.
  The beta case is Lemma 4.2. Therefore all conversion cases rebuild.
- `provableIntro`, `proveTerm`, power, predicate, type lift, equality, and
  existence use their induction hypotheses directly. `equalElim` additionally
  uses the same substitution-composition equation as application.
- In `takeSet`, substitute in `X`, `T`, `f`, nonemptiness, and constancy. The
  two bound variables in constancy are handled by applying `up` twice.
  `takeProp` and `takeEq` are analogous.

No case assumes normalization or confluence. QED.

### Corollary 5.5: regularity

For the corrected application rule:

```text
Gamma |- t : A :: s   implies  Gamma |- A :: s,
Gamma |= P             implies  Gamma |- P :: prop,
Gamma |- A :: s        implies  WF(Gamma).
```

**Proof.** Simultaneous induction on the derivation. Formation premises give
the desired conclusion in each introduction and elimination case. Typed
conversion has the target sorting judgement as an explicit premise.
`appElim` uses product generation followed by Theorem 5.4 for its codomain.
The `proveTerm` and `provableIntro` cases use the two simultaneous induction
hypotheses. QED.

### Lemma 5.6: generation and classification

The following inversion facts hold in the corrected system.

1. If `Gamma |- sort s :: t`, then `axiomTarget s = t`.
2. If `Gamma |- prod k r A B :: s3`, then there are unique `s1` and `s2`
   such that `Gamma |- A :: s1`, the appropriate extended context derives
   `B :: s2`, and `prodResult s1 s2 = s3`. The binder annotation satisfies
   the condition in Section 2.5.
3. A derivation typing `lambda r A b` has, after peeling weakening, typed
   conversion, and refinement wrappers, a `lamIntro` derivation with domain
   `A` and the displayed body.
4. A derivation typing `app f a` similarly has an `appElim` core, so its result
   is the substituted codomain at the codomain sort.
5. Sorting is unique: if `Gamma |- A :: s` and `Gamma |- A :: t`, then
   `s = t`.
6. Ordinary term types have a principal type up to typed conversion and the
   explicit refinement relation generated by `typeLiftIntro` and
   `typeLiftWeak`. In particular, two set-valued product types assigned to the
   same term have typed-convertible domains and codomains after refinement
   wrappers are removed.

**Proof.** Induct on the first derivation, with a subsidiary induction on the
second derivation for uniqueness.

- A sort expression can be introduced only by `sortAxiom` and transported by
  weakening, so the first claim follows from `axiomTarget?`.
- A product expression can be sorted only by `prodForm` and structural
  transport. Invert that constructor and use weakening inversion to recover
  its two premises. The induction hypotheses make `s1` and `s2` unique, and
  `prodResult?` is a partial function, so `s3` is unique.
- The only syntax-directed term constructor introducing a lambda is
  `lamIntro`, and the only one introducing an application is `appElim`.
  Structural rules are peeled by their induction hypotheses. Typed conversion
  changes only the assigned type, and refinement rules change only explicit
  intersection membership, so neither changes the head constructor.
- For sorting uniqueness, compare the possible final formation rules. Their
  result heads are disjoint (`sort`, `var`, `prod`, `power`, `pred`,
  `typeLift`, `equal`, and `exists_`). The variable case uses functional
  lookup. Equal nonvariable heads reduce the problem to their premises; the
  induction hypotheses and determinism of `axiomTarget?` and `prodResult?`
  finish each case.
- For principal term types, perform the same comparison on `tmVar`,
  `lamIntro`, `appElim`, `proveTerm`, `subsetForm`, `takeSet`, and `takeProp`. Lookup is
  functional by Lemma 5.1. Lambda annotations fix the domain, and application
  generation fixes the substituted codomain. Typed conversions compose.
  `typeLiftIntro` and `typeLiftWeak` are recorded rather than incorrectly
  identified with beta conversion. In the set-valued product case, reduction
  preserves the outer `prod` constructor, so product domain and codomain
  generation applies.

These cases exhaust the corrected rules. QED.

## 6. Reduction facts needed by consistency

### Lemma 6.1: substitution preserves reduction

If `E -> E'`, then `E[sigma] -> E'[sigma]`, for either namespace and for
simultaneous substitutions.

**Proof.** Induct on the reduction derivation. Congruence cases rebuild the
same constructor. For term beta reduction, Lemma 4.2 identifies

```text
((lambda A. b) a)[sigma]
```

with a beta redex whose reduct is `b[a][sigma]`. For `predSubset`, the same
lemma identifies substitution into `P[t]tm` with substitution into the
corresponding predicate redex. QED.

### Lemma 6.2: provability respects typed beta equivalence

If `Gamma |= P`, `Gamma |- Q :: prop`, and `P` and `Q` are related by typed
beta conversion, then `Gamma |= Q`.

**Proof.** From `Gamma |= P`, `proveTerm` gives
`Gamma |- prove P : P :: prop`. Type conversion gives that same term type `Q`,
and `provableIntro` concludes `Gamma |= Q`. QED.

### Optional theorem 6.3: one-step subject reduction

After adding context conversion or deleting `lamTy`, one has

```text
Gamma |- A :: s, A -> A'       implies Gamma |- A' :: s,
Gamma |- t : A :: s, t -> t'   implies Gamma |- t' : A :: s.
```

**Proof.** Induct on reduction.

- Term beta uses lambda and application generation plus Theorem 5.4.
- `predSubset` uses subset generation and Theorem 5.4.
- Congruence rules use the induction hypothesis and rebuild formation or
  typing. `lamTy` uses context conversion for the body.
- `prove` uses Lemma 6.2 and type conversion.
- `take` transports the typing, nonemptiness, and constancy premises; Lemma 6.2
  handles the proposition obtained by reducing `f` below the two binders.

The conversion-ending generation cases can be stated directly modulo typed
conversion. A Church-Rosser theorem is one way to prove product injectivity,
but it is not needed by the semantic consistency proof below. QED.

Subject reduction is therefore useful metatheory, but not a dependency of the
relative consistency theorem. Strong normalization is nowhere required.

## 7. Set-theoretic assumptions

Work in ZFC. Assume strongly inaccessible cardinals

```text
kappa_0 < kappa_1 < ... < kappa_Omega
```

with every `kappa_i < kappa_Omega`. Put

```text
V_i = V_(kappa_i),
W   = V_(kappa_Omega).
```

Each is a transitive Grothendieck universe. We use these consequences.

1. `V_i` is an element and a subset of `V_(i+1)`.
2. If `A` is in `V_i`, then its powerset is in `V_i`.
3. If `A` is in `V_i` and every `B(a)` is in `V_i`, then the dependent
   function set `Pi a in A, B(a)` is in `V_i`.
4. `W` contains every `V_i` and is closed under all the same operations.
5. Separation, replacement, extensionality, and choice are available.

These properties, rather than cardinal arithmetic itself, should be fields of
the Lean structure `UniverseTower`. A later construction from inaccessible
cardinals can be kept separate from syntax soundness.

Define

```text
bullet = emptyset,
0      = emptyset,
1      = {bullet},
Bool   = {0, 1}.
```

Choose the universes so that `Bool` belongs to `W`. A proposition is
interpreted by either `0` or `1`; it is true exactly when it contains `bullet`.

Interpret the sort domains by

```text
D(set i)     = V_i,
D(setKind i) = V_(i+1),
D(prop)      = Bool,
D(propKind)  = W.
```

Then the sort axioms are valid because `V_i in V_(i+1)` and `Bool in W`.

## 8. Interpretation

For a valid valuation `rho`, write `[[A]]rho` and `[[t]]rho`. Formally these
interpretations are indexed by sorting and typing derivations. Sections 9 and
10 prove that changing the derivation does not change the result relevant to
a judgement. This derivation indexing resolves proof erasure: any term whose
type has sort `prop` is interpreted as `bullet`.

### 8.1 Types

```text
[[sort s]]rho            = D(s)
[[var n]]rho             = rhoTy[n]
[[power A]]rho           = P([[A]]rho)
[[typeLift A B]]rho      = [[A]]rho intersect [[B]]rho
[[pred A B t]]rho        = 1 iff [[t]]rho in [[B]]rho, otherwise 0
[[equal a b]]rho         = 1 iff [[a]]rho = [[b]]rho, otherwise 0
[[exists_ A]]rho         = 1 iff [[A]]rho is nonempty, otherwise 0.
```

For `prod kind s A B`, put `X = [[A]]rho`. Extend the valuation in the
namespace `kind`. If the result sort is `prop`, define

```text
[[prod kind s A B]]rho = 1
    iff for every a in X, [[B]](rho,a) = 1;
```

otherwise use the dependent function set

```text
Pi a in X, [[B]](rho,a).
```

### 8.2 Terms

If the type of a term has sort `prop`, its denotation is `bullet`. Otherwise,

```text
[[var n]]rho       = rhoTm[n]
[[lambda A. b]]rho = the function a |-> [[b]](rho,a)
[[app f a]]rho     = [[f]]rho([[a]]rho).
[[subset s A P]]rho = {a in [[A]]rho | [[P]](rho,a) = 1}.
```

`[[prove P]]rho = bullet` whenever `P` is true.

For a set-valued `take X T f`, the annotations specify the domain and codomain,
and its typing derivation proves that `X` is nonempty and `f` is constant on
`X`. Choice supplies `x0 in X`; define

```text
[[take X T f]]rho = [[f]]rho(x0).
```

Constancy proves independence from the choice of `x0`. For a
proposition-valued `take X T f`, use `bullet`: a function from a nonempty `X`
into the proposition proves that proposition true.

### 8.3 Contexts

The empty valuation validates the empty context. For a term declaration, an
extended valuation is valid when the new term component belongs to
`[[d.ty]]rho`. For a type declaration `X in C :: s`, the new type component
must belong to `[[C]]rho`; carrier soundness then also puts it in `D(s)`.
The component is added to `rhoTy` or `rhoTm` according to the declaration
kind.

## 9. Semantic infrastructure

### Lemma 9.1: weakening semantics

If `rho'` extends `rho` in namespace `k`, then

```text
[[wk k E]]rho' = [[E]]rho.
```

**Proof.** Simultaneous induction on expressions. At variables this is the
definition of de Bruijn lookup in an extended list. At a binder, extend both
valuations once more and apply the induction hypothesis. All other cases are
congruences of set operations and function application. QED.

### Lemma 9.2: semantic substitution

If `rho'` is `rho` extended by a semantic value `a`, then

```text
[[E[u]tm]]rho = [[E]]rho'  when [[u]]rho = a,
[[E[U]ty]]rho = [[E]]rho'  when [[U]]rho = a.
```

The statement applies to both type and term expressions.

**Proof.** Simultaneous structural induction. Variables are the zero,
successor, and other-namespace cases of environment lookup. Under a binder,
Lemma 4.2 says that syntactic lifting is exactly extension of the semantic
substitution. Products use extensionality of dependent functions; subsets use
extensionality of sets. Predicate, equality, and existence follow by rewriting
their children. Application and lambda are the usual substitution equations.
For `take`, the interpreted functions have equal graphs by the induction
hypothesis, hence equal ranges; constancy makes the selected values equal.
QED.

### Lemma 9.3: reduction invariance

If a well-sorted redex `E` reduces in one step to `E'`, then

```text
[[E]]rho = [[E']]rho.
```

Consequently expressions related by typed beta conversion have equal
denotations.

**Proof.** Induct on reduction. Congruence cases use the induction hypothesis.
For beta,

```text
[[(lambda A. b) a]]rho
= [[b]](rho, [[a]]rho)
= [[b[a]tm]]rho
```

by Lemma 9.2. If the result is a proposition, both sides are `bullet` as terms
or the same truth value as types. For `predSubset`,

```text
[[pred A (subset A P) t]]rho = 1
iff [[t]]rho in {x in [[A]]rho | [[P]](rho,x) = 1}
iff [[P]](rho, [[t]]rho) = 1
iff [[P[t]tm]]rho = 1.
```

Well-typedness supplies `[[t]]rho in [[A]]rho`; without it the middle
equivalence would contain an extra membership conjunct. The final equality is
Lemma 9.2. Reversed typed steps use the same equality in the opposite
direction, and finite composition preserves equality. QED.

### Lemma 9.4: product closure

Every entry of `USort.prodResult?` is validated by the interpretation.

**Proof.** Check the nine possible successful cases.

- `(set i, set i, set i)` uses dependent-product closure of `V_i`.
- `(set i, setKind i, setKind i)` uses closure of `V_(i+1)` and
  `V_i subset V_(i+1)`.
- `(setKind i, setKind i, setKind i)` uses closure of `V_(i+1)`.
- `(setKind i, set i, set (i+1))` also uses closure of `V_(i+1)`.
- Every case whose result is `prop` is the truth value `0` or `1` and hence
  belongs to `Bool`.
- `(propKind, propKind, propKind)` uses closure of `W`.
- `(set i, propKind, propKind)` uses closure of `W` and `V_i subset W`.

These exhaust `prodResult?`. QED.

### Lemma 9.5: interpretation coherence

Two derivations of the same sorting judgement give the same type denotation.
Two derivations of the same term at typed-convertible types give equal term
denotations. For `take X T f`, the annotations fix the domain and codomain.

**Proof.** Induct on the syntax, using regularity and generation to identify
the last non-conversion rule. Sort and product results are deterministic after
the corrections in Sections 2.5 and 2.6. Conversion is harmless by Lemma 9.3.
Variables are fixed by the transported lookup result. Ordinary lambdas and
applications are extensional functions and application. Proof terms are all
`bullet`. For `take X T f`, every `takeSet` derivation chooses a point from the
annotated nonempty domain `X`, on which the same semantic function is constant,
so all choices yield its unique value. The proposition case is always
`bullet`. QED.

## 10. Soundness

Define semantic validity as follows.

```text
rho |= Gamma |- A :: s          iff [[A]]rho in D(s),
rho |= Gamma |- C <= s          iff [[C]]rho subseteq D(s),
rho |= Gamma |- t : A :: s      iff [[A]]rho in D(s) and [[t]]rho in [[A]]rho,
rho |= Gamma |= P               iff [[P]]rho = 1.
```

### Theorem 10.1: fundamental soundness theorem

For every derivation `D`:

1. If `D : WF(Gamma)`, then every valuation generated according to `Gamma`
   is valid.
2. If `D : Gamma |- A :: s`, every valid `rho` satisfies
   `[[A]]rho in D(s)`.
3. If `D : Gamma |- C <= s`, every valid `rho` satisfies
   `[[C]]rho subseteq D(s)`.
4. If `D : Gamma |- t : A :: s`, every valid `rho` satisfies
   `[[t]]rho in [[A]]rho` and `[[A]]rho in D(s)`.
5. If `D : Gamma |= P`, every valid `rho` satisfies `[[P]]rho = 1`.

**Proof.** Simultaneous induction on `D`. The cases are as follows.

- `wfEmpty`: the empty valuation is valid.
- `wfExtend`: for a term declaration, the sorting induction hypothesis
  interprets its type and adjoining an element gives a valid extension. For a
  type declaration, the carrier induction hypothesis puts every element of
  its carrier in the declared sort.
- `sortAxiom`: validity is `V_i in V_(i+1)` or `Bool in W`.
- The three weakening rules: apply the induction hypothesis to the restricted
  valuation and then Lemma 9.1.
- `tyVar`: validity of the context and carrier soundness put the selected
  type component in its declared sort. `tmVar` uses membership in the
  transported declaration type. Lookup transport handles both cases.
- Carrier constructors: type variables use context validity, and
  `sort s <= s` holds by equality. Closure under weakening follows from
  Lemma 9.1.
- `prodForm`: the premises interpret the domain and every fiber. Lemma 9.4
  places the truth-valued universal or dependent function set in the result
  sort.
- `lamIntro`: in a non-proposition sort, the induction hypothesis for the body
  constructs a dependent function in the interpreted product. In sort `prop`,
  every fiber is true, so the product proposition is `1` and the erased lambda
  denotes its unique proof `bullet`.
- `appElim`: in a non-proposition sort, membership of the function in the
  dependent product and membership of the argument in the domain imply that
  application lies in the selected fiber. Lemma 9.2 identifies that fiber with
  `[[B[arg]tm]]rho`. In sort `prop`, product truth and domain membership imply
  that the selected proposition is true, and the application denotes
  `bullet`.
- Typed type-conversion steps: Lemma 9.3 identifies the two type denotations;
  the induction hypotheses then give the required membership. There is no
  unrestricted `sortConv` case.
- `provableIntro`: a term in a proposition can exist only when that proposition
  is `1`.
- `proveTerm`: the premise says the proposition is `1`, whose unique element is
  `bullet`.
- `powerForm`: powerset closure puts `P([[A]]rho)` in `V_i`.
- `subsetForm`: separation produces a subset of `[[A]]rho`, hence literally an
  element of `P([[A]]rho)`. Powerset and separation closure also put it in
  `V_i`, proving the ordinary term-typing conclusion.
- `predForm`: term typing of `B` at `Power A` says
  `[[B]]rho subseteq [[A]]rho`. The predicate interpretation is by definition
  either `0` or `1`, so it is in `Bool`.
- `typeLiftForm`: separation gives
  `[[A]]rho intersect [[B]]rho` in `V_i`.
- `typeLiftIntro`: the first premise gives `[[t]]rho in [[A]]rho`; typing of
  `B` gives `[[B]]rho subseteq [[A]]rho`, and the provability premise says
  `[[t]]rho in [[B]]rho`. Hence the term belongs to the intersection.
- `typeLiftWeak`: membership in the intersection implies membership in its
  left component.
- `subsetProp`: membership in the intersection implies membership in
  `[[B]]rho`, so `pred A B t` is interpreted by `1`.
- `equalForm`: equality interpretation is a truth value.
- `equalRefl`: reflexivity makes the equality interpretation `1`.
- `equalElim`: the equality premise gives `[[a]]rho = [[b]]rho`. The premise
  for `P[a]` and Lemma 9.2 therefore give
  `[[P]](rho,[[a]]rho) = 1`. Rewriting by equality and applying Lemma 9.2 again
  gives `[[P[b]tm]]rho = 1`.
- `existsForm`: nonemptiness is a truth value.
- `existsIntro`: the interpreted element witnesses that `[[A]]rho` is
  nonempty, so `exists_ A` is `1`.
- `takeSet`: nonemptiness supplies `x0 in [[X]]rho`. Function typing gives
  `[[f]]rho(x0) in [[T]]rho`. The constancy premise says that this value is
  independent of `x0`, so it is a well-defined interpretation of
  `take X T f`.
- `takeProp`: the function type is itself a proposition, so its inhabitant is
  erased rather than interpreted as a set-theoretic function. Its truth says
  that `T` is true for every point of `[[X]]rho`. Choose `x0` using
  nonemptiness; `T` is therefore true and `bullet` is its proof.
- `takeEq`: the denotation of `take X T f` is the unique constant value of `f`
  on its annotated domain `X`. Since the term premise
  gives `[[t]]rho in [[X]]rho`, that value equals
  `[[f]]rho([[t]]rho)`, which is `[[app f t]]rho`. Thus the equality proposition
  is `1`.

This list covers every constructor of the corrected `Derives`. QED.

## 11. Consistency

Recall

```text
falseProp = prod ty prop (sort prop) (var 0).
```

It represents `Pi P : Prop, P`.

### Lemma 11.1: formation of `falseProp`

```text
[] |- falseProp :: prop.
```

**Proof.** The sort axiom gives `[] |- sort prop :: propKind`, and the
carrier rule says `[] |- sort prop <= prop`. Extend the context with
a type variable `P in sort prop :: prop`. The variable rule gives `P :: prop`,
that is, the codomain has sort `prop`. Finally

```text
prodResult propKind prop = prop,
```

so `prodForm` yields the claim. QED.

### Lemma 11.2: interpretation of `falseProp`

```text
[[falseProp]] = 0.
```

**Proof.** Its domain is `[[sort prop]] = Bool = {0,1}`. Since the product has
result sort `prop`, its interpretation is `1` exactly if every `q in Bool` is
true. Take `q = 0 = emptyset`. Then `bullet` is not in `q`, so `q` is false.
Therefore the universal proposition is `0`. QED.

### Theorem 11.3: no proof of false

```text
not ([] |= falseProp).
```

**Proof.** Suppose `D : [] |= falseProp`. Apply Theorem 10.1 to the unique
empty valuation. Soundness gives `[[falseProp]] = 1`, while Lemma 11.2 gives
`[[falseProp]] = 0`. Since `0 != 1`, this is a contradiction. QED.

### Corollary 11.4: no term inhabits false

There are no `t` and `s` such that

```text
[] |- t : falseProp :: s.
```

**Proof.** Direct soundness says `[[t]]` belongs to
`[[falseProp]] = emptyset`, which is impossible. If the displayed sort is
`prop`, the syntactic alternative is to apply `provableIntro` and contradict
Theorem 11.3. QED.

## 12. What is and is not needed

The consistency proof depends on total substitution, corrected structural
rules, semantic substitution, reduction invariance, and soundness. It does not
depend on strong normalization, canonical forms, decidability of conversion,
or confluence. No computation rule for `take` is used.

Adding a reduction rule for `take` is consistency-preserving only if every new
reduction is validated by the equation in the `takeSet` premises. For example,
reducing `take X T f` to `f t` is semantically sound when the reduction carries a
derivation of `t : X`, nonemptiness, and constancy. An unconditional rule that
chooses an arbitrary syntactic argument is not covered by this model.

The next Lean milestone should therefore be the corrections in Section 2,
followed by Lemmas 4.1--5.4. Once those compile, the model can be introduced as
an abstract `UniverseTower`, and Theorem 10.1 can be implemented as induction
on `Derives`.
