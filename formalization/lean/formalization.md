# `proof.md` の Lean 形式化

## 1. 役割

この文書は [proof.md](./proof.md) の自然言語証明を Lean へ移すための設計だけを
扱う。数学的証明の本体は `proof.md` に置き、ここでは次を記す。

- Lean 上の定義の形。
- `Prop` elimination と derivation index に関する実装上の制約。
- 必要な構文補題と theorem dependency。
- `System.Derives` の各 case と自然言語証明の対応。

証明対象は `RefType.System.Derives` の original system である。raw `BetaEq` は
維持する。sorting / typing / provability subject reduction を証明し、証明専用の
完全注釈付き導出へ elaboration して soundness の循環を切る。original system の
conversion rule 自体は変更しない。

## 2. ファイル構成

既存ファイルの責務は次の通り。

- `RefType/Sort.lean`: `USort`、`axiomTarget?`、`prodResult?`。
- `RefType/system.lean`: syntax、lift/substitution、reduction、judgement。
- `RefType/Model.lean`: `UniverseTower` と意味論。

実装量が増えたら次へ分割する。

- `RefType/Renaming.lean`: renaming/substitution algebra。
- `RefType/Confluence.lean`: parallel reduction と confluence。
- `RefType/Metatheory.lean`: regularity、generation、subject reduction。
- `RefType/Soundness.lean`: denotation、soundness、consistency。

## 3. `UniverseTower`

`proof.md` では、外部 ZFC に Grothendieck universe

```text
U_0 in U_1 in ... in U_omega in W
```

を仮定すれば以下の field が同時に実現できることも示している。対応は

```text
D (set i)       = U_i
D (setKind i)   = U_(i+1)
D prop          = {0,1}
D propKind      = U_omega
```

である。Lean では ZFC の coding を実装せず、この具体モデルから取り出した law を
structure にする。従って `UniverseTower` は soundness を field に持たず、単に
互いの整合性が不明な公理を集めたものでもない。

### 3.1 基本 field

現在の `Model.lean` の core に次を追加する。

```lean
structure UniverseTower where
  Val : Type u
  El : Val → Val → Prop
  D : USort → Val → Prop
  sortVal : USort → Val

  sortAxiom_mem :
    ∀ {s t}, axiomTarget? s = some t → D t (sortVal s)
  sort_el : ∀ s a, El a (sortVal s) ↔ D s a
```

実際の field では implicit arguments を使ってよいが、proof.md と対応する名前は
維持する。

### 3.2 proposition

```lean
propTrue : Val
propFalse : Val
proofVal : Val
propTrue_mem : D .prop propTrue
propFalse_mem : D .prop propFalse
propTrue_ne_false : propTrue ≠ propFalse
prop_cases : ∀ {p}, D .prop p → p = propTrue ∨ p = propFalse
proof_mem_iff : ∀ {p v}, D .prop p →
  (El v p ↔ v = proofVal ∧ p = propTrue)

truthVal : Prop → Val
truthVal_mem : ∀ Q, D .prop (truthVal Q)
truthVal_true_iff : ∀ Q, truthVal Q = propTrue ↔ Q
```

`truthVal` が `Prop` を引数に取るため、これは computable model ではなく
classical semantic structure である。consistency theorem も `UniverseTower` を
引数に取る相対定理なので問題ない。

### 3.3 product

```lean
appVal : Val → Val → Val
piVal : USort → USort → Val → (Val → Val) → Val
lamVal : USort → USort → Val → (Val → Val) → Val
```

必要な law は次。

```lean
pi_sort
pi_congr_on
lam_congr_on

lam_data_intro
pi_data_elim
app_lam_data

pi_prop_true_iff
```

`pi_congr_on` と `lam_congr_on` は family の全域 equality ではなく

```text
forall x, El x A -> B x = B' x
```

を受け取る。relation から選んだ family の domain 外の値は固定されないためで
ある。

`lam_data_intro`、`pi_data_elim`、`app_lam_data` には
`prodResult? binderSort bodySort = some resultSort` と
`resultSort != prop` を前提として持たせる。`pi_prop_true_iff` は
`resultSort = prop` の場合に使う。

以下の sort inversion lemma を `Sort.lean` に置く。

```lean
prodResult_prop_body :
  prodResult? r q = some .prop -> q = .prop

prodResult_nonprop : ...
```

### 3.4 set 演算

```lean
powerVal : Val → Val
subsetVal : Val → (Val → Val) → Val
predVal : Val → Val → Val → Val
typeLiftVal : Val → Val → Val
eqVal : Val → Val → Val
existsVal : Val → Val
takeVal : Val → Val → Val → Val
```

必要な law は proof.md の名前に対応させる。

```text
power_sort, power_el
subset_mem_power, subset_el, subset_congr_on
pred_mem, pred_true_iff
typeLift_sort, typeLift_el, typeLift_subset
eq_mem, eq_true_iff
exists_mem, exists_true_iff
take_set_mem, take_set_eq
```

`predVal A B t` は `truthVal (El t B)` と定義してもよい。`typeLiftVal A B` は
`B` と定義してよい。定義で済むものを冗長な field にしない。

## 4. syntax infrastructure

### 4.1 renaming

現在の `Expr.liftFrom` だけで substitution proof を進めると、binder ごとの index
計算が重複する。一般の renaming を追加する。

```lean
def Expr.rename (xi : Nat -> Nat) : Expr -> Expr
def Renaming.lift (xi : Nat -> Nat) : Nat -> Nat
```

必要な補題:

```text
rename_id
rename_comp
rename_lift
liftFrom_eq_rename
rename_subst
```

variable の sort annotation は renaming で保存する。

### 4.2 substitution

可能なら simultaneous substitution も定義する。

```lean
def Expr.substitute (sigma : Nat -> Expr) : Expr -> Expr
def Substitution.lift (sigma : Nat -> Expr) : Nat -> Expr
```

既存の `Expr.subst 0 u` との対応を証明する。必要な補題:

```text
substitute_id
substitute_comp
rename_as_substitute
lift_substitute
subst_zero_under_binder
```

### 4.3 derivation transport

proof.md 3.1 に対応して次を三判断について証明する。

```lean
sort_rename
type_rename
provable_rename

sort_subst
type_subst
provable_subst
```

`sortWeak` / `typeWeak` / `propWeak` は一般 renaming theorem の系にする。

## 5. confluence

### 5.1 closure

```lean
abbrev ReducesStar := Relation.ReflTransGen Reduces
```

`BetaEq` と `Relation.EqvGen Reduces` の対応を証明するか、現在の constructors に
対して直接 joinability を証明する。

### 5.2 parallel reduction

`Parallel : Expr -> Expr -> Prop` を定義する。各 constructor の congruence rule、
ordinary beta rule、`predSubset` rule を持つ。

`predSubset` には次の二形を用意すると complete development proof が簡単になる。

```text
pred A (subset s B P) t
  =>par app (lam s B' P') t'

pred A (subset s B P) t
  =>par P'[t']
```

ここで `A=>par A'`, `B=>par B'`, `P=>par P'`, `t=>par t'`。第二規則は
`predSubset` と直後の beta を同時に縮約する。

必要な補題:

```text
parallel_refl
reduces_parallel
parallel_reducesStar
parallel_subst
```

### 5.3 complete development

`complete : Expr -> Expr` を構造再帰で定義する。redex case を先に match する。

```text
complete (app (lam s A body) arg) =
  (complete body)[complete arg]

complete (pred A (subset s B P) t) =
  (complete P)[complete t]
```

必要な主補題:

```lean
theorem parallel_complete : Parallel M N -> Parallel N (complete M)
```

これから diamond、confluence、joinability を得る。

```text
parallel_diamond
reducesStar_confluent
betaEq_joinable
```

## 6. regularity と generation

### 6.1 regularity

```text
wf_of_sort
wf_of_type
wf_of_provable
typing_regular_type
provable_regular
sort_unique
term_sort_unique
```

一般の type uniqueness

```text
HasType Gamma e A s -> HasType Gamma e B t -> A ≃beta B
```

は証明目標に入れない。`typeLiftIntro` が反例を与える。具体的には

```text
Gamma |- t : A :: set i
Gamma |- B : power A :: set i
Gamma |= pred A B t
```

から同じ `t` に `A` と `typeLift A B` の二型が付き、両者の outer constructor は
異なるため一般には beta-convertible でない。

反例を Lean で具体化する場合、context variable `A :: set i` と `t : A` を置き、
`B := subset A (equal x x)` とする。`equalRefl`、`proveTerm`、`predSubset` と beta の
`BetaEq.trans`、`typeConv`、`provableIntro` で `pred A B t` を証明し、
`typeLiftIntro` を適用する。`head_var_ne_typeLift` という head discrimination
で `A` と `typeLift A B` が convert しない instance を示す。

### 6.2 head discrimination

confluence から次を示す。

```text
power_beta_injective
prod_beta_injective
head_power_ne_typeLift
head_power_ne_sort
head_prod_ne_other
head_var_ne_typeLift
```

`Reduces` の root rule が存在するのは `app/lam` beta と `pred/subset` だけなので、
`power`、`prod`、`typeLift`、`sort` の forward reduct は head を保存する。

### 6.3 canonical generation

typing derivation の arbitrary final type を扱うため、まず強い generation result を
定義する。例えば subset では、canonical typing を保持する structure を使う。

```lean
structure SubsetOrigin (Gamma) (i) (B P T) : Prop where
  baseSort : HasSort Gamma B (.set i)
  predSort : HasSort ({ sort := .set i, ty := B } :: Gamma) P .prop
  origin : HasType Gamma (.subset (.set i) B P) (.power B) (.set i)
  -- final derivation is obtained from origin by weakening/conversion/subtype detours
```

実際には「detour」の relation を明示するか、typing derivation induction の結果を
existential で返す。

最終的に必要な theorem:

```text
subset_power_generation :
  HasType Gamma (.subset (.set i) B P) (.power A) (.set i) ->
  HasSort Gamma B (.set i) /\
  HasSort ({ sort := .set i, ty := B } :: Gamma) P .prop /\
  BetaEq A B

beta_redex_generation
take_set_generation
```

`typeConv` case は `power_beta_injective`、`typeLiftIntro` case は
`head_power_ne_typeLift`、`typeLiftWeak` case はその base typing premiseへ再帰する。

### 6.4 subject reduction

consistency に必要なのは少なくとも次。

```lean
sort_subject_reduction :
  HasSort Gamma A s -> Reduces A A' -> HasSort Gamma A' s
```

証明では typing 側の補助 theorem も同時に必要になる。

```text
type_subject_reduction_term
type_subject_reduction_type
```

`predSubset` case は `subset_power_generation` から `BetaEq A B` を得て、argument の
typing を `B` へ convert し、target application の formation を構成する。

## 7. derivation-indexed denotation

### 7.1 raw `interp` を作らない

次のような定義は使わない。

```lean
def interp : Expr -> Valuation M -> M.Val
```

`.lam`、`.app`、`.take` は同じ syntax が proof と data の両方に使われ、結果 sort
が syntax に記録されていないからである。

### 7.2 relation

元の `Derives` は `Prop` に住むため、derivation を match して `Val : Type` を返す
ことはできない。8.2節で定義する `DerivesPlus : Context -> Sequent -> Type` を index
にした Prop-valued relation を定義する。

```lean
SortDenotes
    (h : DerivesPlus Gamma (.hasSort A s))
    (rho : Valuation M) (a : M.Val) : Prop

TypeDenotes
    (h : DerivesPlus Gamma (.hasType e A s)) (rho : Valuation M)
    (a v : M.Val) : Prop

ProvDenotes
    (h : DerivesPlus Gamma (.provable P))
    (rho : Valuation M) (p : M.Val) : Prop
```

`TypeDenotes` は型値 `a` と項値 `v` を両方記録する。`typeConv` と regularity
coherence に必要である。各 typing node の regularity field を `hA` とすると、
`TypeDenotes h rho a v` は `SortDenotes hA rho a` を必ず含む。
provability node の regularity field を `hP` とすると

```text
ProvDenotes h rho p := SortDenotes hP rho p
```

とする。各 provability constructor の soundness は、この `p` が `propTrue` で
あることを示す。

主要 clause:

- `sortAxiom`: `sortVal s`。
- weakening: premise の値を tail valuation で使う。
- `var`: lookup された型値と `rho i`。
- `typeElem`: 型値 `sortVal s`、項値は premise の sort 値。
- `typeSort`: premise `TypeDenotes` の項値を sort 値とする。
- `prodForm`: `piVal binderSort bodySort A B`。
- `lamIntro`: result sort が prop なら `proofVal`、それ以外は `lamVal`。
- `appElim`: fiber sort が prop なら `proofVal`、それ以外は `appVal`。
- `proveTerm`, `takeProp`: `proofVal`。
- `takeSet`: `takeVal`。
- `typeConv`: premise の項値を保ち、target 型値を記録する。

### 7.3 family

product/lambda clause は `F : Val -> Val` の存在を量化し、domain 上でのみ body
denotation と一致させる。

```text
forall x, El x A -> SortDenotes bodyDeriv (x :: rho) (F x)
```

existence theoremから `Classical.choose` で family を作ってもよい。この choice は
object theory の `take` や global choice とは無関係である。

### 7.4 `ValidCtx`

```lean
ValidCtx (hGamma : DerivesPlus Gamma .wf) (rho : Valuation M) : Prop
```

constructor:

```text
nil
cons:
  ValidCtx hGamma rho ->
  SortDenotes hA rho a ->
  El v a ->
  (s = prop -> v = proofVal) ->
  ValidCtx (wfExtend hGamma hA) (v :: rho)
```

補題:

```text
valid_tail
valid_head
valid_cons
lookup_sound
```

### 7.5 denotation theorem

```text
sort_denotation_exists_unique
type_denotation_exists_unique
prov_denotation_exists_unique
proof_denotation_canonical
type_denotes_regular
prov_denotes_regular
semantic_rename
semantic_subst
```

`DerivesPlus` は `Type` に住むため proof irrelevance では同一視しない。同じ
judgement の二つの elaboration が同じ値を表すことを、8.2節の depth に関する
coherence theorem で示す。`TypeDenotes` と `SortDenotes`、`ProvDenotes` と
`SortDenotes` の regularity coherence も同じ bundled theorem に含める。

存在と一意性の後、表示用にだけ noncomputable function を定義してよい。

```lean
sortInterp typeInterp termInterp propInterp
```

## 8. conversion と soundness の依存

### 8.1 semantic reduction

proof.md 6節に対応して、注釈付き導出について次を bundled theorem の一部として
証明する。

```text
sort_step_sound
type_term_step_sound
typed_path_sound
```

`sort_step_sound` の top-level term は型または proposition object であり、sort が
prop でも proof term ではない。ordinary beta は graph application で処理する。
`type_term_step_sound` は typing sort が prop なら両辺を `proofVal` に潰す。

元の体系についての `betaEq_sort_sound` が別途必要なら、elaboration、
`typed_path_sound`、coherence から系として得る。これを fundamental theorem より
先に証明済みの補題として使ってはいけない。

### 8.2 循環の処理

`sort_step_sound` の beta case は generated subterm の typing soundness を使い、
typing soundness の `typeConv` case は `betaEq_sort_sound` を使う。別々の theorem を
単純な順番で証明すると循環する。

この循環は proof.md 4節の注釈付き presentation で切る。注釈付き証明木は高さを
取り出すため `Prop` ではなく `Type` に置く。

```text
DerivesPlus : Context -> Sequent -> Type
TypedPath : Context -> USort -> Expr -> Expr -> Type
TypedJoin : Context -> USort -> Expr -> Expr -> Type
```

`DerivesPlus` は元の constructor を複製するが、`typeConv` は raw `BetaEq` の代わり
に `TypedJoin Gamma s A B` を持つ。`TypedPath` の各 step は `Reduces` と両端の
`DerivesPlus Gamma (.hasSort _ s)` を持つ。`TypedJoin` は共通 reduct `C` と
`A ->* C`, `B ->* C` に対応する二本の `TypedPath` を持つ。

加えて WF 以外の各 node は文脈の `DerivesPlus Gamma .wf` を保持する。
`hasType e A s` node は
`DerivesPlus Gamma (.hasSort A s)`、`provable P` node は
`DerivesPlus Gamma (.hasSort P .prop)` を regularity field として保持する。
regularity theorem で後から作った導出は元の node より深くなり得るため、意味論が
参照する formation evidence を最初から strict subobject にする。

これらは相互 inductive にするか、path node が endpoint の `DerivesPlus` を明示的に
保持する strictly-positive な構造として定義する。各型に全 subobject を数える

```lean
depthDerives : DerivesPlus Gamma J -> Nat
depthPath : TypedPath Gamma s A B -> Nat
depthJoin : TypedJoin Gamma s A B -> Nat
```

を定義する。元の導出からは Type-valued witness を直接返さず、Prop-valued な
existence を示す。

```text
Derives Gamma J -> Nonempty (DerivesPlus Gamma J)
DerivesPlus Gamma J -> Derives Gamma J
```

elaboration の `typeConv` case は `betaEq_joinable`、annotated regularity、annotated
subject reduction で typed join を構成する。recursive call は元の constructor の
真の premise だけに行い、path の後続 node は annotated subject reduction で作る。
各 node の WF / regularity field も、既に elaboration 済みの premise に annotated
regularity と canonical generation を適用して作り、元の regularity proof を別途
elaborate しない。
`Nonempty` から witness を取り出す箇所では `Classical.choice` を使ってよい。これは
Lean meta-level の proof object の選択であり、object theory の `take` や集合モデル
の global choice ではない。

soundness は次の五主張を、関係する `depth` の最大値に関する強い帰納法でまとめて
証明する。

```text
denotation_exists
fundamental
step_invariant
path_invariant
denotation_coherent
term_denotation_coherent
type_regular_coherent
prov_regular_coherent
```

`DerivesPlus.typeConv` 内の path、共通終点の二導出、source/target premise、各 node
の WF / regularity field はすべて node より depth が小さい。従って type
conversion の fundamental case は低い `path_invariant` と
`denotation_coherent` だけを使い、`equalElim` なども低い regularity sorting を
参照できる。高さ `n` ごとに existence と fundamental、step/path invariance、
coherence の順で証明すれば、同じ高さの provability coherence は双方が
`propTrue` であることから処理できる。

これは証明用 presentation の変更であり、original system の規則を typed
conversion へ強めるものではない。erase と elaboration により元の体系と導出可能性が
一致する。

### 8.3 soundness statement

```lean
sort_sound :
  (h : DerivesPlus Gamma (.hasSort A s)) -> ValidCtx ... rho ->
  exists! a, SortDenotes h rho a /\ M.D s a

type_sound :
  (h : DerivesPlus Gamma (.hasType e A s)) -> ValidCtx ... rho ->
  exists! av, TypeDenotes h rho av.1 av.2 /\
    M.D s av.1 /\ M.El av.2 av.1

provable_sound :
  (h : DerivesPlus Gamma (.provable P)) -> ValidCtx ... rho ->
  exists! p, ProvDenotes h rho p /\
    M.D .prop p /\ p = M.propTrue
```

元の `HasSort` / `HasType` / `Provable` に対する theorem は elaboration の
`Nonempty` から witness を取り、上の theorem を適用して得る。別の elaboration を
選んだ場合の値の一致は `denotation_coherent` を使う。

## 9. 各 constructor の対応

proof.md 6節との対応は次の通り。

| constructor | 主に使う補題または field |
| --- | --- |
| `wfEmpty`, `wfExtend` | `ValidCtx.nil/cons` |
| `sortAxiom` | `sortAxiom_mem` |
| weakening 3種 | `semantic_rename`, `valid_tail` |
| `var` | `lookup_sound` |
| `typeElem`, `typeSort` | `sort_el` |
| `prodForm` | `pi_sort`, `valid_cons` |
| `lamIntro` | `lam_data_intro` または `pi_prop_true_iff` |
| `appElim` | `pi_data_elim` または `pi_prop_true_iff`, `semantic_subst` |
| `typeConv` | `path_invariant`, `denotation_coherent` |
| `provableIntro`, `proveTerm` | `proof_mem_iff` |
| `powerForm`, `subsetForm` | `power_sort`, `subset_mem_power` |
| `predForm` | `pred_mem` |
| `typeLiftForm/Intro/Weak` | `typeLift_sort/el/subset` |
| `subsetProp` | `typeLift_el`, `pred_true_iff` |
| `equalForm/Refl/Elim` | `eq_mem`, `eq_true_iff` |
| `existsForm/Intro` | `exists_mem`, `exists_true_iff` |
| `takeSet` | `take_set_mem`, product truth elimination |
| `takeProp` | `pi_prop_true_iff`, `exists_true_iff`, `proof_mem_iff` |
| `takeEq` | `take_set_generation`, `take_set_eq`, `eq_true_iff` |

## 10. 最終定理

### 10.1 `falseProp`

既存の theorem を使用する。

```lean
System.falsePropFormed : HasSort [] falseProp .prop
```

次を追加する。

```lean
falseProp_denotes_false :
  (h : DerivesPlus [] (.hasSort falseProp .prop)) ->
  SortDenotes h emptyValuation M.propFalse
```

標準導出を elaboration した witness について `pi_prop_true_iff`、`sort_el`、
`propFalse_mem`、`prop_cases` を使って計算し、任意の `h` へ
`denotation_coherent` で移す。

### 10.2 consistency

```lean
theorem consistency (M : UniverseTower) :
    ¬ Provable [] falseProp
```

`provable_sound` で得た値と `falsePropFormed` の値を比較するため、
`prov_denotes_regular` と denotation uniqueness を必ず使う。単一 raw `interp` の
rewrite で済ませない。

```lean
theorem no_false_term (M : UniverseTower) :
    ¬ ∃ t s, HasType [] t falseProp s
```

`typing_regular_type` と `sort_unique` で `s=.prop` を得る。
`type_denotes_regular`、`falseProp_denotes_false`、`proof_mem_iff` から矛盾を出す。

## 11. 実装順

1. renaming/substitution infrastructure。
2. parallel reduction、complete development、confluence、joinability。
3. regularity、sort uniqueness、head discrimination。
4. subset/beta/take generation。
5. sorting / typing / provability subject reduction の同時証明。
6. `DerivesPlus`, `TypedPath`, `TypedJoin`, depth、erase/elaboration。
7. annotated regularity と annotated subject reduction。
8. `UniverseTower` の全 field。
9. denotation relations と `ValidCtx`、semantic renaming/substitution。
10. denotation existence、fundamental theorem、step/path invariance、coherence の
    depth に関する強い帰納法。
11. 元の体系の soundness。
12. `falseProp_denotes_false`、`consistency`、`no_false_term`。

各段階で theorem statement を先に置き、後続段階が未証明 theorem やモデル field
として soundness 全体を仮定しないことを確認する。
