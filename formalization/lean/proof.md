# `System` の直接モデルによる無矛盾性証明

この文書では、`RefType.System.Derives` に対する自然言語での証明を書く。
目標は、この証明をそのまま Lean の定義・補題・定理へ分解できる形にする
こと。

証明対象は `formalization/lean/RefType/system.lean` の体系である。Lean 内で
first-order logic や ZFC は定義しない。集合論的 universe に相当する仮定は
`System.UniverseTower` という
Lean の `structure` にまとめ、その仮定のもとで soundness と consistency を
証明する。

## 0. 今の判断

### Subject reduction

subject reduction は、consistency の最終証明に直接は要らない。必要なのは
`typeConv` の soundness、つまり「変換可能な型は同じ意味を持つ」という補題で
ある。

ただし現在の `system.lean` の `BetaEq` は untyped な reduction から作られて
いる。そのため、`predSubset` のように well-typedness がないと意味保存が
言えない step が混ざる。さらに raw な `Reduces` については subject reduction
そのものが成り立たない。例えば

```text
pred A (subset s B P) t  ⇒β  app (lam s B P) t
```

は、左辺が `predForm` で well-sorted でも、右辺の application が typed になる
には `t : B` が必要である。左辺の well-sortedness は通常 `t : A` しか与え
ないので、raw reduction は型を保存しない。

このため、Lean では raw `BetaEq` を `typeConv` の根拠として直接使わない方が
よい。主経路は次のどちらかにする。

- typed reduction / typed conversion を別に定義し、その subject reduction と
  意味保存を証明する。
- untyped `BetaEq` を残しつつ、`typeConv` では well-typed な conversion path
  を別データとして要求する。

subject reduction は後者を作るときの補助補題として有用だが、主定理として
必要なものは reduction invariance である。

### sort-elem function

sort-elem function は、分類用の独立した関数としては要らない。導出には
`Γ |- A :: s` や `Γ |- A : sort s :: t` が明示的に入っているので、構文から
sort を推測する関数を soundness の主経路に置く必要はない。

一方で、意味論上の sort-element 対応は必要である。`typeElem` と `typeSort`
の soundness には、`sort s` の意味がちょうど `D s` の要素全体を表す、という
同値が必要になる。この文書ではそれを

```lean
sort_el : ∀ s v, El v (sortVal s) ↔ D s v
```

として `UniverseTower` の field にする。これは doc/book の古い
`sort-elem function` という分類関数ではなく、`sort s` の意味を固定する
意味論的公理である。

## 1. 最終定理

最終的に示したい定理は次の形。

```lean
theorem consistency
    (M : System.UniverseTower) :
    ¬ System.Provable [] System.falseProp := ...
```

さらに、項としての inhabitant も存在しないことを示す。

```lean
theorem no_false_term
    (M : System.UniverseTower) :
    ¬ ∃ t s, System.HasType [] t System.falseProp s := ...
```

ここで

```text
falseProp = prod propKind (sort prop) (var propKind 0)
```

であり、直観的には `forall P : Prop, P` を表す。

Lean では、`consistency` は soundness と `falseProp` の意味計算から出す。
`no_false_term` は typing soundness から直接出すか、あるいは
`provableIntro` により `Provable [] falseProp` を作って `consistency` に帰着
する。

## 2. モデルの形

自然言語の命題: `UniverseTower` は、`system.lean` の各構文と各導出規則を
解釈するために必要な意味領域、所属関係、sort の解釈、命題の真偽値、
product/powerset/subset/equality/exists/take の演算と閉包性を持つ。

モデルは 1 つの意味領域 `Val` と、sort ごとの領域述語 `D` を持つ。

```lean
structure UniverseTower where
  Val : Type u
  D : USort → Val → Prop
  sortVal : USort → Val
  ...
```

`D s v` は「値 `v` が sort `s` の意味領域に属する」という意味である。
構文 `sort s` の意味は `sortVal s` である。

ただし `sortVal s` は単なる値では足りない。`typeElem` と `typeSort` の
soundness のため、`sortVal s` は `D s` そのものを表す値でなければならない。
自然言語では次の同値を仮定する。

```text
v ∈ El(sortVal s)  iff  D s v.
```

ここで `El : Val -> Val -> Prop` は「値を集合のように見たときの所属関係」
である。Lean では、抽象 `Val` の上に直接 `∈` はないので、`UniverseTower`
に次のような field を追加する方向になる。

```lean
El : Val → Val → Prop
sort_el : ∀ s v, El v (sortVal s) ↔ D s v
```

以後、自然言語では `v ∈ a` と書くが、Lean では `M.El v a` と読む。

自然言語の命題 `sort_el`: 任意の sort `s` と意味値 `v` について、`v` が
`sort s` の意味に属することと、`v` が sort `s` の領域 `D s` に属することは
同値である。

`UniverseTower` にはさらに、soundness に必要な閉包性と演算を足す。

- `sortAxiom`: `axiomTarget? s = some t` なら `D t (sortVal s)`。
- product: dependent product の値 `piVal A F` と、その所属規則。
- application: function value を argument に適用する演算 `appVal`。
- lambda: semantic function を値として作る演算 `lamVal`。
- powerset: `powerVal A` と、subset 所属の同値。
- subset: `subsetVal A P` と、`x ∈ subsetVal A P` の同値。
- propositions: `trueVal`, `falseVal`, `D prop trueVal`, `D prop falseVal`,
  `trueVal ≠ falseVal`。
- proof irrelevance: proposition の証明項は canonical value に潰す。
- equality: `eqVal a b` は `a = b` のとき true、そうでなければ false。
- exists: `existsVal A` は `A` が非空のとき true、空のとき false。
- take: set 側では `⋃ { f x | x ∈ X }` に対応する total operation。
- reduction invariance: `e ⇒β e'` なら、well-typed な状況で `[[e]] = [[e']]`。

Lean 化では、最初から完全な集合モデルを作るのではなく、これらを
`UniverseTower` の field として必要な分だけ追加する。soundness 自体を field
にしてはいけない。soundness は `Derives` の induction で証明する対象である。

## 3. 解釈

自然言語の命題: 任意の式 `e` と valuation `rho` に対して、意味値
`[[e]]_rho` が定まる。また、文脈 `Gamma` の妥当性と判断 `J` の意味論的妥当性
は、この式解釈を用いて定義される。

valuation `rho` は文脈の各変数に値を割り当てるリストである。
de Bruijn index なので、先頭の宣言に対応する値が `rho` の先頭に来る。

式の解釈を次のように書く。

```text
[[e]]_rho : Val
```

主要な定義は次の通り。

```text
[[sort s]]_rho        = sortVal s
[[var s i]]_rho       = rho[i]
[[prod s A B]]_rho    = piVal [[A]]_rho (fun x => [[B]]_(x :: rho))
[[lam s A body]]_rho  = lamVal [[A]]_rho (fun x => [[body]]_(x :: rho))
[[app f a]]_rho       = appVal [[f]]_rho [[a]]_rho
[[prove P]]_rho       = proofVal
[[power A]]_rho       = powerVal [[A]]_rho
[[subset s A P]]_rho  = subsetVal [[A]]_rho (fun x => [[P]]_(x :: rho))
[[typeLift A B]]_rho  = subsetVal [[A]]_rho (fun x => [[pred A B x]]_rho)
[[pred A B t]]_rho    = truthVal ([[t]]_rho ∈ [[B]]_rho)
[[equal a b]]_rho     = eqVal [[a]]_rho [[b]]_rho
[[exists A]]_rho      = existsVal [[A]]_rho
[[take X T f]]_rho    = takeVal [[X]]_rho [[T]]_rho [[f]]_rho
```

`typeLift` は実装上は `pred` と同じ意味の subset として扱う。実際の Lean
定義では、`truthVal` のような meta-level proposition から `Val` への変換を
`UniverseTower` の field として与える。

文脈の妥当性は次のように定義する。

```text
Valid [] [].
Valid ({ sort := s, ty := A } :: Gamma) (v :: rho)
  iff Valid Gamma rho
      and [[A]]_rho ∈ D(s)
      and v ∈ [[A]]_rho.
```

Lean では `ValidCtx M Γ ρ : Prop` とする。lookup の soundness は
`ValidCtx` に関する基本補題になる。

自然言語の命題 `valid_tail`: `v :: rho` が拡張文脈 `d :: Gamma` を満たすなら、
tail `rho` は元の文脈 `Gamma` を満たす。

自然言語の命題 `valid_cons`: `rho` が `Gamma` を満たし、`A` が sort `s` の
意味領域に属し、`v` が `A` の解釈に属するなら、`v :: rho` は
`({sort := s, ty := A} :: Gamma)` を満たす。

判断の意味は次の通り。

```text
rho |= Gamma wf
  iff Valid Gamma rho

rho |= Gamma |- A :: s
  iff Valid Gamma rho -> D s [[A]]_rho

rho |= Gamma |- e : A :: s
  iff Valid Gamma rho -> D s [[A]]_rho and [[e]]_rho ∈ [[A]]_rho

rho |= Gamma |= P
  iff Valid Gamma rho -> [[P]]_rho = trueVal
```

Lean では `SemSeq M Γ J` を定義し、`J` の constructor で場合分けする。

## 4. 構文補題

soundness の前に、次の構文補題が必要である。

### 4.1 lookup soundness

自然言語の命題: `Lookup Gamma i A s` が成り立ち、valuation `rho` が文脈
`Gamma` を満たすなら、`rho` の `i` 番目の値は `A` の解釈に属し、さらに
`A` の解釈は sort `s` の領域に属する。

`Lookup Γ i A s` かつ `ValidCtx M Γ ρ` なら、

```text
D s [[A]]_rho
and
rho[i] ∈ [[A]]_rho.
```

ここで `Lookup` の `A` は context をまたぐたびに `liftFrom 0` される。
したがって、Lean では lift と valuation extension の対応補題が必要になる。

```lean
interp_lift :
  [[A.liftFrom 0]]_(v :: rho) = [[A]]_rho
```

この補題を使って `Lookup.here` と `Lookup.there` の induction を行う。

### 4.2 weakening の意味補題

自然言語の命題: 任意の式 `e` について、文脈の先頭に新しい値を 1 つ追加した
valuation で `e.liftFrom 0` を解釈すると、元の valuation で `e` を解釈した値と
等しい。

任意の式 `e` について、

```text
[[e.liftFrom 0]]_(v :: rho) = [[e]]_rho.
```

`sortWeak`, `typeWeak`, `propWeak` の soundness はこの補題で処理する。

Lean では `Expr.interp_liftFrom_zero` として、`Expr` の構造帰納法で証明する。

一般化した命題 `interp_liftFrom`: 任意の cutoff について、`liftFrom cutoff` の
解釈は、de Bruijn index を対応する valuation 操作でずらした解釈と一致する。
まずは `interp_liftFrom_zero` だけで進め、一般形は substitution 証明で必要に
なった時点で入れる。

### 4.3 substitution の意味補題

自然言語の命題: 任意の式 `B` と項 `u` について、`B[u]` を valuation `rho` で
解釈した値は、`B` を `[[u]]_rho :: rho` で解釈した値と等しい。

任意の式 `B` と値 `a = [[u]]_rho` について、

```text
[[B[u]]]_rho = [[B]]_(a :: rho).
```

`appElim`, beta reduction, `predSubset`, equality elimination で必要になる。

Lean ではまず `Expr.subst` と `Expr.liftFrom` の代数則を証明し、その後
interpretation との対応を証明する。

### 4.4 typed conversion

自然言語の命題: `typeConv` の soundness に必要なのは、raw `BetaEq` ではなく、
well-typed な conversion path に沿って意味が保存されることである。

Lean では、現在の raw `BetaEq` とは別に、次のような relation を導入するのが
よい。

```lean
TypedStep (Γ : Context) (s : USort) (A B : Expr) : Prop

TypedConv (Γ : Context) (s : USort) (A B : Expr) : Prop
```

これは `UniverseTower` に依存しない構文的 relation として定義する。意味保存
定理の側で `M : UniverseTower` と妥当な valuation を量化する。

`TypedStep Γ s A B` は「`Γ |- A :: s` と `Γ |- B :: s` が成り立つ one-step
reduction」と読む。constructor には raw reduction の各 constructor に対応する
ものを入れるが、危険な redex には typing premise を追加する。

欲しい補助定理は次の 4 つである。

自然言語の命題 `typedStep_subject`: `TypedStep Γ s A B` なら
`Γ |- A :: s` かつ `Γ |- B :: s` である。

自然言語の命題 `typedStep_sound`: `TypedStep Γ s A B` かつ `rho` が `Γ` を
満たすなら、`[[A]]_rho = [[B]]_rho` である。

自然言語の命題 `typedConv_subject`: `TypedConv Γ s A B` なら
`Γ |- A :: s` かつ `Γ |- B :: s` である。

自然言語の命題 `typedConv_sound`: `TypedConv Γ s A B` かつ `rho` が `Γ` を
満たすなら、`[[A]]_rho = [[B]]_rho` である。

`TypedConv` は reflexive, symmetric, transitive closure として定義する。
`typedConv_sound` は `TypedConv` の induction で証明する。refl は自明、symm は
等式の対称性、trans は等式の推移性である。したがって本質は
`typedStep_sound` である。

#### 4.4.1 beta step

自然言語の命題: typed な beta redex

```text
app (lam r A body) arg
```

は、対応する substitution 結果 `body[arg]` と同じ意味を持つ。

前提は次の形にする。

```text
Γ |- lam r A body : prod r A B :: resultSort
Γ |- arg : A :: r
Γ |- body[arg] :: bodySort
```

妥当な valuation `rho` を取る。lambda の意味より

```text
[[lam r A body]]_rho
  = lamVal [[A]]_rho (fun x => [[body]]_(x :: rho)).
```

application の意味と `Γ |- arg : A :: r` から

```text
[[app (lam r A body) arg]]_rho
  = [[body]]_([[arg]]_rho :: rho).
```

substitution の意味補題により

```text
[[body[arg]]] _rho
  = [[body]]_([[arg]]_rho :: rho).
```

したがって両辺の意味は等しい。

Lean では、この証明は `lam_app_beta` のような `UniverseTower` の計算規則と
`interp_subst_zero` だけで進む。

#### 4.4.2 pred-subset step

自然言語の命題: `t` が subset の基底型 `B` に属しているなら、

```text
pred A (subset s B P) t
```

と

```text
app (lam s B P) t
```

は同じ意味を持つ。

ここが conversion 周りで一番重要である。raw reduction は

```text
pred A (subset s B P) t  ⇒β  app (lam s B P) t
```

を無条件に許すが、これは soundness には強すぎる。typed step では少なくとも
次を前提に入れる。

```text
Γ |- B :: set i
Γ, x : B :: set i |- P :: prop
Γ |- t : B :: set i
Γ |- pred A (subset (set i) B P) t :: prop
Γ |- app (lam (set i) B P) t :: prop
```

妥当な valuation `rho` を取る。`Γ |- t : B :: set i` から
`[[t]]_rho ∈ [[B]]_rho` が得られる。subset の意味より

```text
[[t]]_rho ∈ [[subset (set i) B P]]_rho
  iff
[[t]]_rho ∈ [[B]]_rho
and [[P]]_([[t]]_rho :: rho) = trueVal.
```

左辺 `pred A (subset ... ) t` の意味は、この所属命題の truth value である。
`[[t]]_rho ∈ [[B]]_rho` が既にあるので、これは

```text
truthVal ([[P]]_([[t]]_rho :: rho) = trueVal)
```

と同じである。proposition の truth value は冪等なので、これは
`[[P]]_([[t]]_rho :: rho)` と等しい。

一方、右辺は lambda/application の計算規則により

```text
[[app (lam (set i) B P) t]]_rho
  = [[P]]_([[t]]_rho :: rho).
```

したがって両辺の意味は等しい。

この証明は `t : B` がないと失敗する。`t : A` だけでは、左辺は
「`t` が subset に属するか」を false と判定できる一方、右辺は `P[t]` を
そのまま返すため、両者が一致しない可能性がある。

#### 4.4.3 congruence steps

自然言語の命題: subexpression の typed step が意味を保存するなら、その step を
任意の constructor の中に入れても、全体の意味は保存される。

例として product domain の場合を考える。

```text
A ↦ A'
prod s A B ↦ prod s A' B
```

帰納法の仮定から `[[A]]_rho = [[A']]_rho`。product の意味は

```text
piVal [[A]]_rho (fun x => [[B]]_(x :: rho))
```

である。`piVal` が domain の等式を尊重するという `UniverseTower` の extensional
field により、全体の意味は等しい。

codomain 側では、任意の `x` について fiber の意味が等しいことを示し、
`piVal` の fiber extensionality を使う。lambda、application、power、subset、
typeLift、pred、equal、exists、take の各 congruence も同様に、対応する semantic
operation が引数の等式を尊重することを使う。

Lean では、各 operation について次のような extensionality field または lemma が
必要になる。

```text
piVal_congr
lamVal_congr
appVal_congr
powerVal_congr
subsetVal_congr
truthVal_congr
eqVal_congr
existsVal_congr
takeVal_congr
```

完全な集合モデルで `Val` を実際の集合として作るなら、これらは通常の関数の
congruence から出る。抽象 `UniverseTower` では field として持たせるのが
現実的である。

#### 4.4.4 subject reduction の位置づけ

自然言語の命題: `TypedStep Γ s A B` なら、source と target は同じ sort `s` で
well-sorted である。

これは raw `Reduces` には成り立たないが、typed step には成り立つように
constructor を設計する。多くの場合は constructor の premise に target の
formation を明示的に入れるだけでよい。beta の target `body[arg]` は
substitution lemma から formation を証明できる。`predSubset` の target
`app (lam B P) t` は `t : B` を premise に入れることで formation が出る。

この補題は conversion path の推移を扱うときに使う。つまり、各 step の target
が well-sorted であるから、次の step の source として使える。

ただし consistency 証明で直接使うのは subject reduction ではなく
`typedConv_sound` である。subject reduction は typed conversion をきれいに
定義するための補助補題である。

## 5. Soundness theorem

自然言語の命題: `System.Derives Gamma J` が導出可能なら、任意の
`UniverseTower` と任意の妥当な valuation に対して、判断 `J` の意味論的解釈は
正しい。sorting は `D s` への所属、typing は型の意味への所属、provability は
proposition の真理として解釈される。

主定理は次。

```lean
theorem soundness
    (M : System.UniverseTower)
    (h : System.Derives Γ J) :
    SemSeq M Γ J := ...
```

証明は `h` に関する induction。以下では各 constructor の場合を示す。

### 5.1 `wfEmpty`

空 valuation は空文脈を満たす。

Lean では `ValidCtx.nil` または `ValidCtx` の定義から直接出す。

### 5.2 `wfExtend`

前提は `WF Γ` と `Γ |- A :: s`。帰納法の仮定より、任意の妥当な `rho` で
`D s [[A]]_rho` が成り立つ。文脈拡張の妥当性は、さらに
`v ∈ [[A]]_rho` を満たす値 `v` を与えたときに成立する。

注意として、`WF ({sort := s, ty := A} :: Γ)` は「すべての拡張 valuation が
妥当ならよい」という形で読む。文脈の全 inhabitedness までは要求しない。

Lean では `ValidCtx.cons` の constructor と `SemSeq` の定義で処理する。

### 5.3 `sortAxiom`

`axiomTarget? s = some t` が前提。`[[sort s]] = sortVal s` なので、必要なのは
`D t (sortVal s)`。これは `UniverseTower.sortAxiom_mem` そのものである。

### 5.4 `sortWeak`

前提は `Γ |- A :: s` と `WF (d :: Γ)`。妥当な valuation `v :: rho` を取る。
tail `rho` は `Γ` に対して妥当である。帰納法の仮定で
`D s [[A]]_rho`。weakening の意味補題により
`[[A.liftFrom 0]]_(v :: rho) = [[A]]_rho`。よって結論。

### 5.5 `typeWeak`

`sortWeak` と同じ。`e` と `A` の両方に weakening の意味補題を使い、
`[[e.liftFrom 0]]_(v :: rho) ∈ [[A.liftFrom 0]]_(v :: rho)` を得る。

### 5.6 `propWeak`

`sortWeak` と同じ。`[[P.liftFrom 0]]_(v :: rho) = [[P]]_rho` を使う。

### 5.7 `var`

前提は `WF Γ` と `Lookup Γ i A s`。妥当な `rho` に対して lookup soundness を
適用すると、`D s [[A]]_rho` と `rho[i] ∈ [[A]]_rho` が得られる。
`[[var s i]]_rho = rho[i]` なので結論。

### 5.8 `typeElem`

前提は `Γ |- A :: s` と `Γ |- sort s :: t`。妥当な `rho` を取る。
帰納法の仮定から

```text
D s [[A]]_rho
D t [[sort s]]_rho
```

が得られる。`[[sort s]]_rho = sortVal s` であり、`sort_el` により
`D s [[A]]_rho` は `[[A]]_rho ∈ sortVal s` と同値。したがって
`[[A]]_rho ∈ [[sort s]]_rho`。また `D t [[sort s]]_rho` もあるので、
`Γ |- A : sort s :: t` の意味が成り立つ。

### 5.9 `typeSort`

前提は `Γ |- A : sort s :: t`。妥当な `rho` を取る。帰納法の仮定から

```text
[[A]]_rho ∈ [[sort s]]_rho
```

が得られる。`[[sort s]]_rho = sortVal s` と `sort_el` の逆向きより
`D s [[A]]_rho`。よって `Γ |- A :: s`。

### 5.10 `prodForm`

前提は

```text
Γ |- A :: binderSort
Γ, x : A :: binderSort |- B :: bodySort
prodResult? binderSort bodySort = some resultSort
```

妥当な `rho` を取る。帰納法の仮定から `D binderSort [[A]]_rho`。
さらに任意の `x ∈ [[A]]_rho` について、`x :: rho` は拡張文脈に妥当なので
`D bodySort [[B]]_(x :: rho)`。

product closure により、

```text
D resultSort (piVal [[A]]_rho (fun x => [[B]]_(x :: rho))).
```

これは `[[prod binderSort A B]]_rho` なので結論。

Lean では `UniverseTower.pi_mem` のような field を使う。

### 5.11 `lamIntro`

前提は

```text
Γ |- prod binderSort A B :: resultSort
Γ, x : A :: binderSort |- body : B :: bodySort
```

妥当な `rho` を取る。第一前提の soundness により product type 自体は
`D resultSort` に属する。第二前提より、任意の `x ∈ [[A]]_rho` について
`[[body]]_(x :: rho) ∈ [[B]]_(x :: rho)`。

lambda closure により

```text
lamVal [[A]]_rho (fun x => [[body]]_(x :: rho))
  ∈ piVal [[A]]_rho (fun x => [[B]]_(x :: rho)).
```

これは `[[lam binderSort A body]]_rho ∈ [[prod binderSort A B]]_rho`。
よって結論。

### 5.12 `appElim`

前提は

```text
Γ |- f : prod binderSort A B :: resultSort
Γ |- a : A :: binderSort
Γ |- B[a] :: bodySort
```

妥当な `rho` を取る。第一前提から `[[f]]_rho` は dependent product に属する。
第二前提から `[[a]]_rho ∈ [[A]]_rho`。product elimination の意味論より

```text
appVal [[f]]_rho [[a]]_rho ∈ [[B]]_([[a]]_rho :: rho).
```

substitution の意味補題により

```text
[[B[a]]] _rho = [[B]]_([[a]]_rho :: rho).
```

したがって `[[app f a]]_rho ∈ [[B[a]]] _rho`。第三前提から
`D bodySort [[B[a]]] _rho` も得られるので typing の意味が成り立つ。

### 5.13 `typeConv`

自然言語の補助命題 `typedConv_sound`: `TypedConv Γ s A B` が成り立つなら、
任意の妥当な valuation `rho` に対して `[[A]]_rho = [[B]]_rho` である。

前提は

```text
Γ |- e : A :: s
Γ |- B :: s
TypedConv Γ s A B
```

妥当な `rho` を取る。第一前提から `[[e]]_rho ∈ [[A]]_rho`。
第二前提から `D s [[B]]_rho`。typed conversion の意味保存により
`[[A]]_rho = [[B]]_rho`。よって `[[e]]_rho ∈ [[B]]_rho`。

現在の `system.lean` の constructor は raw `A ≃β B` を premise にしている。
このままだと `predSubset` により soundness が壊れる可能性がある。したがって
Lean 実装では、`typeConv` の premise を `TypedConv Γ s A B` に変更するのが
最も安全である。

raw `BetaEq` をどうしても残す場合は、`A ≃β B` だけでなく「その path が
`TypedConv Γ s A B` に lift できる」という追加 premise が必要になる。すると
実質的には `TypedConv` を使っているのと同じである。

### 5.14 `provableIntro`

自然言語の補助命題 `prop_inhabited_iff_true`: proposition の意味値 `P` について、
`P` に証明値が属することと `P = trueVal` は同値である。

前提は `Γ |- p : P :: prop`。妥当な `rho` を取る。typing soundness により
`[[p]]_rho ∈ [[P]]_rho`。

命題は proof-irrelevant に解釈するので、命題値 `[[P]]_rho` に証明項が属する
ことは `[[P]]_rho = trueVal` と同値である。よって `Γ |= P`。

Lean では `prop_inhabited_iff_true` のような field を使う。

### 5.15 `proveTerm`

前提は `Γ |= P`。妥当な `rho` を取る。帰納法の仮定から
`[[P]]_rho = trueVal`。`[[prove P]]_rho = proofVal` であり、true proposition
には `proofVal` が属するという field により
`[[prove P]]_rho ∈ [[P]]_rho`。また `D prop [[P]]_rho` も proposition validity
から得る。

Lean では `proofVal_mem_true` と、provability から proposition formation を
取り出す regularity 補題が必要になる。あるいは `Provable` の意味に
`D prop [[P]]` も含めておくとよい。

### 5.16 `powerForm`

前提は `Γ |- A :: set i`。帰納法の仮定から `D (set i) [[A]]`。
powerset closure により `D (set i) (powerVal [[A]])`。
これは `[[power A]]` なので結論。

### 5.17 `subsetForm`

前提は

```text
Γ |- A :: set i
Γ, x : A :: set i |- P :: prop
```

任意の `x ∈ [[A]]` について、拡張 valuation で `[[P]]` は proposition として
well-formed。subset closure により

```text
subsetVal [[A]] (fun x => [[P]]_(x :: rho)) ∈ powerVal [[A]].
```

よって `[[subset (set i) A P]] ∈ [[power A]]`。また `[[power A]]` は
`set i` に属するので typing の意味が成り立つ。

### 5.18 `predForm`

前提は

```text
Γ |- B : power A :: set i
Γ |- t : A :: set i
```

第一前提より `[[B]] ∈ [[power A]]`、つまり `[[B]]` は `[[A]]` の部分集合。
第二前提より `[[t]] ∈ [[A]]`。したがって命題

```text
[[t]] ∈ [[B]]
```

は well-formed な truth value に変換できる。これが
`[[pred A B t]]` なので `D prop [[pred A B t]]`。

### 5.19 `typeLiftForm`

自然言語の補助命題: `B` が `power A` の要素なら、`typeLift A B` は `A` の
部分集合を型として見た値であり、sort `set i` の領域に属する。

前提は `Γ |- B : power A :: set i`。`[[B]]` は `[[A]]` の部分集合である。
`typeLift A B` はその部分集合を型として見る構成なので、意味は
`[[B]]` または `subsetVal [[A]] ...` と同一視できる。powerset の所属から
`D (set i) [[typeLift A B]]` が従う。

Lean では `typeLiftVal` を `B` の意味そのものにするのが簡単である。

### 5.20 `typeLiftIntro`

自然言語の補助命題 `typeLift_pred`: `B` が `power A` の要素なら、値 `t` が
`typeLift A B` に属することと、`pred A B t` が真であることは同値である。

前提は

```text
Γ |- B : power A :: set i
Γ |- t : A :: set i
Γ |= pred A B t
```

第三前提から `[[pred A B t]] = trueVal`。`pred` の意味より
`[[t]] ∈ [[B]]`。`typeLift A B` の意味を `[[B]]` と読むので
`[[t]] ∈ [[typeLift A B]]`。第一前提から `[[typeLift A B]]` は `set i` に
属するため、typing の意味が成り立つ。

### 5.21 `typeLiftWeak`

自然言語の補助命題 `typeLift_subset`: `B` が `power A` の要素なら、
`typeLift A B` に属する任意の値は `A` に属する。

前提は `Γ |- t : typeLift A B :: set i`。`typeLift A B` は `A` の部分集合
なので、`[[t]] ∈ [[typeLift A B]]` から `[[t]] ∈ [[A]]` が従う。
よって `Γ |- t : A :: set i`。

Lean では `typeLift_subset` という field または lemma を使う。

### 5.22 `subsetProp`

前提は `Γ |- t : typeLift A B :: set i`。前ケースと同様に
`[[t]] ∈ [[B]]` が得られる。`pred A B t` の意味はこの所属命題の truth value
なので true になる。よって `Γ |= pred A B t`。

### 5.23 `equalForm`

自然言語の補助命題: 任意の値 `a`, `b` について、`equal a b` の意味は
proposition の truth value である。

前提は `Γ |- a : A :: set i` と `Γ |- b : A :: set i`。両者の意味は同じ集合
`[[A]]` の要素である。`eqVal [[a]] [[b]]` は proposition の truth value なので
`D prop [[equal a b]]`。

### 5.24 `equalRefl`

自然言語の補助命題 `eq_true_iff`: `equal a b` の意味が true であることと、
`a` と `b` の意味が等しいことは同値である。

前提は `Γ |- a : A :: set i`。`[[a]] = [[a]]` なので
`[[equal a a]] = trueVal`。よって provable。

### 5.25 `equalElim`

前提は

```text
Γ |- a : A :: set i
Γ |- b : A :: set i
Γ |= equal a b
Γ, x : A :: set i |- P :: prop
Γ |= app (lam (set i) A P) a
```

soundness から `[[a]] = [[b]]`。また最後の前提から

```text
[[P]]_([[a]] :: rho) = trueVal
```

lambda/application の意味と substitution 補題でそう読める。
`[[a]] = [[b]]` なので

```text
[[P]]_([[b]] :: rho) = trueVal.
```

再び lambda/application の意味に戻して
`Γ |= app (lam (set i) A P) b`。

### 5.26 `existsForm`

自然言語の補助命題: 任意の set 型 `A` について、`exists A` の意味は
proposition の truth value である。

前提は `Γ |- A :: set i`。`existsVal [[A]]` は proposition の truth value なので
`D prop [[exists A]]`。

### 5.27 `existsIntro`

自然言語の補助命題 `exists_true_iff`: `exists A` の意味が true であることと、
`A` の意味が非空であることは同値である。

前提は `Γ |- e : A :: set i`。よって `[[e]] ∈ [[A]]`。したがって `[[A]]` は
非空であり、`[[exists A]] = trueVal`。

### 5.28 `takeSet`

自然言語の補助命題 `take_set_mem`: `X` が非空で、`f` が `X` から `T` へ写り、
かつ `X` 上で定値なら、`take X T f` の意味は `T` に属する。

前提は

```text
Γ |- X :: set i
Γ |- T :: set i
Γ |- f : prod (set i) X (T.liftFrom 0) :: set i
Γ |= exists X
Γ |= prod (set i) X
      (prod (set i) (X.liftFrom 0)
        (equal (app f x1) (app f x2)))
```

妥当な `rho` を取る。第一、第二前提から `[[X]]` と `[[T]]` は集合。
第三前提から `[[f]]` は `[[X]]` から常に `[[T]]` へ値を返す関数。
第四前提から `[[X]]` は非空。第五前提から任意の
`x1, x2 ∈ [[X]]` に対して

```text
appVal [[f]] x1 = appVal [[f]] x2.
```

従って `f` の image は `[[T]]` の中の singleton である。

`take` の set 側の意味を

```text
takeVal X T f = ⋃ { appVal f x | x ∈ X }
```

としておく。image が非空 singleton `{y}` なので、この union は `y` であり、
特に `y ∈ [[T]]`。したがって

```text
[[take X T f]] ∈ [[T]].
```

ここでは global choice は使わない。非空集合から代表元を選んでいるのでは
なく、定値関数の image の唯一の値を union で取り出している。

Lean では抽象 `Val` 上で union を直接定義しない場合、

```lean
take_set_mem :
  nonempty X ->
  constant_on X f ->
  maps_to X T f ->
  El (takeVal X T f) T

take_set_eq :
  x ∈ X ->
  constant_on X f ->
  takeVal X T f = appVal f x
```

のような field を `UniverseTower` に入れる。

### 5.29 `takeProp`

自然言語の補助命題 `take_prop_mem`: `X` が非空で、`f` が各 `x ∈ X` から
proposition `T` の証明を返すなら、`take X T f` の意味は `T` の証明である。

前提は

```text
Γ |- X :: set i
Γ |- T :: prop
Γ |- f : prod (set i) X (T.liftFrom 0) :: prop
Γ |= exists X
```

`X` は非空で、`f` は任意の `x ∈ X` から `T` の証明を返す。
したがって `T` は真である。proof irrelevance により、`take X T f` の値は
canonical proof value としてよく、`[[take X T f]] ∈ [[T]]`。

ここでも代表元の選択は不要である。`T` が proposition なので、どの証明を
返すかは意味上区別しない。

### 5.30 `takeEq`

自然言語の補助命題 `take_set_eq`: `X` が非空で、`f` が `X` 上で定値で、
`t` が `X` に属するなら、`take X T f` の意味は `f t` の意味と等しい。

自然言語の補助命題 `take_generation`: `take X T f` が set 型 `T` の要素として
導出されているなら、その導出から `X` の非空性、`f` の型、`f` の定値性の前提を
復元できる。

前提は

```text
Γ |- take X T f : T :: set i
Γ |- t : X :: set i
```

`takeSet` の soundness を得た導出から、`takeVal X T f` は任意の
`x ∈ [[X]]` に対して `appVal f x` と等しい。第二前提より
`[[t]] ∈ [[X]]`。よって

```text
[[take X T f]] = [[app f t]].
```

したがって `[[equal (take X T f) (app f t)]] = trueVal`。

Lean では、この規則の soundness は単なる typing soundness だけでは足りない。
`takeSet` の導出に含まれる constancy premise を取り出す必要がある。
方法は二つある。

1. `takeEq` の Lean 規則に `takeSet` と同じ constancy premise を明示的に持たせる。
2. generation lemma により
   `Γ |- take X T f : T :: set i` から `takeSet` の前提を復元する。

現在の `system.lean` は 2 を要求する形になっている。Lean 実装では
`take_generation` を先に証明するか、規則自体を 1 の形に修正するかを決める。

## 6. `falseProp` の formation

自然言語の命題 `falsePropFormed`: 空文脈で
`falseProp = prod propKind (sort prop) (var propKind 0)` は proposition として
形成できる。

`System.falsePropFormed` は次の導出を Lean で確認している。

```text
[] |- sort prop :: propKind
P : sort prop :: propKind |- P : sort prop :: propKind
P : sort prop :: propKind |- P :: prop
[] |- prod propKind (sort prop) P :: prop
```

自然言語では、`P` を `Prop` の任意の要素として仮定し、その `P` 自身が
proposition であることを `typeSort` で取り出して、`forall P : Prop, P` を
形成している。

## 7. `falseProp` の意味計算

自然言語の命題 `interp_falseProp`: 空 valuation における `falseProp` の意味は
`falseVal` である。

空 valuation で計算する。

```text
[[falseProp]]
  = [[prod propKind (sort prop) (var propKind 0)]]
  = Pi(P ∈ [[sort prop]]). [[var propKind 0]]_(P :: [])
  = Pi(P ∈ sortVal prop). P
  = forall P ∈ D(prop), P.
```

`D(prop)` には少なくとも `trueVal` と `falseVal` があり、
`falseVal` は真ではない。従って

```text
[[falseProp]] = falseVal.
```

より正確には、proposition の dependent product は

```text
trueVal  iff  every fiber is trueVal
falseVal otherwise
```

として解釈される。fiber に `P = falseVal` を取ると false なので、全体は
`falseVal`。

Lean では次を補題にする。

```lean
theorem interp_falseProp :
    interp M [] System.falseProp = M.propFalse := ...
```

この補題は `sort_el`, `propFalse_mem`, proposition product の計算規則から証明
する。

## 8. Consistency

自然言語の命題 `consistency`: 空文脈では `falseProp` は証明できない。

`h : System.Provable [] System.falseProp` と仮定する。

soundness より、空 valuation に対して

```text
[[falseProp]] = trueVal.
```

一方、前節の計算から

```text
[[falseProp]] = falseVal.
```

よって `trueVal = falseVal`。これは `UniverseTower.propTrue_ne_false` に反する。
したがって

```text
¬ System.Provable [] System.falseProp.
```

Lean では次の形になる。

```lean
theorem consistency (M : UniverseTower) :
    ¬ Provable [] falseProp := by
  intro h
  have hs := soundness M h
  have htrue : interp M [] falseProp = M.propTrue := hs empty_valid
  have hfalse : interp M [] falseProp = M.propFalse := interp_falseProp M
  exact M.propTrue_ne_false (htrue.symm.trans hfalse)
```

細部では `Provable` の意味を `interp P = propTrue` としておくか、
`true` proposition に proof value が属することとしておくかで形が少し変わる。

## 9. 項版の無矛盾性

自然言語の命題 `no_false_term`: 空文脈では `falseProp` を型に持つ項は存在
しない。

`∃ t s, System.HasType [] t System.falseProp s` と仮定する。
ある `t, s` について typing soundness より

```text
[[t]] ∈ [[falseProp]].
```

しかし `[[falseProp]] = falseVal` であり、`falseVal` は空 proposition として
解釈される。したがって要素を持たない。矛盾。

Lean では `false_empty : ∀ v, ¬ El v propFalse` のような field を
`UniverseTower` に追加し、次の形で証明する。

```lean
theorem no_false_term (M : UniverseTower) :
    ¬ ∃ t s, HasType [] t falseProp s := by
  rintro ⟨t, s, h⟩
  have hs := soundness M h
  have ht : M.El (interp M [] t) (interp M [] falseProp) := ...
  rw [interp_falseProp M] at ht
  exact M.false_empty _ ht
```

あるいは `Derives.provableIntro h` で `Provable [] falseProp` を作り、
`consistency` に渡してもよい。この場合は `s = prop` が必要なので、typing
regularity か conversion を使うより、直接 semantic contradiction を出す方が
自然である。

## 10. Lean 実装順

実装は次の順で進める。

1. `UniverseTower` に `El`, `sort_el`, proposition の truth values,
   product/powerset/subset/equality/exists/take の必要 field を足す。
2. `Valuation` と `ValidCtx` を定義する。
3. `interp : Valuation M -> Expr -> M.Val` を定義する。
4. `interp_liftFrom_zero` と `interp_subst_zero` を証明する。
5. `lookup_sound` を証明する。
6. `TypedStep` と `TypedConv` を定義する。
7. `typedStep_subject`, `typedStep_sound`, `typedConv_subject`,
   `typedConv_sound` を証明する。
8. `system.lean` の `typeConv` premise を raw `BetaEq` から `TypedConv` に
   変更する。
9. `SemSeq` を定義する。
10. `soundness : Derives Γ J -> SemSeq M Γ J` を induction で証明する。
11. `takeEq` のために、`take_generation` を証明するか、規則に前提を追加する。
12. `interp_falseProp` を証明する。
13. `consistency` と `no_false_term` を証明する。

最も不確実なのは `typeConv` と `takeEq` である。

`typeConv` は raw `BetaEq` を使わず、typed conversion に寄せるのが安全である。
raw `BetaEq` は syntax-level な到達可能性として残してよいが、soundness theorem
の `typeConv` case では使わない。

`takeEq` は現在の規則だと `take` の typing derivation から constancy premise
を復元する必要がある。これは generation lemma でできるはずだが、実装負荷が
高ければ `takeEq` に constancy premise を明示的に追加する方がよい。
