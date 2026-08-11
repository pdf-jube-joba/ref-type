# `System` の直接モデルによる相対無矛盾性

## 1. 主定理と証明の基礎

対象は `doc/book/src/system.md` および `RefType.System.Derives` の体系である。
`Gamma |- A :: s` を sorting、`Gamma |- e : A :: s` を typing、
`Gamma |= P` を provability と書く。`->` は `Reduces`、`->*` はその反射推移閉包、
`≃beta` は `BetaEq` である。

外部の集合論として ZFC に加え、推移的な Grothendieck universe の列

```text
U_0 in U_1 in U_2 in ... in U_omega in W
```

が存在すると仮定する。`U_omega` はすべての `U_i` を含み、`W` は
`U_omega` を含む。この仮定は、可算個の strongly inaccessible cardinal と、
それらより大きい strongly inaccessible cardinal があるという仮定から得られる。
Lean ではこの集合論自体を形式化せず、以下で取り出す演算と閉包則を
`UniverseTower` の field として仮定する。

> [!important]
> **定理（相対無矛盾性）** 上の universe tower が存在するなら、空文脈で
>
> ```text
> falseProp = (P : Prop) -> P
> ```
>
> は証明できない。また、`falseProp` を型に持つ項も存在しない。

証明は次の順で行う。

1. reduction と typing だけに関する構文メタ理論を証明する。
2. conversion に sorting 導出を注釈した有限の導出へ元の導出を変換する。
3. tower 上に導出依存の解釈を定義する。
4. 注釈付き導出の高さに関する強い帰納法で、soundness、reduction の意味保存、
   coherence を同時に証明する。
5. `falseProp` の意味が空命題であることから矛盾を得る。

この順序では、意味論を subject reduction の証明に使わず、soundness の
`typeConv` case で未証明の conversion invariance を呼び出すこともない。

## 2. 集合モデル

### 2.1 sort の領域

意味値全体を `W` の要素とする。各 sort の領域と sort 自身の値を次で定める。

```text
D_(set i)       = U_i,       S_(set i)       = U_i,
D_(setKind i)   = U_(i+1),   S_(setKind i)   = U_(i+1),
D_prop          = {0,1},     S_prop          = {0,1},
D_propKind      = U_omega,   S_propKind      = U_omega.
```

ここで `0=empty`、`bullet=empty`、`1={bullet}` とする。従って任意の sort `s` と
値 `a` について

```text
a in S_s  iff  a in D_s
```

である。`U_i in U_(i+1)` と `{0,1} in U_omega` から sort axiom も満たされる。

命題値は `0` と `1` だけであり、集合としての所属は

```text
v in p  iff  v=bullet and p=1
```

を満たす。従って証明項をすべて `bullet` に潰しても membership は正しく保存
される。meta-level の命題 `Q` の真理値を `truth(Q)` と書く。

### 2.2 dependent product、lambda、application

`A` と family `B(x)` に対し、product の結果 sort が `prop` でなければ

```text
Pi(A,B) = { f | f is a functional graph with domain A
                and app(f,x) in B(x) for every x in A }.
```

`Lam(A,m)` は `{(x,m(x)) | x in A}` という graph とする。application は全域化し、
functional graph の domain 内ではその値、domain 外または graph でない値では
`0` を返す。この定義から

```text
x in A                         => app(Lam(A,m),x)=m(x),
f in Pi(A,B) and x in A        => app(f,x) in B(x),
(forall x in A, m(x) in B(x))  => Lam(A,m) in Pi(A,B)
```

が従う。graph、product は family の `A` 上での値だけに依存する。

product の結果 sort が `prop` なら、function set を作らず

```text
Pi(A,B) = truth(forall x in A, B(x)=1)
```

とする。この product の証明項は `bullet` である。これが impredicative な
`prop` を proof-irrelevant に解釈する箇所である。

Grothendieck universe の dependent product に対する閉包性から、
`prodResult? r q = some z` の各 non-proposition case で `Pi(A,B) in D_z` が
成り立つ。特に `(setKind i,set i,set(i+1))` では domain と product が
`U_(i+1)` に入り、`(set i,propKind,propKind)` では `U_omega` の閉包性を使う。

### 2.3 power、subset、equality、existence

well-formed な入力では次の通常の集合を使い、それ以外の入力では `0` を返して
演算を全域化する。

```text
Power(A)       = { B | B subset A },
Subset(A,P)    = { x in A | P(x)=1 },
Pred(A,B,t)    = truth(t in B),
TypeLift(A,B)  = B,
Eq(a,b)        = truth(a=b),
Exists(A)      = truth(exists x, x in A).
```

`Pred` の第一引数は formation にだけ使う。`A in U_i` なら powerset とすべての
subset は `U_i` に入る。`B in Power(A)` なら `B in U_i` かつ `B subset A` で
あるため、`TypeLift` の formation、introduction、weakening は通常の subset
membership になる。

### 2.4 `take`

set-valued な `take` は全入力について

```text
Take(X,T,f) = union { app(f,x) | x in X }
```

と定める。`X` が非空で `f` が `X` 上で定値 `y` を取り、`y in T` なら image は
singleton `{y}` なので

```text
Take(X,T,f)=y,    Take(X,T,f) in T.
```

これは代表元を選ばないため global choice を使わない。proposition-valued な
`take` の項値は `bullet` とする。

> [!important]
> **補題（モデルの閉包性）** 上で定義した値、membership、product、lambda、
> application、power、subset、predicate、type lift、equality、existence、take は、
> `System` の各 formation rule に対応する sort closure と、各 introduction /
> elimination rule に対応する membership law を満たす。

**証明。** proposition product は真理値の定義から従う。non-proposition product
は各 `U_i` と `U_omega` の dependent product closure から従う。power と subset は
powerset closure と separation、graph と `take` は replacement、pairing、union
から得られる。`take` の二法則は前項の singleton 計算である。残りは各演算の定義を
展開すればよい。従って、以下で仮定する意味論的 law はこの集合モデルで同時に
実現され、互いに矛盾する公理の寄せ集めではない。□

## 3. 構文メタ理論

この節は意味論を一切使わない。

### 3.1 renaming、weakening、substitution

de Bruijn index の一般 renaming `rename xi` と simultaneous substitution
`substitute sigma` を考える。binder の下では `xi` と `sigma` を通常通り lift
する。現在の `liftFrom` と `subst` はそれぞれ一変数の場合である。

> [!important]
> **補題（renaming と substitution の代数則）** identity、composition、binder
> 下での lift、renaming と substitution の交換、および
>
> ```text
> M =>par M', N =>par N'  implies  M[N] =>par M'[N']
> ```
>
> が成り立つ。ここで `=>par` は3.2節の parallel reduction である。

**証明。** 最初の四つは式の構造帰納法である。variable case は index の大小で
場合分けし、binder case では帰納法の仮定を lifted renaming / substitution に
適用する。最後の主張は parallel reduction の導出帰納法であり、ordinary beta
case では substitution composition、`predSubset` case でも同じ binder 用の等式を
使う。□

> [!important]
> **補題（構文的 weakening）** `d::Gamma` が well-formed なら、`Gamma` で導出
> できる sorting、typing、provability を一段 lift した判断は `d::Gamma` で導出
> できる。

**証明。** `sortWeak`、`typeWeak`、`propWeak` そのものである。任意位置への挿入版は
renaming theorem を導出に関して証明して得る。□

> [!important]
> **補題（構文的 substitution）** `Gamma |- u : A :: r` とする。
>
> 1. `x:A::r,Gamma |- B :: s` なら `Gamma |- B[u] :: s`。
> 2. `x:A::r,Gamma |- e : B :: s` なら `Gamma |- e[u] : B[u] :: s`。
> 3. `x:A::r,Gamma |= P` なら `Gamma |= P[u]`。

**証明。** 三判断の導出に関する同時帰納法を行う。variable zero は `u`、successor
は一段下げた variable になる。binder case では `u` を lift する。`typeConv` case
では `A≃beta B` から substitution compatibility により
`A[u]≃beta B[u]` を得る。`takeSet` の二重 binder では substitution を二度 lift
する。その他は同じ constructor を帰納法の仮定へ適用する。□

### 3.2 confluence

parallel reduction は、全 constructor の reflexive congruence、ordinary beta

```text
app (lam s A body) arg =>par body'[arg']
```

および `predSubset` の次の二規則を持つ。

```text
pred A (subset s B P) t =>par app (lam s B' P') t',
pred A (subset s B P) t =>par P'[t'].
```

各右辺の prime は対応する部分式の parallel reduct である。第二規則は
`predSubset` の直後に現れる ordinary beta も同時に進める。

complete development `M*` は構造再帰で定め、redex case だけ次とする。

```text
(app (lam s A body) arg)*       = body*[arg*],
(pred A (subset s B P) t)*      = P*[t*].
```

ここで縮めるのは元の項に由来する residual であり、「新たに現れるすべての redex
を再帰的に正規化する」という意味ではない。従って自己適用を含む untyped term
に対しても `M*` は構造再帰で全域に定義される。

> [!important]
> **補題（parallel complete development）** `M =>par N` なら
> `N =>par M*` である。

**証明。** `M` の構造に関する帰納法と、`M=>par N` の最後の規則の inversion を
使う。通常の beta の contraction case は parallel substitution 補題を使う。
`predSubset` では三つの場合がある。

1. congruence のまま `pred A' (subset B' P') t'` へ進んだ場合は、第二の特殊規則で
   `P*[t*]` へ進む。
2. `app (lam B' P') t'` へ進んだ場合は ordinary parallel beta で進む。
3. 既に `P'[t']` へ進んだ場合は parallel substitution 補題で進む。

いずれも帰納法の仮定から `P'=>par P*` と `t'=>par t*` が得られ、同じ
`P*[t*]` に到達する。他の constructor は congruence だけなので直ちに従う。□

> [!important]
> **定理（confluence）** `M ->* M1` かつ `M ->* M2` なら、ある `N` が存在して
> `M1 ->* N` かつ `M2 ->* N` である。

**証明。** 構造帰納法で `M=>par M`。一段 reduction は parallel reduction に
含まれ、parallel reduction は `->*` に含まれる。前補題から parallel reduction
は diamond property を持つので、その反射推移閉包は confluent である。包含関係を
使って `->*` へ戻す。□

> [!important]
> **系（joinability）** `A≃beta B` なら、ある `C` が存在して
> `A->*C` かつ `B->*C` である。

**証明。** `BetaEq` の導出帰納法。step は `C=B`、対称 case は二経路を交換する。
transitive case は二つの join diagram の中央から出る二経路を confluence で合流
させる。□

### 3.3 canonical origin、regularity、sort uniqueness

typing の最後には `typeConv`、三つの weakening、`typeLiftIntro`、
`typeLiftWeak` のように項の outer constructor を作らない規則が並び得る。
また `typeElem` / `typeSort` は sorting と typing の間を移る。これらを
**detour** と呼ぶ。`typeElem` ではその sorting premise へ、`typeSort` ではその
typing premise へ移り、他の detour でも strict premise へ移る。従って sorting と
typing の導出木を同時に反転すれば有限回で構文の outer constructor に対応する
formation / introduction rule に着く。

> [!important]
> **補題（canonical origin）** sorting と typing の導出を同時に反転して detour
> を除くと、式または項の outer constructor に対応する core rule に到達する。
> 途中の `typeElem/typeSort` は universe object とその sorting origin を、
> `typeConv` は表示型との beta conversion を、`typeLiftIntro/Weak` は元の base
> typing を記録する。
> 特に次が成り立つ。
>
> 1. subset が `power A` を型に持つなら、その構文上の base `B` と `A` は
>    beta-convertible であり、`B` と predicate の formation を復元できる。
> 2. application の typing から function、argument、codomain の typing を復元
>    できる。function が lambda なら、その body typing と構文上の domain まで
>    復元できる。
> 3. `take X T f` が set sort の項なら、同じ構文上の `X,T,f` を持つ `takeSet`
>    の四 premise を復元できる。

**証明。** sorting / typing 導出の高さに関する同時帰納法。weakening と conversion
は premise へ帰納法を適用して結果を transport する。`typeElem` と `typeSort` は
互いの新しい導出を作らず、現在の constructor が保持する strict premise へ進む。
`typeLiftWeak` はその premise へ、`typeLiftIntro` は同じ項の base typing premise へ
進むので高さが真に減る。
core rule では outer constructor を比較する。表示型が `power` や `prod` の場合、
joinability と、これらの head を変える root reduction がないことから domain と
codomain の conversion を取り出す。異なる不活性 head は共通 reduct を持たない。
これで三つの特殊形を含む全 case が尽きる。□

> [!important]
> **補題（regularity）** 導出可能な判断の文脈は well-formed であり、
>
> ```text
> Gamma |- e : A :: s  =>  Gamma |- A :: s,
> Gamma |= P            =>  Gamma |- P :: prop.
> ```

**証明。** 四判断の導出に関する同時帰納法。variable は lookup された宣言型の
formation を renaming で現在位置まで運ぶ。PTS の introduction / elimination と
`typeConv` は明示された型 formation を使う。`typeLiftWeak`、`subsetProp`、
`takeEq` は canonical origin から base、predicate、application の formation を
復元する。`equalElim` は `P` の formation と `b:A` から lambda/application の
formation を再構成する。他の proposition rule は対応する formation ruleを直接
使う。各 premise の文脈 well-formedness も同じ帰納法で得られる。□

> [!important]
> **補題（sort uniqueness）** `Gamma |- A :: s` と `Gamma |- A :: t` なら
> `s=t` である。

**証明。** 二導出の高さの和に関する帰納法。weakening を剥がし、`typeSort` は
canonical origin で `A` の core typing まで進む。sort axiom の target と
`prodResult?` は関数なので結果が一意である。power、typeLift、predicate、equality、
exists は規則により結果 sort が固定される。表示型の conversion が介在する場合は
joinability と head discrimination で同じ core head に帰着する。
`typeLiftIntro/Weak` は sorting rule ではなく、sort object を別の sort objectへ
変換することもできない。従ってすべての case で `s=t`。□

> [!important]
> **補題（term sort uniqueness）** `Gamma |- e:A::s` と
> `Gamma |- e:B::t` なら `s=t` である。表示型 `A` と `B` が
> beta-convertible であるとは限らない。

**証明。** canonical origin で両導出の detour を剥がし、core rule の組を調べる。
variable の sort annotation、proof term、subset、take、lambda/application の
result sort は、それぞれ lookup、構文、または `prodResult?` と subterm の sort
uniqueness により一意である。`typeConv` は sort を保存し、`typeLiftIntro/Weak` は
どちらも `set i` の内部だけで型を変える。`typeElem` に到達した側は、その sorting
origin と functional な `axiomTarget?` に帰着する。異なる core head は同じ raw
term を結論できない。従って `s=t`。□

一般の type uniqueness は成り立たない。文脈に `A::set i` と `t:A` を置き、
`B={x:A | x=x}` とすれば `t:A` と `t:TypeLift(A,B)` が得られる。`A` を variable
にすれば二型の head は異なり、beta-convertible ではない。以後この偽の補題は
使用しない。

### 3.4 subject reduction

sorting だけを単独で帰納法にかけると、predicate や equality の congruence case
で typed subterm を扱えない。そこで次の三主張を同時に示す。

> [!important]
> **定理（subject reduction）** 次が同時に成り立つ。
>
> 1. `Gamma |- A :: s`、`A->A'` なら `Gamma |- A' :: s`。
> 2. `Gamma |- e : A :: s`、`e->e'` なら `Gamma |- e' : A :: s`。
> 3. `Gamma |= P`、`P->P'` なら `Gamma |= P'`。
>
> また `Gamma |- e:A::s`、`A->A'` なら `Gamma |- e:A'::s`。

**証明。** 最初の三主張は導出の高さと reduction 導出の組に関する同時帰納法。
まず canonical origin で detour を剥がす。congruence case では、型位置には第1、
項位置には第2、proposition 位置には第3の帰納法の仮定を適用して、同じ core rule
を再構成する。subset の base が進んで表示型が `power A'` になった場合などは、
`power A'≃beta power A` と `typeConv` で元の表示型へ戻す。

ここでいう congruence case は `prodDom/prodCodom`、`lamTy/lamBody`、
`appFn/appArg`、`prove`、`power`、`subsetBase/subsetPred`、
`typeLiftLeft/typeLiftRight`、`predLeft/predMid/predRight`、
`equalLeft/equalRight`、`exists_`、`takeDomain/takeCodomain/takeFunction` のすべてで
ある。従って `Reduces` の constructor で残る root case は ordinary `beta` と
`predSubset` だけである。

ordinary beta は lambda/application generation と構文的 substitution を使う。
`predSubset`

```text
pred A (subset (set i) B P) t
  -> app (lam (set i) B P) t
```

では source の `predForm` と subset generation から

```text
Gamma |- t : A :: set i,    A≃beta B,
x:B::set i,Gamma |- P :: prop
```

を得る。conversion で `t:B` とし、`P` に `typeElem`、続いて `lamIntro` と
`appElim` を適用すると target は `prop` に sort される。typing/provability 版は
この sorting と `typeElem`、`typeConv`、`provableIntro` を使う。

`takeDomain` では `X->X'` に第1主張を適用し、function type、`exists X`、定値性の
二重 product をそれぞれ type conversion と第3主張で `X'` へ transport して
`takeSet/takeProp` を再適用する。`takeCodomain` も同様で、再構成後の表示型 `T'`
を `typeConv` で元の `T` へ戻す。`takeFunction` では第2主張で `f'` の function
typing を得て、定値性 proposition 内の二つの `f` occurrence を第3主張を反復して
`f'` へ進める。従って三つの `take` congruence も generic というだけで premise を
失ってはいない。

最後の主張は regularity で `A'::s` を第1主張から得て、一段 reduction が
`A≃beta A'` を与えることから `typeConv` を一回適用する。意味論は使っていない。□

## 4. conversion を注釈した導出

元の `typeConv` は raw な `BetaEq` だけを持つ。そのまま導出帰納法で soundness を
証明すると、conversion の意味保存と soundness が循環する。循環を有限データへ
展開するため、証明専用の完全注釈付き判断 `Derives+` を導入する。

`Derives+` は元の規則と同じだが、`typeConv` は `A≃beta B` の代わりに、ある `C`
への二本の typed path を保持する。

```text
A=A0 -> A1 -> ... -> Am=C,
B=B0 -> B1 -> ... -> Bn=C.
```

path の各節点には `Gamma |-+ Ai :: s` または `Gamma |-+ Bj :: s` の導出を添える。
各次節点の導出は3.4節の subject reduction で直前の注釈付き導出から構成したものを
そのまま保存する。共通終点に二つの導出がある場合も両方を有限データとして保存する。

さらに、WF 以外のすべての node はその文脈の WF 導出を保持し、typing node
`Gamma |-+ e:A::s` は `Gamma |-+ A::s` を、provability node `Gamma |=+ P` は
`Gamma |-+ P::prop` を保持する。これらは3.3節の regularity で作る証拠である。
後から regularity 導出を組み立てると元の node より高くなる場合があるため、意味論で
使う証拠を最初から node の field にしておくことが重要である。

注釈付き導出の高さは、constructor と、内部の path および節点導出すべてを含む木の
高さとする。

> [!important]
> **補題（注釈付き regularity と subject reduction）** 3.3節の regularity と
> 3.4節の四つの subject reduction は、すべての `Derives` を `Derives+` に置き
> 換えても成り立つ。subject reduction が作る target 導出には、source 導出から
> 再帰的に作った WF、formation、conversion path をすべて保持できる。

**証明。** 3.3節と3.4節の証明を注釈付き導出に対して繰り返す。`typeConv` case
では既に constructor 内にある二本の path を再利用し、新しい conversion が必要な
場合は confluence で join diagram を合成する。再帰は source の strict premise
または reduction の strict subderivation にだけ行うため、有限の注釈付き導出が
得られる。□

> [!important]
> **補題（erase）** `Derives+ Gamma J` なら `Derives Gamma J` である。

**証明。** 注釈付き導出の帰納法。`typeConv` では左 path、逆向きの右 pathを
`BetaEq.step/symm/trans` で連結して `A≃beta B` を復元し、元の `typeConv` を使う。□

> [!important]
> **補題（elaboration）** `Derives Gamma J` なら `Derives+ Gamma J` である。

**証明。** 元の導出に関する帰納法。`typeConv` 以外は帰納法の仮定を同じ規則へ
入れ、WF と formation field は既に elaboration 済みの premise に注釈付き
regularity / canonical origin を適用して構成する。元の regularity 導出をもう一度
elaborate する再帰呼出しは行わない。`typeConv` では source typing の regularity と
target sorting を使い、
joinability から共通 reduct `C` を取る。3.4節の subject reduction を各 step に
適用して二本の path の全節点を注釈する。source typing と target sorting は現在の
`typeConv` の真の premise なので既に elaboration 済みであり、path の後続導出は
前補題の注釈付き regularity / subject reduction でそれらから直接構成する。従って
現在の node を再帰的に呼び出しておらず、有限の `Derives+` が得られる。□

従って以後 `Derives+` の soundness を示せば元の体系へ戻せる。

## 5. 導出依存の解釈

### 5.1 valuation

論理的にはまず5.2節の denotation relation を全 valuation 上で定義し、その relation
を使って `Valid` を定義する。denotation relation の定義自体は valuation の
validity を要求しないため、定義は循環しない。説明上、文脈の意味を先に示す。

注釈付き WF 導出 `hGamma` に対する妥当な valuation を帰納的に定める。

```text
Valid(empty, []).
Valid(extend hGamma hA, v::rho)
  iff Valid(hGamma,rho)
      and a is the value denoted by hA at rho
      and v in a.
```

`s=prop` なら最後の membership から自動的に `v=bullet` が従う。空型を宣言した
well-formed context には valuation がないが、soundness は妥当な valuation を
仮定する条件文なので問題ない。

> [!important]
> **補題（valuation と lookup）** `Valid(hGamma,rho)` なら tail valuation は元の
> context に妥当である。また `Lookup Gamma i A s` なら、`rho[i]` は lookup された
> 型の解釈に属する。

**証明。** 前者は `Valid` の inversion。後者は lookup 導出の帰納法で、`here` は
head membership、`there` は帰納法の仮定と semantic renaming を使う。ここで必要な
semantic renaming の variable case は valuation の index 計算だけであり、lookup
soundness を仮定しない。従ってこの補題と5.2節の semantic renaming を、lookup と
denotation 導出の高さの和に関して同時に証明できる。□

### 5.2 denotation relation

同じ raw lambda、application、take が proof と data の双方に使われるため、raw
expression だけの全域関数は定義しない。注釈付き導出 `h` と valuation `rho` に
対する Prop-valued relation を使う。

```text
SortDenotes(h,rho,a),
TypeDenotes(h,rho,Aval,eVal),
ProvDenotes(h,rho,p).
```

`TypeDenotes` は必ず node の formation field `hA` に対する
`SortDenotes(hA,rho,Aval)` を含み、その上で項値を定める。`ProvDenotes` は node の
proposition formation field `hP` を使い

```text
ProvDenotes(h,rho,p)  iff  SortDenotes(hP,rho,p)
```

とする。従って typing / provability と regularity sorting の接続は定義から失われ
ない。各 provability constructor の soundness は、この `p` が `1` であることを
示す問題になる。

主要 clause は次の通り。

| 導出 | 値 |
| --- | --- |
| sort axiom | `S_s` |
| variable | valuation の対応成分 |
| `typeElem` / `typeSort` | premise が記録した値 |
| `prodForm` | `Pi(A,x |-> B(x))` |
| `lamIntro` | result sort が `prop` なら `bullet`、それ以外は `Lam` |
| `appElim` | term sort が `prop` なら `bullet`、それ以外は `app` |
| `typeConv` | source の項値と target sorting の型値 |
| proof term | `bullet` |
| `power/subset/pred/typeLift/equal/exists` | 2.3節の対応する値 |
| `takeSet` | `Take(X,T,f)` |
| `takeProp` | `bullet` |

binder body は `x in A` ごとの拡張 valuation における denotation relation で family
を定める。二つの選び方は domain 上で同じであれば `Pi` と `Lam` の外延性により
同じ値になる。

> [!important]
> **補題（semantic renaming と substitution）** 妥当な valuation の対応する
> 挿入・置換に対し、renaming / substitution 後の注釈付き導出が表す値は元の値と
> 等しい。特に `u0` が `u` の項値なら
>
> ```text
> [[B[u]]]rho = [[B]](u0::rho).
> ```

**証明。** denotation relation と注釈付き導出に関する同時帰納法。variable case は
valuation の計算と前項の lookup induction、binder case は lifted
renaming/substitution を使う。
`typeConv` の path 自体も構文的 renaming/substitution で transport し、各節点に
帰納法の仮定を適用する。proof-valued variable は両側とも `bullet`。□

## 6. 基本定理

ここが循環を解消する中心である。次の五主張を一つの強い帰納法で証明する。

> [!important]
> **定理（denotation、fundamental theorem、各 invariance、coherence）**
> 妥当な valuation のもとで次が成り立つ。
>
> 1. **Denotation existence:** sorting、typing、provability の各導出を表す値が
>    存在する。
> 2. **Fundamental theorem:** sorting 値は `D_s` に属し、typing の型値は `D_s`
>    に属し、項値は型値に属する。provability の命題値は `1` である。
> 3. **Step invariance:** subject reduction で結んだ一段 reduction の source と
>    target は同じ値を表す。typed term reduction についても項値が等しい。
> 4. **Path invariance:** 注釈付き path の両端は同じ値を表す。
> 5. **Coherence:** 同じ judgement の二つの注釈付き導出は同じ値を表す。同じ
>    導出に対する denotation relation の値も一意である。さらに typing が記録する
>    型値はその node の formation field の sorting 値と等しく、provability の
>    命題値もその node の proposition formation field の sorting 値と等しい。
>    同じ raw term の二つの typing は、表示型が異なっていても同じ項値を表す。

**証明。** 関係する注釈付き導出、path、join diagram の高さの最大値 `n` に関する
強い帰納法を行う。`typeConv` node 内の二本の path と全節点の導出、各 node が
保持する WF / formation 導出は、その node より真に低い。従って conversion case
で path invariance や共通終点の coherence を使うときも、`equalElim` などで
regularity sorting の step invariance を使うときも、帰納法の仮定の高さは必ず
`n` 未満である。これが従来の循環した「三定理の同時帰納法」との違いである。

高さ `n` の段階では、まず denotation existence と fundamental theorem、次に
step/path invariance、最後に coherence を示す。binder family は各
`x in A` に対する低い body 導出の denotation の一意性で定まるため、replacement
でその graph を集合にできる。ここで任意の候補から代表を選ぶ global choice は
使わない。

まず step invariance を確認する。

- ordinary beta が sorting された type-level application の場合、canonical
  origin から argument typing を得る。fundamental theorem の低い導出に対する
  帰納法の仮定により argument 値は lambda domain に入る。graph beta と semantic
  substitution から両辺の値が等しい。
- typed term の ordinary beta で結果 sort が `prop` なら両項値は `bullet`。
  それ以外は前項と同じ graph beta を使う。
- `predSubset` では subset generation と fundamental theorem から `t in B`。
  source は `truth(t in B and P(t)=1)`、target は domain 内の graph beta により
  `P(t)` なので等しい。なお全域 application の定義では `t notin B` の場合も両辺
  は `0` だが、derivable source ではその場合は起こらない。
- congruence は reduction 位置に応じて sorting、typing、provability 版の低い
  step invariance と、各意味演算の外延性を使う。binder body は任意の
  `x in A` で拡張した妥当な valuation に帰納法の仮定を適用する。

path invariance は各一段の step invariance と等式の推移性から従う。左右の path
の共通終点に異なる導出が付いている場合は、高さの低い coherence を使う。

次に fundamental theorem を導出規則ごとに確認する。

### 6.1 PTS と proof

- `wfEmpty` / `wfExtend` を含む WF judgement の意味は `True` とする。soundness は
  「すべての valuation が
  valid」という主張ではない。sorting / typing / provability case で、対応する
  WF 導出に妥当な valuation を仮定する。
- `sortAxiom` は `S_s in D_t`。
- weakening は valid tail、semantic renaming、premise の帰納法の仮定。
- variable は lookup 補題。
- `typeElem` と `typeSort` は `a in S_s iff a in D_s` の二方向。
- `prodForm` は各 `x in A` で valid context を拡張し、body の帰納法の仮定と
  product closure を使う。
- `lamIntro` の result sort が `prop` なら、body proof の membership から各 fiber
  が `1` であり product も `1`。従って `bullet` が属する。non-proposition なら
  body 値を graph にして lambda introduction law を使う。
- `appElim` の term sort が `prop` なら product truth から該当 fiber が `1`。
  それ以外は graph elimination。最後に semantic substitution で `B[a]` の値へ
  書き換える。
- `typeConv` は source typing の帰納法の仮定から `eVal in Aval`。注釈された左右
  path の path invariance、source typing とその formation field の coherence、
  共通終点の coherence から `Aval=Bval`。従って `eVal in Bval`。ここでは現在の
  soundness theorem 自身を再帰呼出ししない。
- `provableIntro` は proposition に要素があることから命題値が `1`。
- `proveTerm` は premise が `1` であることから `bullet in 1`。

### 6.2 subset、equality、existence、take

- `powerForm` は powerset closure。`subsetForm` は
  `Subset(A,P) in Power(A)`。
- `predForm` は `truth(t in B) in D_prop`。
- `typeLiftForm` は `B in Power(A)` から `B in D_(set i)`。
- `typeLiftIntro` と `subsetProp` は `Pred(A,B,t)=1 iff t in B`。
  `typeLiftWeak` は `B subset A`。
- `equalForm` と `equalRefl` は truth value と反射律。
- `equalElim` は equality premise から `aVal=bVal`。最後の premise と
  beta step invariance から `P(aVal)=1` を得て、等しい値で置換し
  `P(bVal)=1`。もう一度 beta step invariance で conclusion の applicationへ戻す。
- `existsForm` は truth value、`existsIntro` は項値を witness にする。
- `takeSet` では existence から `X` が非空。function typing から `f` は `X` を
  `T` へ写す。二重 proposition product と equality の soundness から `f` は
  `X` 上で定値。2.4節の law で `Take(X,T,f) in T`。
- `takeProp` では proposition product が `1` なので各 `x in X` で `T=1`。
  existence から一つの `x` があるため `T=1`、従って `bullet in T`。
- `takeEq` は canonical origin で元の `takeSet` の四 premise を得る。第二 premise
  の `t in X` と定値性から `Take(X,T,f)=app(f,t)` なので equality は `1`。

最後に coherence を示す。二導出の最後の detour を canonical origin まで剥がす。
`typeConv` は低い path invariance、`typeLiftIntro/Weak` は保存している base term
値、weakening は semantic renaming に帰着する。同じ outer constructor の二つの
core rule は、低い subderivation の coherence と `Pi`、`Lam`、`Subset` の外延性で
一致する。application や lambda の subterm が異なる表示型で導出されている場合は、
term sort uniqueness と、低い同一 raw term に対する term coherence を使う。
sorting / typing で異なる core rule が同じ judgement を結論し得る
`typeElem/typeSort` の迂回は、低い premise の coherence に帰着する。それ以外の
異なる不活性 head は canonical origin と head discrimination で除かれる。
provability には `equalRefl` と `provableIntro` のように異なる core rule が同じ
judgement を与える場合があるが、その段階で既に示した fundamental theorem により
双方の命題値が `1` なので一致する。typing / provability と各 formation field の
cross-relation coherence は各 constructor の定義を展開し、低い premise の
coherence と path invariance を使って示す。これで五主張の全 case が閉じ、強い
帰納法が完了する。□

> [!important]
> **系（元の体系の soundness）** 元の導出と妥当な valuation `rho` に対し、
>
> 1. `Gamma |- A :: s` なら `[[A]]_rho in D_s`。
> 2. `Gamma |- e : A :: s` なら `[[A]]_rho in D_s` かつ
>    `[[e]]_rho in [[A]]_rho`。
> 3. `Gamma |= P` なら `[[P]]_rho=1`。

**証明。** 元の導出を elaboration し、fundamental theorem を適用する。別の
elaboration を選んでも coherence により値は同じである。□

## 7. `falseProp`

> [!important]
> **補題（formation）** 空文脈で `falseProp :: prop` が成り立つ。

**証明。** sort axiom から `sort prop :: propKind`。文脈に
`P : sort prop :: propKind` を追加すると variable rule で
`P : sort prop :: propKind`、`typeSort` で `P :: prop`。product formation の
`(propKind,prop,prop)` を使って `(P:Prop)->P :: prop`。□

> [!important]
> **補題（意味計算）** 空 valuation における任意の elaboration で
> `[[falseProp]]=0` である。

**証明。** formation の標準導出では

```text
[[falseProp]] = Pi(S_prop, P |-> P)
              = truth(forall P in {0,1}, P=1).
```

`0 in S_prop` だが `0!=1` なので右辺は `0`。同じ sorting judgement の他の
elaboration も coherence によりこの値と等しい。□

## 8. 無矛盾性

> [!important]
> **定理（provability の無矛盾性）** 空文脈で `falseProp` は証明できない。

**証明。** `[] |= falseProp` と仮定する。空 valuation は空文脈に妥当である。
soundness により `[[falseProp]]=1`、意味計算により `[[falseProp]]=0`。これは
`0!=1` に反する。□

> [!important]
> **定理（項の不存在）** 空文脈で `t : falseProp :: s` を満たす `t,s` は存在
> しない。

**証明。** regularity から `falseProp::s`。formation と sort uniqueness から
`s=prop`。soundness、typing と sorting の coherence、意味計算から

```text
[[t]] in [[falseProp]] = 0.
```

しかし `0=empty` は要素を持たないので矛盾。□

以上で、外部集合論における universe tower の存在を仮定した `System` の相対
無矛盾性が示された。一般の type uniqueness、strong normalization、term 全体の
normalization、global choice は使用していない。
