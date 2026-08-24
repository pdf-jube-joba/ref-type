# `system.md` の体系の相対無矛盾性

## 1. 対象とする体系

この文書の目的は、[`doc/book/src/system.md`](../system.md) で定義された、
一般再帰を含む体系の相対無矛盾性を数学的に示すことである。ここでいう無矛盾性は、
空文脈で偽命題が証明されないという proof-theoretic consistency であり、強正規化ではない。
実際、停止証明を無視した raw term の reduction には発散する `run` が存在する。
Lean のデータ型、de Bruijn index、実装用証明書は扱わない。それらは
[`formalization/lean/formalization.md`](../../../../formalization/lean/formalization.md) に分離する。

以下では `system.md` の規則表を定義とする。特に次を変更しない。

- 変数は sort annotation を持つ名前付き変数である。束縛変数は alpha-renaming してよい。
- primitive weakening は sorting と typing の二規則である。provability weakening は後で
  admissible rule として導く。
- dependent elimination の primitive premise は function typing と argument typing の二つだけで、
  substituted codomain の sorting は premise ではない。これは regularity と substitution から導く。
- reduction は通常の beta reduction、その全 compatible closure、および `system.md` にある
  `Pred`、`RfType`、`RfTerm`、`run`、`runCase` の root rule である。特に `Pred` rule は

  ```text
  Pred(A,{x:B | P},t) -> (lambda x:B.P) t
  ```

  であり、`A ≡ B` という side condition は加えない。
- `RfType` と `RfTerm` は構文の消去ではなく、それぞれ source type と payload を保持する
  raw constructor である。
- `Acc` は一般の公理ではなく、`acc intro` と `acc descent` だけで生成される predicate である。

sort を次の略記で書く。

```text
Set_i   = *^s_i,       Kind_i = square^s_i,
Prop    = *^p,         PropKind = square^p,
Comp    = *^c,         CompKind = square^c.
```

`Gamma |- A :: s` を sorting、`Gamma |- e : A :: s` を typing、`Gamma |= P` を
provability と書く。`M -> N` は一段 reduction、`->*` はその反射推移閉包、`≡` は
reduction が生成する反射・対称・推移閉包である。

外部の集合論として ZFC と、推移的な Grothendieck universe の tower

```text
U_0 in U_1 in ... in U_omega in W
```

を仮定する。`U_omega` はすべての `U_i` を含む Grothendieck universe であり、`W` も
Grothendieck universe である。例えば順序型 `omega+2` の strongly inaccessible cardinal の
狭義増加列があればよい。単なる `union_i U_i` は dependent product に閉じない可能性が
あるため、`U_omega` の代わりにはしない。

> [!important]
> **目標とする主定理。** この仮定のもとで、空文脈では
>
> ```text
> falseProp = (P : Prop) -> P
> ```
>
> は provable でなく、`falseProp` を型に持つ項も存在しない。

### 1.1 証明の水準

以下は通常の集合論内での紙上証明である。特に、モデルを提示しただけで conversion rule の
soundness を仮定することはしない。3節で typed subject reduction を、4節で conversion path を
有限な証明対象に展開する方法を、5--6節でその path に沿う意味保存と導出の coherence を示す。
規則の取りこぼしがないことは6.1節の39規則表、6.2節の補助 phase 表、8節の constructor 監査で
検査する。

これは Lean による機械検証済みという意味ではないが、主定理を条件付きにする未証明補題は
残さない。Lean 上の別構文に移す際には、6.1節の各行が一つの形式化上の case になる。

一般再帰の追加に新しい集合論的公理は要らない。`Comp` を `U_0` に解釈し、`Acc` と `run` には
ZFC の整礎再帰定理を使う。証明は、集合モデル、構文的メタ理論、soundness、`falseProp` の
意味計算の順に行う。

## 2. 集合モデル

### 2.1 sort

意味値は `W` の要素である。各 sort の領域 `D_s` と sort term 自身の値 `S_s` を

```text
D_(Set_i)    = U_i,        S_(Set_i)    = U_i,
D_(Kind_i)   = U_(i+1),    S_(Kind_i)   = U_(i+1),
D_Prop       = {0,1},      S_Prop       = {0,1},
D_PropKind   = U_omega,    S_PropKind   = U_omega,
D_Comp       = U_0,        S_Comp       = U_0,
D_CompKind   = U_1,        S_CompKind   = U_1.
```

とする。`0=empty`、`bullet=empty`、`1={bullet}` とする。tower の推移性と有限集合への
閉包から、すべての `S_s` は `W` の要素であり、

```text
a in S_s  iff  a in D_s
```

である。`U_i in U_(i+1)`、`{0,1} in U_omega`、`U_0 in U_1` により `system.md` の三種の
axiom `(Set_i,Kind_i)`、`(Prop,PropKind)`、`(Comp,CompKind)` が成り立つ。`Comp` と
`Set_0` の領域を同じ集合にしたことは、二つの sort を構文的に同一視することではない。

`p in D_Prop` なら

```text
v in p  iff  v=bullet and p=1.                         (proof_mem)
```

meta-level proposition `Q` に対し、`Q` が真なら `1`、偽なら `0` を返す値を `truth(Q)` と
書く。排中律により定義でき、

```text
truth(Q) in D_Prop,
truth(Q)=1 iff Q,
truth(Q)=0 iff not Q
```

を満たす。

### 2.2 family、product、lambda、application

family は `W` 内の functional graph で表す。graph application `app(f,x)` は、`f` が
functional graph で `x` が domain に属するときその値を返し、それ以外は `0` を返す。
従ってすべての `W`-valued input で全域である。

`system.md` の product rule `(r,q,z) in R` を考える。`z != Prop` のとき

```text
Pi_z(A,B) = { f | f is a functional graph with domain A
                 and app(f,x) in B(x) for every x in A },
Lam_z(A,m) = { (x,m(x)) | x in A },
App_q(f,x) = app(f,x).
```

sort table を直接調べると、`(r,q,z) in R` のもとで

```text
z=Prop iff q=Prop.                                      (prop-branch)
```

従って上の data branch では `q!=Prop` でもあり、

```text
x in A
  => App_q(Lam_z(A,m),x)=m(x),
f in Pi_z(A,B) and x in A
  => App_q(f,x) in B(x),
(forall x in A, m(x) in B(x))
  => Lam_z(A,m) in Pi_z(A,B).
```

`z=Prop` のときは proof-irrelevant に

```text
Pi_Prop(A,B) = truth(forall x in A, B(x)=1),
Lam_Prop(A,m) = bullet,
App_Prop(f,x) = bullet
```

とする。このとき

```text
(forall x in A, B(x)=1) => bullet in Pi_Prop(A,B),
f in Pi_Prop(A,B) and x in A => bullet in B(x).
```

後者は `f in Pi_Prop(A,B)` から product が `1`、従って全 fiber が `1` となるためである。

`system.md` の non-proposition product case ごとの閉包は次の通りである。

- `(Set_i,Set_j,Set_max(i,j))` は universe tower の包含と
  `U_max(i,j)` の dependent-product closure。
- `(Set_i,Kind_j,Kind_max(i,j))` と
  `(Kind_i,Kind_j,Kind_max(i,j))` は `U_(max(i,j)+1)` の closure。
- `(Kind_i,Set_j,Set_max(i+1,j))` は domain `U_i` 自身と各 fiber が
  `U_max(i+1,j)` に入り、この universe が dependent product に閉じることによる。
- `(PropKind,PropKind,PropKind)` は `U_omega` の closure。
- `(Set_i,PropKind,PropKind)` は `U_i subset U_omega` と `U_omega` の closure。
- `(Comp,Comp,Comp)` は `U_0` の dependent-product closure。

proposition result の `(Prop,Prop,Prop)`、`(PropKind,Prop,Prop)`、
`(Set_i,Prop,Prop)` は `truth` の定義から閉じる。これで一般再帰追加後の `R` の全 case が尽きる。

### 2.3 集合演算

すべての `W`-valued input に対して

```text
Power(A)       = { B | B subset A },
Subset(A,P)    = { x in A | P(x)=1 },
Pred(A,B,t)    = truth(t in B),
TypeLift(A,B)  = B,
Eq(a,b)        = truth(a=b),
Exists(A)      = truth(exists x, x in A)
```

とする。`P(x)` は family graph の全域 application である。`A in U_i` なら powerset と
すべての subset は `U_i` に入る。`B in Power(A)` なら `B subset A` かつ `B in U_i` なので、
type lift の formation、introduction、weakening は通常の subset membership で解釈できる。

### 2.4 take

set-valued な take を

```text
Take(X,T,f) = union { app(f,x) | x in X }
```

とする。`X` が非空で `f` が `X` 上で定値 `y` を取り、`y in T` なら image は `{y}` であり、

```text
Take(X,T,f)=union {y}=y in T.                           (take-law)
```

これは代表元を定義により選ばないので global choice を使わない。proposition-valued take の
項値は `bullet` とする。

### 2.5 Compute、reflection、accessibility、run

`A,B in U_0` に対し、tagged disjoint sum を

```text
RunStep(A,B) = ({0} x A) union ({1} x B),
continue(A,B,a) = (0,a),
finish(A,B,b)   = (1,b)
```

とする。Grothendieck universe の有限和への閉包により `RunStep(A,B) in U_0` である。
tag が異なるので二つの constructor は disjoint かつ injective である。

`Comp` と `Set_0` の双方を `U_0` で解釈したので、well-typed な input では reflection を
恒等写像として解釈できる。

```text
RfType(A)   = A,
RfTerm(A,m) = m.
```

これは raw constructor を構文的に消すという定義ではなく、その**意味値**の定義である。
特に Compute variable を含む `RfTerm_A(x^Comp)` も valuation が与える同じ集合を表す。
functional graph の定義を Set と Compute で共通にしたので、非依存 function type に対し

```text
RfType(A -> B) = RfType(A) -> RfType(B),
app(RfTerm(A -> B,f), RfTerm(C,a)) = RfTerm(B,app(f,a))       (rf-law)
```

が成り立つ。第一式には `system.md` と同じ非依存性条件を置く。第二式では annotation `C` の値を
参照しない。ただし typed な reduction の membership proof では、source の generation から
`A` と `C` の denotation が等しいことを回収する。

`F in Pi(A, const RunStep(A,B))` に対して

```text
b <_F a  iff  app(F,a)=(0,b)
```

と定める。`Acc_F subset A` を monotone operator

```text
Phi_F(X) = { a in A | forall b in A, b <_F a implies b in X }
```

の最小不動点とする。この存在と、後で使う整礎性を省略せずに確認する。ordinal `alpha` に対して

```text
X_0          = empty,
X_(alpha+1)  = Phi_F(X_alpha),
X_lambda     = union_(beta<lambda) X_beta       (lambda は limit)
```

と置く。`Phi_F` の単調性から `X_alpha subset X_(alpha+1)` である。`P(A)` は集合なので、Hartogs の
補題によりこの増大列はある ordinal `theta` で安定し、`X_theta=Phi_F(X_theta)` となる。
`Acc_F=X_theta` と置く。任意の不動点 `Y` に対して transfinite induction で
`X_alpha subset Y` だから、これは最小不動点である。

`a in Acc_F` に対して

```text
rank_F(a) = least alpha such that a in X_(alpha+1)
```

と定められる。`b <_F a` なら `b in X_(rank_F(a))` なので
`rank_F(b) < rank_F(a)` である。従って `<_F` を `Acc_F` に制限した関係は well founded である。
また不動点方程式 `Acc_F=Phi_F(Acc_F)` から

```text
(forall b in A, b <_F a implies b in Acc_F) => a in Acc_F,   (acc-intro-law)
a in Acc_F and b <_F a => b in Acc_F.                        (acc-descent-law)
```

`Acc` の命題値を

```text
Acc(A,B,F,a) = truth(a in Acc_F)
```

とする。reflection が恒等写像であり `continueFun` の意味が `b |-> (0,b)` なので、体系の
`acc intro` の最後の premise はちょうど `(acc-intro-law)` の左辺を、`acc descent` の等式
premise は `b <_F a` を表す。詳しくは、固定した `b in A` に対して equality domain は

```text
truth(app(F,a)=(0,b))
```

である。これを domain とする proposition product（含意）の値が `1` であることは、domain が
`1` なら `Acc(A,B,F,b)=1`、domain が `0` なら自明、という条件と同値である。さらに外側の
`b:A` に関する proposition product を展開すると

```text
forall b in A, b <_F a implies b in Acc_F
```

が正確に得られる。

次に ordinal `rank_F(a)`（同値には上で得た well-founded relation）に沿って recursion を行い、

```text
Run_(A,B)(F,a) = Run_(A,B)(F,a')   if app(F,a)=(0,a'),
Run_(A,B)(F,a) = b                  if app(F,a)=(1,b)
```

と定める。`F` の codomain が tagged sum なので場合分けは排他的かつ全域であり、continue case
では `(acc-descent-law)` により再帰呼出しが正当化される。従って `a in Acc_F` なら
`Run_(A,B)(F,a) in B` である。malformed または inaccessible な input での値は `0` として、
この四引数の演算をすべての `W`-valued input に全域化する。以下では型引数 `A,B` を省略して
`Run(F,a)` と書くが、演算自体はそれらにも依存する。

ここで result membership は `rank_F(a)` に関する induction で確認できる。`app(F,a)=(1,b)`
なら function typing と tagged-sum の定義から `b in B`。`app(F,a)=(0,a')` なら同様に
`a' in A` であり、`a' <_F a` から `a' in Acc_F` と `rank_F(a')<rank_F(a)` が従うので、帰納法の
仮定から `Run(F,a') in B` である。

```text
RunCase(F,a,(0,a')) = Run(F,a'),
RunCase(F,a,(1,b))  = b,
RunCase(F,a,u)      = 0             otherwise
```

とする。`a in Acc_F` かつ `u=app(F,a)` のとき、次の三つの law が成り立つ。

```text
Run(F,a) = RunCase(F,a,app(F,a)),
RunCase(F,a,(0,a')) = Run(F,a'),
RunCase(F,a,(1,b))  = b.                                  (run-laws)
```

第二式を typed な input に使うときは、invariant から `a' <_F a`、従って
`a' in Acc_F` が従うことに注意する。ここが、無条件の一般不動点と今回の `run` の違いである。

Grothendieck universe の pairing、replacement、powerset、separation、union により、ここまでの
すべての演算は `W`-valued である。well-founded recursion の graph も replacement により集合に
なる。各演算は ordinary argument の等号と、domain 上の family の pointwise equality を保つ。
特に `Pi`、`Lam`、`Subset`、`Acc`、`Run` は表示に現れた集合と graph にだけ依存する。

> [!important]
> **モデル補題。** 上の演算は `system.md` の全 formation rule に必要な sort closure、
> introduction / elimination rule に必要な membership law、data beta law、`rf-law`、
> `acc-intro-law`、`acc-descent-law`、`run-laws`、および `Pred(A,Subset(B,P),t)` に必要な
> truth law を同時に満たす。

これは上の定義と universe closure を rule ごとに展開すれば得られる。`Pred` reduction の
意味保存にはさらに derivability から `A` と `B` の値が等しく、`t in B` であることを使う。
これは3.4節の subject reduction と6節の soundness で確認する。

## 3. 構文的メタ理論

この節では意味論を使わない。変数は capture を避けて alpha-renaming し、以下では束縛変数が
文脈に新しいものとして選ばれているとする。

### 3.1 renaming、weakening、substitution

> [!important]
> **補題（renaming と substitution）。** WF、sorting、typing、provability は capture-avoiding
> renaming で保存される。また `Gamma |- u:A::r` のとき、
>
> ```text
> WF(Gamma,x:A::r,Delta)              => WF(Gamma,Delta[u/x]),
> Gamma,x:A::r,Delta |- B::s       => Gamma,Delta[u/x] |- B[u/x]::s,
> Gamma,x:A::r,Delta |- e:B::s     => Gamma,Delta[u/x] |- e[u/x]:B[u/x]::s,
> Gamma,x:A::r,Delta |= P          => Gamma,Delta[u/x] |= P[u/x].
> ```

**証明。** 文脈 `Delta` の長さと四 judgement の導出の同時帰納法である。WF の start caseは
最後の宣言の sorting に帰納法を適用して startを付け直す。variable case は `x` 自身、`x` より
新しい変数、古い変数に分ける。binder の下では置換を lift する代わりに、名前付き表示では
束縛変数を fresh に取り直す。conversion case は reduction と convertibility が substitution で
保存されることを使う。take の定値性 premise では二つの binder の双方を fresh にする。
新しい constructor では、`RfTerm_A(m)` の annotation と payload の双方、`RunStep`、`Acc`、
`run`、`runCase` の全引数に置換を入れる。`Terminates` と `RunInv` は単なる略記なので、各引数への
置換と一致する。`acc intro` の `b` は先に fresh に取り直す。□

`system.md` の weak sort / weak type から任意位置への weakening が得られる。正確には挿入位置より
後ろの context suffix の長さに関する帰納法で、base は primitive weak、step は最後の宣言の
sorting と startを作り直してから primitive weakを適用する。
provability weakening は primitive rule ではないが、

```text
Gamma |= P
=> Gamma |- Proof P : P :: Prop
=> Gamma,x:A::s |- Proof P : P :: Prop
=> Gamma,x:A::s |= P
```

により admissible である。古い変数の rule も、variable rule と weak type の反復で得られる。

> [!important]
> **補題（context conversion）。** `Gamma |- A::s`、`Gamma |- A'::s`、`A≡A'` とする。
> well-formed context 中の宣言 `x:A::s` を `x:A'::s` に置き換えても、WF、sorting、typing、
> provability は同じ raw judgement のまま保存される。

**証明。** 置換位置より新しい宣言の個数と導出の同時帰納法。`x` の variable case では
variable rule が与える型 `A'` を conversion で `A` に戻す。新しい宣言の formation と binder
body も同時に輸送する。conversion が renaming で保存されるため任意位置で同じ議論ができる。□

provability に primitive conversion rule はないが、次は admissible である。

```text
Gamma |= P,  Gamma |- Q::Prop,  P≡Q
=> Gamma |= Q.                                           (prov-conv)
```

実際 `Proof(P):P::Prop` を typing conversion で `Q` 型へ移し、provable rule をもう一度適用すれば
よい。3.4節で `RunInv` や `Terminates` の形を reduction に合わせて変える箇所では、常にこの
`(prov-conv)` と proposition の regularity を使う。

### 3.2 confluence

raw reduction は強正規化しないので、Newman の補題は使えない。代わりに
Tait--Martin-Lof の parallel reduction `=>>` を使う。これは次を一回で行ってよい関係である。

- 全 immediate subterm の reflexive parallel reduction。
- source に既に存在する beta、`Pred`、reflection、recursion redex の root contraction。subterm の
  reduction で新しく head constructor が現れた redexは、その parallel step では縮めない。
- `Pred` contraction の直後の beta contraction。

正確には、各 constructor `K` に reflexive congruence

```text
Mi =>> Mi' for every immediate subterm
---------------------------------------
K(M1,...,Mn) =>> K(M1',...,Mn')
```

を置き、binder の body は alpha-renaming して同じ fresh variable の下で比較する。これに加えて
次の root clause を置く。prime は対応する immediate subterm の parallel reduct である。

```text
(lambda x:A.M) N
  =>> M'[N'/x],

Pred(A,Subset(x:B,P),t)
  =>> (lambda x:B'.P') t',

Pred(A,Subset(x:B,P),t)
  =>> P'[t'/x],

RfType((x:A)->B)
  =>> (z:RfType(A'))->RfType(B')
       if x notin FV(B) and z is fresh,

RfTerm_(A->B)(f) @ RfTerm_C(a)
  =>> RfTerm_(B')(f'@a'),

run_(A,B)(f,a)
  =>> runCase_(A',B')(f',a',f'@a'),

runCase_(A,B)(f,a,continue_(C,D)(a0))
  =>> run_(A',B')(f',a0'),

runCase_(A,B)(f,a,finish_(C,D)(b))
  =>> b'.
```

二つの `Pred` clause の前者は primitive root step だけを、後者はその直後の beta までを一つの
parallel step で行う。これにより primitive な `Pred` step 自身も `=>>` に含まれる。
例えば `Rf-App` clause には `A=>>A'`、`B=>>B'`、`C=>>C'`、`f=>>f'`、`a=>>a'` を、
continue clause には外側と内側の四 annotation を含む全 immediate subterm の parallel premise を
置く。target に現れない reduct も、`=>>` が raw `->*` に含まれることを示すときに source を
componentwise に進めるため premise として保持する。二つの `Pred` clause は `Pred` root と直後の beta を
別々に、または一度に行う二通りを表す。

`Rf-App` の function domain と argument annotation はそれぞれ `A,C`、`runCase` の外側と
constructor 側の annotation はそれぞれ `A,B,C,D` という異なる metavariable にしたため、全 root
pattern は左線形である。従って annotation を共通 reduct へ同期して redex を復元する特殊 clause は
不要である。型保存に必要な `A≡C`、`B≡D` は raw reduction の side condition ではなく、well-typed
source の generation から回収する。

> [!important]
> **補題（parallel reduction の基本性質）。** alpha 同値を法として
>
> ```text
> M -> N       => M =>> N,
> M =>> N      => M ->* N,
> M =>> M', N =>> N'
>              => M[N/x] =>> M'[N'/x].                  (parallel-subst)
> ```

**証明。** 第一式は変化しない subterm に reflexivity を使う。第二式は parallel derivation の
帰納法で、まず congruence により全 component を prime 付きの値まで進め、最後に対応する root
rule を一度使う。`Pred` の第二 clause だけはさらに beta を一度使う。

`(parallel-subst)` も parallel derivation の帰納法である。binder はあらかじめ `N,N'` の自由変数
と異なる名前に直す。beta と `Pred` では capture-avoiding substitution の交換則を使う。
`Rf-Arrow` では source binder を substitution の support から fresh に取り直せば
`x notin FV(B)` が保存される。他の追加 root clause は左線形で、substitution が各 metavariable に
componentwise に入るだけである。□

complete development `M*` は、もとの term に既にある root redex を generic congruence より
先に一度だけ match して、次を含むように定める。

```text
((lambda x:A.M) N)*       = M*[N*/x],
Pred(A,Subset(B,P),t)*     = P*[t*/x],
RfType(A -> B)*            = RfType(A*) -> RfType(B*),
(RfTerm_(A -> B)(f) @ RfTerm_C(a))*
                            = RfTerm_(B*)(f* @ a*),
run_(A,B)(f,a)*             = runCase_(A*,B*)(f*,a*,f* @ a*),
runCase_(A,B)(f,a,continue_(C,D)(a'))*
                            = run_(A*,B*)(f*,a'*),
runCase_(A,B)(f,a,finish_(C,D)(b))*
                            = b*.
```

`RfType` の式には非依存性と freshness の side conditionを置き、target binder は alpha 同値類で
canonical な fresh name を選ぶ。他は全 immediate subterm に `*` を適用する。右辺に新しく
生じた `runCase` や `run` をさらに展開しないため、これは term の大きさに関する構造再帰であり、
normalization ではない。

> [!important]
> **補題（complete development）。** `M=>>N` なら `N=>>M*`。

**証明。** `M` の構造と parallel derivation の同時帰納法。beta contraction は parallel
substitution を使う。`Pred/Subset` overlap は、congruence のまま進む場合、primitive root だけを
進んで lambda application まで行く場合、さらに beta して substitution 後まで進む場合の三つで
ある。第一の場合は component を development してから第二の `Pred` clause、第二の場合は
parallel beta、第三の場合は parallel substitution を使い、いずれも `P*[t*/x]` に合わせる。

追加 rule の root/congruence case を明記する。

- `Rf-Arrow` source が root clause で進んだ場合、target の二つの `RfType` に帰納法を適用して
  `RfType(A*) -> RfType(B*)` へ進める。congruence で進んだ場合も、`x notin FV(B)` なら reduction は
  新しい自由変数を作らないので `x notin FV(B')` であり、そこで root clause を使って同じ target に
  進める。fresh name の違いは alpha 同値である。source では side condition が偽で、subterm の
  development 後に初めて真になった場合、`M*` は root contraction しない定義なので、target も
  congruence だけで componentwise development すればよい。
- `Rf-App` source が root clause で進んだ場合、target
  `RfTerm_(B')(f'@a')` は congruence と帰納法で `RfTerm_(B*)(f*@a*)` へ進む。congruence で
  source shape を保った場合は、`A',B',C',f',a'` をそれぞれ complete development へ進めてから
  generalized `Rf-App` clause を使う。`A*` と `C*` の一致は要求されない。
- `run` の root target に複製された `f',a'` は、それぞれ同じ `f*,a*` へ進める。congruence branch
  では component を development してから run root clause を使う。従って双方とも
  `runCase_(A*,B*)(f*,a*,f*@a*)` に進む。
- continue branch の root target `run_(A',B')(f',a0')` は congruence で
  `run_(A*,B*)(f*,a0*)` へ進む。source shape を保つ branch では外側の `A',B'` と payload を
  development し、内側の `C',D'` は root clause で捨てる。finish branch も同様で、両 branch は
  `b*` に進む。

reflection / recursion の root head は `RfType`、`RfTerm` を左にもつ application、`run`、`runCase`
のいずれかで相互に異なり、二つの `runCase` rule も第三引数の tag が異なるので相互の
root/root overlap はない。二つの `Pred` clause だけは同じ sourceを持つが、primitive-only target
が parallel betaで primitive-plus-beta targetへ進むので joinする。
subterm reduction で新しい root redex が現れた場合は、それを同じ parallel step で縮める必要は
なく、`M*` へ componentwise に進めればよい。以上で全 case が尽きる。□

従って `=>>` は alpha 同値を法として diamond であり、`->` を両側から挟む標準的な議論により

> [!important]
> **定理（confluence）。** `M->*M1` かつ `M->*M2` なら共通 reduct が存在する。

が得られる。特に `A≡B` なら `A` と `B` は joinable である。これは reduction の停止性を
仮定していない。

`sort`、variable、product、lambda、proof mark、power、subset、type lift、equality、exists、take、
`RunStep`、`continue`、`finish`、`Acc` は単独では outer head を変える root reduction を持たない。
従って二つの異なる不活性 head は convertible でなく、product、power、type lift、tagged
constructor の convertibility から対応する component の joinability が得られる。

### 3.3 regularity、generation、sort uniqueness

> [!important]
> **補題（regularity / generation package）。** 導出可能な judgement の文脈は well formed であり、
>
> ```text
> Gamma |- e:A::s  => Gamma |- A::s,
> Gamma |= P       => Gamma |- P::Prop.
> ```
>
> さらに下の `(G-Pi)`--`(G-RunCase)` の各 inversion clause が成り立つ。各 clause の結論は、
> formation / typing / provability の**導出**と、明記した component の joinを返す。従ってこれは
> raw expression の形だけを述べる inversion ではなく、後の subject reduction で再利用できる
> derivation-producing statementである。

この package は WF、sorting、typing、provability の四 judgement の regularityと、有限個の
generation clauseを一つの同時定理として証明する。表示型が conversion を経ている場合は、3.2節の
confluence と不活性 head の識別により、対応する component の joinまで出力に含める。

**証明。** WF、sorting、typing、provability の導出と上の generation statement に関する同時
強帰納法。各 detour では strict premise に進むので導出高が減る。dependent elimination case が
重要である。function typing の product generation から product formation

```text
Gamma |- A::r,
Gamma,x:A::r |- B::q,
(r,q,z) in R
```

を回収し、argument typing と substitution 補題から `Gamma |- B[a/x]::q` を得る。従って
`system.md` の dependent elimination にこの sorting premise を追加する必要はない。

type lift weak と subset property では、入力 typing の canonical origin を辿って
`B:Power(A)` と `A::Set_i` を回収する。take equal では第一 premise の take origin から
`X,T,f` の formation と function typingを回収し、第二 premiseと合わせて equality formation を
作る。

`continue_(C,D)` と `finish_(C,D)` では constructor generation から payload typing を回収する。
それらが conversion を経て `RunStep(A,B)` を表示型に持つ場合は、confluence と `RunStep` head の
injectivity から `A≡C`、`B≡D` も回収する。後述する Compute rigidity により、実際には component は
alpha 同値である。`acc descent`
では第一 premise の regularity から `A,B,f,a` の formation を、第二 premise の equality / application
generation から `b:RfType(A):Set_0` を回収して conclusion の `Acc` formation を作る。`run` と
`runCase` では明記された formation premiseに加え、`Terminates` と `RunInv` の regularity を使う。
他の case は規則の premise または帰納法の仮定から直接従う。

上の「同時強帰納法」を省略記法のままにしないため、帰納対象と全 terminal case を固定する。
導出 `h` の **origin trace** は次の有限木である。

```text
core(rule,h1,...,hn)
weak(h0,WF,o0)
conv(h0,hB,join,o0)
type-elem(hA,hs,oA)
type-sort(hA,oA)
lift-intro(hB,ht,hP,ot)
lift-weak(h,o)
```

`o0,oA,ot,o` は表示した strict premise の trace である。`lift-intro` と `lift-weak` は表示型を
convertible とみなす tag ではなく、前者は base typing `ht`、後者は入力の lifted typing `h` を
明示的に保存する。各 edge は元の導出木の strict premise へ向くので、trace は有限である。
`weak`、`conv`、`type-elem`、`type-sort`、`lift-intro`、`lift-weak` のどれでもない最後の規則が
`core` である。raw head と core rule の可能性は次で尽きる。

| raw head | sorting の core | typing の core |
| --- | --- | --- |
| sort / variable | axiom / variable を `type sort` で上げたもの | variable または `type elem` |
| product / lambda / application | `dep form` / `type sort` / `type sort` | `type elem` / `dep intro` / `dep elim` |
| `Proof` | `type sort` | `proof term` |
| `Power`, `Ty`, `Pred`, `=`, `exists` | 各 formation rule | `type elem` |
| subset | `type sort` | `subset form` |
| `Take` | `type sort` | `take set` または `take prop` |
| `RunStep`, `Acc`, `RfType` | 各 formation rule | `type elem` |
| `continue`, `finish`, `RfTerm`, `run`, `runCase` | `type sort` | 対応する typing rule |

ここで表の `type elem` / `type sort` は trace 上では detour tag であり、その strict premise の
core まで必ず進む、という意味である。provability の terminal rule は `provable`、`subset prop`、
`id intro`、`id elim`、`exists intro`、`take equal`、`acc intro`、`acc descent` の八つである。

regularity の constructor check は次の通りである。表中「IH」は該当 strict premise の
regularity を表す。

| rule 群 | conclusion の regularity を作るデータ |
| --- | --- |
| empty, start, weak, variable | premise の WF と IH。variable では WF の最後の宣言を反転する |
| axiom, dep form, power/type-lift/predicate formation | rule 自身の formation premise |
| dep intro | 第一 premiseの product formation |
| dep elim | function の product origin、argument typing、substitution |
| conversion | target sorting premise |
| type elem / type sort | 互いに書かれた sorting / typing premise |
| provable / proof term | typing premiseの IH / provability premiseの IH |
| subset form | `Power(A)` formation、subset intro / weak / prop は `B:Power(A)` の origin |
| equality form / intro / elim | 二項の typing、または binder body sorting と application formation |
| exists form / intro | `A` の sorting、またはその typing の IH |
| take set / prop | 明記された `T` sorting。take equal は take origin と `t:X` から equality formation |
| `RunStep`, `continue`, `finish`, reflection | 明記された `A,B` の formation と payload typing の IH |
| `Acc` form / intro / descent | formation premise。descent の `b` は equality/application originから回収 |
| `run`, `runCase` | `B::Comp` premise。略記された命題の sorting は残りの formation premiseから再構成 |

generation 側で origin trace の各 tagを処理する方法も固定しておく。

| origin tag | 回収した導出の処理 | 減少先 |
| --- | --- | --- |
| `weak` | premise の generation 出力すべてを同じ新宣言の下へ weaken する | weakened judgement の strict premise |
| `conv` | source typing の出力を保持し、target sorting と confluenceから表示型の raw joinを追加する。不活性 headでは joinの共通終点を反転して component joinを得る | conversion の source typing |
| `type-elem` | sorting premiseへ進み、必要なら sort axiomを付け直す | 保存された sorting premise |
| `type-sort` | typing premiseへ進み、表示型が sortである bridgeを記録する | 保存された typing premise |
| `lift-intro` | base typing、`B:Power(A)`、membership proofを別々に保存し、raw termの origin探索は base typingへ進める | base typing |
| `lift-weak` | 入力 lifted typingに保存された `lift-intro` または genuine subtype originまで進む。前後の型を convertible とはしない | 入力 lifted typing |
| `core` | raw headに対応する唯一の core ruleを反転し、その strict premiseをそのまま返す | 各 rule premise |

`conv` で target derivationへ再帰せず、既存の source childだけへ進むこと、`lift-intro/weak` で
非 convertible な二型を同一視しないことが、この同時帰納法の停止性と正しさに必要である。

これで WF の2 case（empty/start）と、sorting、typing、provability の
どの constructor も未処理にならない。generation は同じ trace を上から辿る。`conv` では common
reduct までの join を記録し、不活性 head なら共通 reduct の head も同じなので component の
joinability を得る。`lift-intro/weak` では base child へ進み、必要な表示型の head が現れるまで
進む。この探索は常に strict premise へ移るので、「lift intro と weak が交互に現れる」場合にも
停止する。従って本文で使った generation statement は独立の仮定ではなく、この有限 trace の
帰納的帰結である。

ここで canonical origin とは、上の trace に沿って weakening、conversion、type elem / type sort を
有限回剥がし、type lift intro / weak は coercion tag と base child を保存したまま、raw term の
outer constructor を作った最後の rule とその premise を記録する generation lemma である。
type lift intro / weak の前後の型を convertible とはしない。一般の type uniqueness は実際に偽である。

同時定理に含めた inversion の結論を正確に列挙する。各行は、左辺の導出から右辺の導出と
表示型間の join（必要な行だけ）を返す。

```text
(G-Pi)
Gamma |- f : (x:A)->B :: z
  => A::r,  Gamma,x:A::r |- B::q,  (r,q,z) in R

(G-Subset)
Gamma |- {x:B|P} : Power(A) :: Set_i
  => B::Set_i,  Gamma,x:B::Set_i |- P::Prop,  A≡B

(G-Take)
Gamma |- Take(X,T,f) : T :: s
  => X::Set_i, T::s, f:X->T::s,
     together with the premises of take-set or take-prop selected by s

(G-Continue)
Gamma |- u : RunStep(A,B) :: Comp
  and head(u)=continue_(C,D)
  => A≡C, B≡D, payload(u):C::Comp

(G-Finish)
Gamma |- u : RunStep(A,B) :: Comp
  and head(u)=finish_(C,D)
  => A≡C, B≡D, payload(u):D::Comp

(G-RfTerm)
Gamma |- RfTerm_C(a) : RfType(A) :: Set_0
  => RfType(A)≡RfType(C), a:C::Comp

(G-Acc)
Gamma |= Acc_(A,B)(f,a)
  => A::Comp, B::Comp, f:A->RunStep(A,B)::Comp,
     a:RfType(A)::Set_0

(G-Run)
Gamma |- run_(A,B)(f,a) : T :: Comp
  => T≡B and all five premises of run

(G-RunCase)
Gamma |- runCase_(A,B)(f,a,u) : T :: Comp
  => T≡B and all seven premises of run-case.
```

`(G-Pi)`--`(G-Take)` の `≡` は一般には alpha 同値へ強めない。`(G-Continue)`、`(G-Finish)`、
`(G-RfTerm)` の component equalityだけは、以下の Compute rigidity と reflection injectivity によって
alpha 同値へ強める。これが subject reduction で必要な generation の全出力である。□

> [!important]
> **補題（Compute type の rigidity）。** `Gamma|-A::Comp` なら `A` は一段 reduct を持たない。
> 従って `Gamma|-A::Comp`、`Gamma|-C::Comp`、`A≡C` なら `A` と `C` は alpha 同値である。

**証明。** `A::Comp` の canonical origin に関する帰納法を使う。`R` で result sort が `Comp` に
なるのは `(Comp,Comp,Comp)` だけであり、special formation で result sort が `Comp` になるのは
`RunStep` だけである。ここで type elem / type sort の往復は新しい型を作らず、canonical origin の
strict premise に戻す。さらに result sort が `CompKind` となる product rule や special formation
rule は存在しないので、`CompKind` に sort される型の core origin は axiom `Comp::CompKind` だけで
ある。従って application や lambda が conversion を介して「Compute 型そのもの」になる余地も
ない。以上から detour を除いた raw head は次のいずれかである。

```text
Compute type variable,
(x:A1)->A2       with A1::Comp and A2::Comp,
RunStep(A1,A2)   with A1::Comp and A2::Comp.
```

いずれの head にも root reduction はなく、immediate subterm は帰納法により normal なので `A` も
normal である。二つの well-sorted Compute type が convertible なら confluence により joinable だが、
両方とも normal なので共通 reduct は両者自身であり、alpha 同値である。□

Compute branch には type lift rule がないので、同じ origin induction から次も得られる。

```text
Gamma |- m:A::Comp,  Gamma |- m:C::Comp
=> A≡C, hence A =alpha C.                              (comp-type-unique)
```

ここで使う帰納法の measure は、二つの typing derivation の canonical origin の高さの和である。
conversion、weakening、type elem / type sort の detour があれば strict premise に進む。core case では
raw head が同じなので、variable は文脈中の宣言の一意性、lambda は body の帰納法、application は
function の product generation と argument の帰納法を使う。`continue`、`finish`、`run`、
`runCase` は raw annotation が component を固定し、残る型の違いは strict premise の帰納法と
product / `RunStep` head の injectivity に帰着する。Compute result sort の rule に type-lift
intro / weak はなく、別の非 convertible な表示型へ飛ぶ case は生じない。まずこの帰納法で
`A≡C` を得て、両型の Comp-sorting と直前の rigidity を適用すると alpha 同値まで強まる。

`RfType` は `Rf-Arrow` を持つので一般には不活性 head ではない。rigid な Compute type `A` に対して
その完全な reflection development `Q(A)` を

```text
Q((x:A1)->A2) = Q(A1) -> Q(A2)    if x notin FV(A2),
Q(A)           = RfType(A)         otherwise
```

と定める。第一式は右辺の二つの引数へ再帰する。Compute rigidity により `A` の内部には redex が
なく、`RfType(A)->*Q(A)` で `Q(A)` は normal である。また `Q` は構文について単射である。
nondependent product は Set product head に、それ以外は `RfType` head に写り、前者では二成分へ
帰納法を適用できるからである。従って confluence から

```text
Gamma |- A::Comp,  Gamma |- C::Comp,  RfType(A)≡RfType(C)
=> Q(A)=alpha Q(C) => A=alpha C.                         (rf-injective)
```

を得る。

以上と不活性な `RunStep` head の injectivity を canonical origin に適用すると、新しい root rule で
使う generation は次の強い形になる。

```text
Gamma |- RfTerm_C(a) : RfType(A) :: Set_0
=> A=alpha C and Gamma |- a:C::Comp,

Gamma |- continue_(C,D)(a) : RunStep(A,B) :: Comp
=> A=alpha C, B=alpha D and Gamma |- a:C::Comp,

Gamma |- finish_(C,D)(b) : RunStep(A,B) :: Comp
=> A=alpha C, B=alpha D and Gamma |- b:D::Comp.
                                                               (component-generation)
```

表示型が conversion や Set 側の type-lift detour を経る場合は、detour を origin まで剥がしてから
`(rf-injective)` を使う。Compute constructor の二式には type-lift detour がないので、
`(comp-type-unique)` と `RunStep` head の injectivityだけでよい。

> [!important]
> **補題（sort と term-sort の一意性）。** 同じ raw expression の二つの sorting
> `Gamma|-A::s`、`Gamma|-A::t` から `s=t`。同じ raw term の二つの typing
> `Gamma|-e:A::s`、`Gamma|-e:B::t` からも `s=t`。

**証明。** 二つの canonical origin の高さの和に関する強い帰納法。direct formation rule は
raw head により一意である。product result は `R` の表の関数性、sort axiom は `A` の関数性、
power、predicate、type lift、equality、exists は規則に書かれた sort で決まる。lambda は body
の低い term-sort uniqueness と `R`、application は argument と function の低い uniqueness と
`R` を使う。take set と take prop の混在は同じ `T` の低い sort uniqueness で排除される。
`RunStep`、`continue`、`finish`、`Acc`、`RfType`、`RfTerm`、`run`、`runCase` は raw head と
各規則に固定された result sort で決まる。type elem / type sort の往復は strict premise に
進むので高さが減る。type lift intro / weak も term-sort は base typing と同じ `Set_i` であり、
二導出を比較するときは保存した base child と相手側の originに帰納法を適用する。特に `Comp`、
`Set_i`、`Prop` の三群が同じ raw judgement に混在することは
ない。ここで type sort を `Gamma|-e:A::s` に適用できるのは表示型 `A` 自身が sort の場合だけで
あり、末尾の term-sort `s` を表示型と取り違えてはならない。□

一般の type uniqueness は使わない。例えば `t:A` とし、
`B={x:A | x=x}` とすれば `t:A` と `t:TypeLift(A,B)` が導けるが、二型は一般には
convertible でない。

### 3.4 subject reduction

> [!important]
> **定理（subject reduction）。** 次の四 clause が成り立つ。
>
> ```text
> (SR-Sort) Gamma |- M::s,      M->M' => Gamma |- M'::s,
> (SR-Term) Gamma |- e:A::s,    e->e' => Gamma |- e':A::s,
> (SR-Prov) Gamma |= P,         P->P' => Gamma |= P',
> (SR-Type) Gamma |- e:A::s,    A->A' => Gamma |- e:A'::s.
> ```

**証明。** まず前三 clauseを、source の WF / sorting / typing / provability derivation と一段
reduction の位置に関する同時強帰納法で証明する。recursive call の owner は常に source rule の
strict premiseである。regularity や generation が作った viewを使う場合、その viewを作った strict
premiseを owner と数え、生成後の target derivationの見かけの高さでは数えない。この call graphは
3.3節の origin trace の edgeの部分木なので有限である。`SR-Type` は前三 clauseの完成後、regularity
で `Gamma|-A::s` を得て `SR-Sort` を適用し、最後に primitive conversionを付ける系として導く。

weakening は reduction を一段下の term に反映して strict premiseへ帰納法を適用する。binder domain
の reductionには context conversion、bodyには binder 下の帰納法を使う。application argument の
reductionで表示型が `B[a/x]` から `B[a'/x]` に変わる場合は substitution compatibility と conversion
を使う。この conversionの両 endpoint sortingは `(G-Pi)` の codomain formation、argument の
`SR-Term`、3.1節の substitutionから作るので、`SR-Type` を先取りしない。

root beta は application と lambda の generation から body typing、domain typing、codomain
formation を回収して substitution する。`Pred/Subset` root は subset generation により
構文上の base `B` と predicate側の base `A` が convertible であることを回収する。
argument を `B` へ convert して target application を形成する。

take domain / codomain / function の reductionでは、function typing、existence、定値性 premise を
それぞれ subject reduction と context conversion で輸送する。定値性 proposition で `f` が二回
現れる場合は、一方ずつ進めた二つの一段 congruence を conversion で連結する。生成した target
導出へ帰納法を再適用せず、source の strict premise だけへ再帰するため整礎的である。

新しい root case は次の通りである。

- `Rf-Arrow` ではまず **Comp-sorting strengthening**

  ```text
  Gamma,x:A::Comp |- C::Comp,  x notin FV(C)
  => Gamma |- C::Comp
  ```

  を使う。この限定された strengthening は `C::Comp` の canonical origin に関する帰納法で
  証明できる。core rule で result sort が `Comp` になるのは、`(Comp,Comp,Comp)` による product、
  `RunStep` formation、または既存の Comp-sort variable であり、それぞれ raw subexpression に
  帰納法を適用できる。type elem / type sort、weakening の detour は strict premise まで剥がす。
  `run` の termination proof や subset introduction の membership proof は typing には現れるが、
  `C::Comp` の canonical formation origin には現れないので、この限定補題を妨げない。

  source の product generation と side condition から `Gamma|-B::Comp` を得て、fresh な
  `z:RfType(A)::Set_0` の下へ weaken する。reflection formation と
  `(Set_0,Set_0,Set_0) in R` により target の
  `RfType(A) -> RfType(B)` formation が得られる。freshness により capture は起きない。
- `RfTerm_(A->B)(f) @ RfTerm_C(a)` の `Rf-App` では、両 `RfTerm` と application の generation、
  `Rf-Arrow` から argument の表示型を `RfType(A)` まで戻す。`(component-generation)` から
  `A=alpha C` と `a:C:Comp` を得るので、通常の application rule で
  `f@a:B:Comp`、さらに reflection term rule で target
  `RfTerm_B(f@a):RfType(B):Set_0` を得る。source application にさらに outer conversion があった
  場合、application generation が元の表示型と `RfType(B)` の joinability を与えるので、最後に
  その conversion を付け直す。
- `run(f,a) -> runCase(f,a,f@a)` では、`u=f@a` と置く。`RunInv(f,a,u)` は equality reflexivity で
  provable なので、元の `Terminates(f,a)` と合わせて `run case` rule を適用できる。
- `runCase_(A,B)(f,a,continue_(C,D)(a')) -> run_(A,B)(f,a')` では constructor generation と
  `(component-generation)` から `A=alpha C`、`B=alpha D`、`a':C:Comp` を得る。従って alpha-renaming
  の範囲で `a':A:Comp` である。`RunInv` の右辺にある `continue_(C,D)(a')` も
  `continue_(A,B)(a')` と alpha 同値である。そこで `RunInv` を
  `Rf-App` と beta で変換すると、`acc descent` が要求する
  `RfTerm(f)@RfTerm(a) = RfTerm(continueFun)@RfTerm(a')` になる。従って
  `Terminates_(A,B)(f,a')` が得られ、外側の parameter を保った `run_(A,B)` rule を適用できる。
- `runCase_(A,B)(f,a,finish_(C,D)(b)) -> b` では constructor generation が `b:D:Comp` と
  `B=alpha D` を与えるので、target は直接 `b:B:Comp` を持つ。`run` / `runCase` の source typing
  が最後に別の表示型へ conversion されていた場合も、canonical origin まで剥がした conversion を
  target に付け直す。

annotation 内の compatible reduction も確認しておく。`RfTerm_A(m)` では二 case、すなわち
`A->A'` のときの `RfTerm_A'(m)` と、`m->m'` のときの `RfTerm_A(m')` がある。前者には表示型に
関する subject reduction、後者には payload typing の帰納法を使う（統一して、変化しない側にも
primeを付ければ `m':A':Comp`）。target の core type は `RfType(A')` だが、
compatible reduction から `RfType(A)->*RfType(A')` なので、必要なら元の表示型へ conversion できる。
`RunStep`、`continue`、`finish` の annotation も同じ componentwise argument である。`run` と
`runCase` では `A,B,f,a,u` の typing premise を帰納法で輸送し、reduction 後の `Terminates` と
`RunInv` は regularity と `(prov-conv)` で作り直す。`Acc` 自身と、これら二つの略記の引数内の
compatible reduction も同じである。

compatible closure の全位置について、実際に使う輸送を表にすると次の通りである。`SR` は strict
premise への帰納法、`CC` は context conversion、`PC` は `(prov-conv)`、`Conv` は typing
conversion である。core rule を作り直したとき表示型も一段進む場合は、最後の `Conv` で元の
表示型へ戻す。

| reduced raw constructor / position | target 導出の構成 |
| --- | --- |
| product domain / codomain | domain は `SR+CC`、codomain は binder 下の `SR` |
| lambda domain / body | product formationを前行で輸送し、body に `CC` / `SR`、最後に `dep intro` |
| application function / argument | function は `SR`。argument は `SR` と `B[a/x]≡B[a'/x]`、最後に `Conv` |
| `Proof(P)` | `P` の `SR` と `PC` から `Proof(P')`; displayed proposition は `Conv` |
| `Power(A)` | `A` の sorting `SR` と power formation |
| subset の base / predicate | base は `SR+CC`、predicate は binder 下の `SR`; `Power(A')≡Power(A)` で `Conv` |
| `Ty(A,B)` | `B:Power(A)` を各 component の `SR` と `Conv` で輸送し type-lift formation |
| `Pred(A,B,t)` | `B:Power(A)` と `t:A` を各 component の `SR` と `Conv` で輸送 |
| equality の左 / 右 | 共通表示型を generation で回収し、項の `SR` と `Conv` で equality formation |
| `exists(A)` | `A` の sorting `SR` |
| `Take(X,T,f)` | `X,T,f` を `SR`; existence と定値性は target の formation 後に `PC` |
| `RunStep(A,B)` | `A,B` の sorting `SR` |
| `continue`, `finish` | annotation と payload を `SR+Conv`; target `RunStep` を作り直す |
| `RfType(A)`, `RfTerm_A(m)` | annotation と payloadを `SR+Conv`; reflection ruleを再適用 |
| `Acc(A,B,f,a)` | 四 premiseを `SR+Conv` して formationを再適用 |
| `run(A,B,f,a)` | 四 formation/typing premiseを輸送し、`Terminates` を `PC` |
| `runCase(A,B,f,a,u)` | 五 formation/typing premiseを輸送し、`Terminates`,`RunInv` を `PC` |

outer derivation ruleの structural / value detourも、次の表で全て固定する。

| source の最後の rule | recursive call と target の作り方 |
| --- | --- |
| empty / start / axiom / variable | WF conclusion、sort、variable headには主式の root / compatible stepがないので vacuous。variable の表示型 reductionは後の `SR-Type` |
| weak sort / weak type | source の sorting / typing strict premiseに `SR-Sort` / `SR-Term` を適用し、同じ WF childで weakenし直す |
| conversion | term stepは source typing strict premiseへ進み、元の target sortingと conversionを付け直す。表示型 stepは `SR-Type` の系で処理する |
| type elem / type sort | 保存された sorting / typing strict premiseへ進み、同じ sort axiomまたは bridgeを付け直す |
| type-lift intro | base typingと membership provabilityの該当 strict premiseを輸送して introを再適用する |
| type-lift weak | 入力 lifted typingの strict premiseを輸送して weakを再適用する |
| dep form / intro / elim | 上の product / lambda / application 行。betaだけは root case |
| その他の formation / typing core rule | raw constructorの該当行で全 premiseを輸送し、同じ core ruleを再適用する。`Pred`、reflection、recursionの rootだけは既述の個別 case |

`SR-Prov` の八 terminal ruleは、proof premiseが conclusion syntaxから消える場合を含むので個別に
確認する。`PC` を使う行でも target propositionの sortingは表に書いた strict premiseだけから先に
構成し、source provability ownerへ subject reductionを再帰しない。

| provability terminal | target proposition / proof の構成 |
| --- | --- |
| `provable` | strict premise `p:P::Prop` の regularity viewを `SR-Sort` で `P'::Prop` へ進め、typing conversionで `p:P'::Prop`、最後に `provable` |
| `subset prop` | strict lifted typingを輸送し、`(G-Subset)` から target `Pred` formationを作って `subset prop` を再適用 |
| `id intro` | strict premise `a:A` を reduced operandへ輸送して target equalityを形成し、source reflexivityに `PC`。両 operandのどちらが進む場合も同じ |
| `id elim` | `a,b`、binder body、最後の proof premiseの該当 strict childを輸送し、target applicationを形成して `id elim` を再適用。outer betaなら substitutionで target sortingを作って `PC` |
| `exists intro` | strict witness typingとその regularityを輸送し、target typeへの typing conversion後に `exists intro` を再適用 |
| `take equal` | take typingの `(G-Take)` と `t:X` を輸送し、target equality formationを作って `take equal` を再適用 |
| `acc intro` | `A,B,f,a` の formation / typingと最後の binder propositionをその strict childで輸送し、target `acc intro` を再適用 |
| `acc descent` | 二つの strict provability premiseを輸送し、`(G-Acc)` と equality/application generationで target formationを作って `acc descent` を再適用 |

sort と variable には immediate subterm がない。上の二表により subset intro/weak/prop、equality
intro/elim、exists intro、take equal、acc intro/descent の proof premiseを含め、各 targetは source の
strict premiseから構成される。
これで全39 ruleの congruence caseと、beta、`Pred`、reflection二つ、recursion三つの root caseが
尽きる。生成した target 導出を再帰入力にはせず、常に source rule の strict premise にだけ
帰納法を適用するので同時帰納法は整礎的である。□

## 4. conversion を展開した有限導出

soundness の conversion case で「convertible な型は同じ意味」と言うには reduction の
意味保存が必要であり、reduction の beta case には subterm の typing soundness が必要になる。
これらを別々に先取りすると循環する。

この循環を避けるため、各 conversion use `A≡B` を、confluence が与える共通 reduct `C` と

```text
A=A0 -> A1 -> ... -> C,
B=B0 -> B1 -> ... -> C
```

に展開する。subject reduction により全中間点に同じ sort の sorting derivationを付ける。
また各 typing / provability derivation に、regularity が与える型 / proposition formation と
文脈 WF を付ける。このようなものを**正則導出**と呼ぶ。

「付随する証明も node と数える」だけでは循環がないことの証明にならないので、ここで使う
certificate を有限木の相互帰納族として固定する。対象は次の八種類である。

```text
DerivationPlus          WF / regularity / origin を保持する導出,
TypedStep               一段 reduction の source / target 導出と構成記録,
TypedPath               TypedStep の有限な順向き列,
TypedConv               同じ sort を持つ二式の typed convertibility,
TypedJoin               共通 reduct と左右の TypedPath,
SubstitutionPlus        3.1節の構造的 substitution の記録,
ContextConversionPlus   context conversion の構造的記録,
OriginPlus              core rule と structural detour の記録.
```

`DerivationPlus` の index は context と judgement、`TypedStep` の index は context、judgement の
種類、source、target、一段 reduction、`TypedPath` はその forward path、`TypedConv` と
`TypedJoin` は context、sort、二 endpoint、`SubstitutionPlus` と `ContextConversionPlus` は
輸送する object の種類と source / target index、`OriginPlus` は sorting または typing judgement
である。index は再帰的な certificate を含まず、raw term、sort、raw reduction、alpha-renaming、
common reduct はすべて index または有限な label であって recursive child ではない。

この八族を、以下の局所条件を満たす**有限な rooted tree の最小クラス**として定義する。従って、
constructor に渡せるのは既に構成済みの child だけであり、owner 自身を child や index に戻すことは
できない。`r` を primitive rule の一つの instance とすると、その premise 数 `n(r)` と各 premise
judgement は `system.md` の表から一意に決まる。raw constructor `K` と immediate position `j` に
ついても、その位置の binder 情報と残りの component は構文から一意に決まる。

| family | constructor と局所条件 | recursive child |
| --- | --- | --- |
| `DerivationPlus` | `DCore_r`。conversion 以外の rule instance `r` と同じ conclusionを持つ | `r` の `n(r)` 個の premise。conclusion が WF でなければ context WF、typing / provability なら regularity、sorting / typing なら originも持つ |
|  | `DConv`。source typing、target sorting、両型の `TypedConv` から元の conversion conclusionを持つ | source typing、target sorting、context WF、regularity、origin、`TypedConv` |
| `TypedStep` | `SRoot_k`。beta、`Pred`、reflection、recursion のいずれかの root tag `k` について3.4節の core constructionを再現する | source / target の `DerivationPlus` と、その construction が使う source の strict premise / origin |
|  | `SCong_(K,j)`。`K` の第 `j` immediate position の一段 stepを、残りの componentを固定して再構成する | source / target、位置 `j` の `TypedStep`、binder で必要な `ContextConversionPlus`、dependent application で必要な `SubstitutionPlus` / `TypedConv` |
|  | `SStructural_l`。weakening、conversion、type elem / type sort の detour `l` を一段剥がして戻す | source / target、detour の strict premiseの `TypedStep`、必要な context transport / typed conversion |
|  | `SValue_l`。type-lift intro / weak の detour `l` を base typingへ移して戻す | source / target、base typing の `TypedStep`、power / membership premiseとその transport |
| `TypedPath` | `PRefl`、または `PCons`。後者では step の target と残り path の source が同じ raw judgement | endpoint の `DerivationPlus`、または先頭 `TypedStep` と残りの `TypedPath` |
| `TypedJoin` | `Join(C)`。左右 path の target が同じ raw expression `C` | 左右の `TypedPath` と、それぞれの endpoint sorting derivation |
| `TypedConv` | `CJoin`。`TypedJoin` の二始点を endpoint とする | その `TypedJoin` |
| `SubstitutionPlus` | variable の hit / newer / older、binder、または rule `r` の構造をそのまま写す constructor | source / target object、および source の各 recursive child に対する substitution certificate。binder caseでは fresh renaming と延長 context の certificate |
| `ContextConversionPlus` | 置換位置での `CtxHere`、suffixを一つ進む `CtxThere`、または各 rule / path / origin constructorを写す constructor | source / target object、宣言型の `TypedConv`、suffix の declaration formation、source の各 recursive child の transport |
| `OriginPlus` | `OCore_r` | `r` の strict premise |
|  | `OWeak`、`OConv`、`OTypeElem`、`OTypeSort` | detour の strict premiseの originと、順に WF、`TypedConv`、sort premise、または typing premise |
|  | `OLiftIntro`、`OLiftWeak` | base typing の originと、intro では power / membership premise、weak では入力 lifted typing |

表中の「source / target object」はその constructor の index に書かれた judgement を持つ
`DerivationPlus`、または輸送対象として index に指定された八族の object である。target は source の
構造的変換で作ったものに限り、同じ target judgement を持つ任意の別導出を選んではならない。
また `SRoot_k` の tag は raw reduction の七 root rule、`SCong_(K,j)` は有限構文 `K` の各 immediate
position、`DCore_r` は conversion を除く38 primitive ruleに対して一つずつ存在する。`OCore_r` は
そのうち weak sort / type、type elem / sort、type-lift intro / weak を除いた core ruleだけに対応し、
除いた六種と conversion は表の専用 origin tagで表す。従って各 schema の分岐数と child 数は有限であり、
「残りの case」を表す暗黙の constructor はない。

名前付き構文を対象とするこの証明では primitive variable rule が context の最後の宣言だけを参照し、
古い変数は `weak type` の有限列として `DerivationPlus` と `OWeak` に記録される。このため独立な
`LookupPlus` は不要である。de Bruijn index を使う Lean 実装では lookup derivation 自体を輸送する
必要があるので、上の八族に `LookupPlus` を加えた九族になる。これは別構文での実装上の差であり、
自然言語証明で recursive child を省略してよいという意味ではない。

> [!important]
> **補題（certificate elaboration）。** 元の有限導出 `h` から、同じ judgement を結論に持ち、
> erasure が `h` である有限な `DerivationPlus(h+)` が存在する。また上の八族の各 certificate の
> 注釈を消すと、元の primitive rule または3.1--3.4節で示した admissible construction が得られる。

**証明。** 構成の主 measure を「source certificate の高さ」とし、同じ高さの中の stage を次の
一方向に固定する。

```text
annotated renaming / substitution
  -> ContextConversionPlus
  -> annotated one-step subject reduction (TypedStep)
  -> TypedPath
  -> TypedJoin -> TypedConv
  -> DerivationPlus の conversion node
```

`SCong` の dependent application や conversion detour が既存の `TypedConv` を使う場合、その
`TypedConv` は source の strict premiseから構成された、主 measure が真に小さい childである。
従って stage の右側にある objectを左側から参照してよいのは主 measureが減る場合だけであり、同じ
高さでの back edge は許さない。以下の構成はこの `(source height,stage)` の辞書式順序に従う。

元の導出高に関する帰納法で premise を先に elaborate する。高さ `n+1` の core ruleでは、高さ
`n` 以下の全 premise certificate が完成している。それらに3.1節の構造再帰を適用して WF、
regularity、substitution、context transportを作り、3.3節の有限 origin traceを作ってから
`DCore_r` で包む。ここでは新しく作った target derivationを一般の elaboration へ再投入せず、完成済み
childに有限個の rule wrapperを付けるだけである。

conversion rule の二 premiseを

```text
d  : Gamma |- e:T1::s,
h2 : Gamma |- T2::s
```

とする。帰納法で `d+`,`h2+` と、`d+` の regularity child
`h1+ : Gamma|-T1::s` が先に完成する。`T1≡T2` と confluence から raw common reduct `C` と有限な
forward path `T1->*C`, `T2->*C` を取る。各 path は、その時点で完成している endpoint sortingに
3.4節の annotated subject reductionを一段ずつ適用して `TypedPath` にする。各一段の再帰呼出しは
source certificate の strict premiseだけに向き、生成中の `DConv` には向かない。二 pathから
`TypedJoin`、それから `TypedConv` を作り、最後に一度だけ `DConv` で包む。従って conversion ownerは
どの path endpoint、step source / target、origin、transportの子孫にも現れない。

補助 certificate の構成も表の recursive child に関する構造帰納法である。`SubstitutionPlus` は
source ruleの strict child、`ContextConversionPlus` はそれに加えて短い context suffix、
`TypedStep` は source の strict premise、`TypedPath` は path の残り長についてだけ再帰する。
`TypedJoin` と `TypedConv` は既に完成した pathを包むだけである。従って外側の導出高を固定した
各段でも再帰 measure はそれぞれ

```text
source certificate の tree height,
context suffix の長さ,
source derivation の高さ,
path の残り長
```

のいずれかを真に減らし、上の構成順に逆らう back edge はない。これで八族の全 node は有限である。

注釈の消去は八族の同時構造帰納法である。`DCore_r` は `r` を再適用し、`CJoin` は左右の forward
pathから raw convertibilityを返し、`DConv` はそれを conversion ruleに使う。`SRoot/SCong` は
3.4節の target derivation、`SubstitutionPlus` と `ContextConversionPlus` は3.1節の admissible
derivation、`OriginPlus` はその underlying derivationを返す。各 recursive call は表で指定した
strict childへ進むので、erasure も停止する。□

この相互帰納族の node `o` に

```text
rank(o) = 1 + max { rank(c) | c is a recursive child of o }
```

（leaf では max を `0` とする）と定める。有限 tree なので rank は自然数であり、endpoint
derivation、path、typed conversion、origin、substitution、context transport はすべて owner より
真に小さい。複数の certificateを同時に比較するときの rank はそれらの rank の最大値とする。
5--6節でいう正則導出とは、この `DerivationPlus` のことである。

## 5. 導出に沿う解釈

同じ raw lambda、application、take が proof branch と data branch の双方に使われるため、
raw term だけから意味値を決めない。正則導出に沿って意味関係を定義する。

```text
SortDenotes(h,rho,a),
TypeDenotes(h,rho,Aval,eVal),
ProvDenotes(h,rho,p).
```

typing relation は型の sorting derivation の witness `Aval` も含む。provability relation は
regularity で付けた `P::Prop` の sorting valueをそのまま `p` とする。

context valuation は raw context だけでなく、その WF certificate に沿って定義する。WF の
constructor は empty と start だけなので、`h_empty` と
`h_start(hGamma,hA)`（ここで `hA : Gamma|-A::s` は start の第二 premise）に対して

```text
ValidCtx(h_empty, []),

ValidCtx(h_start(hGamma,hA), (rho,v))
  iff ValidCtx(hGamma,rho)
      and exists Aval,
            SortDenotes(hA,rho,Aval)
            and v in Aval.                              (valid-cons)
```

と構造再帰で定める。従って `Aval` は束縛され、`SortDenotes` に渡す導出も start node に保存された
特定の `hA` である。この定義は後の coherence を先取りしない。同じ raw context `Gamma` の二つの
WF certificate `hGamma,kGamma` に対する

```text
ValidCtx(hGamma,rho) iff ValidCtx(kGamma,rho)             (valid-coherence)
```

は6節 phase 0で証明する定理である。start/start caseでは prefix に phase 0の帰納法を適用し、二つの
declaration sorting child に低い rank の denotation existence と phase 5 coherenceを適用する。
従って一方の `(valid-cons)` witness `Aval` は他方でも同じ集合を表し、両方向が従う。WF の terminal
tag は empty/start だけなので、これで phase 0 の全 case が尽きる。

三つの関係は `DerivationPlus` の構造再帰で、以下の各行を「その場合に限る」という clause として
定義する。sorting nodeではその raw expression の値を、typing nodeでは regularity childが表す型値
`Aval` と ruleが表す項値 `eVal` を同時に記録する。weakening は valuation の末尾を捨てた premise
relation、binder は延長 valuationにおける body relationを使う。補助 fieldである WF、origin、
typed conversion自体には新しい意味値を割り当てない。

- sort axiom は `S_s`。
- variable は valuation の対応成分。
- type elem は sorting premise の値、type sort は typing premise の項値。
- product、lambda、application は `Pi_z`、`Lam_z`、`App_q`。
- proof mark と proposition-valued take は `bullet`。
- power、subset、predicate、type lift、equality、exists、set-valued take は2節の同名演算。
- `RunStep`、`continue`、`finish` は tagged sum と二つの injection。
- `RfType` と `RfTerm` は、対応する Compute type / term の値そのもの。
- `Acc` は `truth(aVal in Acc_fVal)`。
- `run` と `runCase` は2.5節の well-founded operation。
- conversion node `DConv(d,h2,c)` では

  ```text
  TypeDenotes(DConv(d,h2,c),rho,Aval,eVal)
    iff SortDenotes(h2,rho,Aval)
        and exists A1, TypeDenotes(d,rho,A1,eVal).
  ```

  すなわち source term の項値を保ち、target sorting の型値と組にする。`A1=Aval` は定義に入れず、
  `c:TypedConv(T1,T2)` に対する6節 phase 2と fundamental propertyから後で証明する。

provability node `h` では、保存された regularity childを `reg(h):Gamma|-P::Prop` として

```text
ProvDenotes(h,rho,p) iff SortDenotes(reg(h),rho,p)
```

と定める。従って provability の意味値の存在は regularity childの denotation existenceから従い、
その値が `1` であることだけが各 provability ruleの fundamental caseで証明すべき内容になる。

6節で existence と uniquenessを証明するまでは `[[M]]rho` は関数記号ではなく、対応する
`SortDenotes` / `TypeDenotes` relation の witnessを一つ固定したときの略記とする。witnessを使う
等式は常に、その witnessが存在する lower-rank childを明示してから用いる。phase 3と5の後は値が
一意になるので、通常の関数的な denotation notationとして読んでよい。

binder body の family は、各 `x in A` に対する body denotation の graphとして定める。6節の
低い-rank denotation existence と coherence により値は一意に存在するので、replacement で
graphを集合にできる。代表元の global choice は不要である。

renaming、weakening、substitution で構造的に対応させた二導出は、対応する valuation のもとで
同じ値を表す。これは導出の構造帰納法で、binder では fresh variable、application では
semantic substitution

```text
[[B[a/x]]]rho = [[B]](aVal,rho)
```

を使う。この段階では構造的に対応する witness だけを比較し、任意の別導出との一致を
仮定しない。

さらに、意味値は raw expression の自由変数にしか依存しないという **support 補題**を同時に
示す。`run` の termination proof、subset introduction の membership proof など、規則の premise に
だけ現れて raw term に保存されない proof は導出可能性を制限するが、項値を定義する clause の
引数にはならない。従って、このような proof が余分な context variable を使っていても raw term
自身の値はその variable に依存しない。この補題は `Rf-Arrow` の非依存 codomain の意味保存にも
使う。

## 6. soundness と coherence

対象となる正則導出と補助 certificate の有限 tupleについて、4節で定めた最大 rank に関する強い
帰納法で次を同時に証明する。

1. 同じ raw context `Gamma` の二つの WF certificate `hGamma,kGamma` について
   `ValidCtx(hGamma,rho)` と `ValidCtx(kGamma,rho)` は同値である。
2. 各 sorting、typing、provability denotation が存在する。
3. sorting value は `D_s` に入り、typing は `Aval in D_s` と `eVal in Aval` を満たし、
   provability value は `1` である。
4. 注釈された一段 reduction、finite path、typed join / typed conversion の両端は同じ値を表す。
5. 同じ judgement の二つの正則導出、および同じ導出の二 witness は同じ値を表す。さらに、
   同じ raw term の二つの typing は、表示型が異なっていても同じ項値を表す。また
   `Gamma|-M::s` と `Gamma|-M:s::t` の sorting / typing bridge も同じ `M` の値を表す。

帰納法の第一・第二 measure は `(rank,phase)` の辞書式順序とし、同じ rank の phase を

```text
0 validity / WF coherence,
1 substitution and context-transport invariance,
2 step / path / join / conversion invariance,
3 denotation existence,
4 fundamental property,
5 coherence
```

の順にする。phase 0--2 が denotation や coherence を必要とする場合、参照先は certificate に
格納された strict child なので rank が減る。conversion の fundamental caseは owner より低い
`TypedConv` 内の `TypedJoin` の phase 2 と endpoint の phase 5 だけを使う。rankを保つ後向き参照は phase 5 の
coherence が同じ rank の完成済み phase 4 を使う場合だけであり、provability の二値が双方 `1` と
示す case もこれに含まれる。従って辞書式 measure はすべての呼出しで真に減少する。

coherence の origin-pair case もここで閉じておく。二つの `OriginPlus` の tag の順序対に対して、
次の決定的な簡約を行う。

1. 片側が `OWeak` なら tail を捨て、support とその strict child の coherenceへ進む。
2. 片側が `OConv` なら保持された `TypedConv` 内の join の phase 2で型値を common endpointへ移し、その strict
   source childとの coherenceへ進む。
3. `OTypeElem` と `OTypeSort` は、それぞれ保存した sorting / typing childへ進む。同じ raw `M` の
   sorting と `M:s::t` の typing が向き合った場合が bridge clauseで、両 clauseは定義上同じ
   `M` valueを返す。
4. `OLiftIntro` は保存した base typingへ進む。`OLiftWeak` は lifted type の originを一段進め、
   `OLiftIntro` に到達すればその base childへ、genuine subtype variable/application に到達すれば
   その core valueへ進む。どちらも項値を変更しない。
5. 両側が `OCore` なら raw outer headを比較する。sort、variable、product、lambda、application、
   `Proof`、集合 constructor、`Take`、再帰 constructor の各 headは互いに異なる。同じ headでは
   3.3節の core 表により同じ rule tagである。ただし `Take` の set/prop 二 ruleは term-sort
   uniquenessで混在せず、provabilityの八 terminal ruleは phase 4により値がすべて `1` なので
   直接一致する。残る値は strict premiseの coherenceと2節の演算の外延性で一致する。

各1--4は少なくとも一方の origin trace の strict childへ進み、5は rule premiseへ進むので、
origin の高さの和が真に減少する。正確な全 measure は

```text
(maximum certificate rank, phase,
 origin-height-left + origin-height-right)
```

の辞書式順序とし、第三成分は phase 5以外では `0` とする。同 rank の fundamental propertyを使う
coherence callでは phaseが `5` から `4` へ減り、detourを剥がして coherenceを再帰するときは第三
成分が減る。従って coherenceで未処理の tag pairや非減少 callはない。

主要 rule case を確認する。

- weakening は `ValidCtx` の `(valid-cons)` から得る tail と semantic weakening。
- variable は context validity の対応成分。
- type elem / type sort は `a in S_s iff a in D_s`。
- product は universe closure。
- lambda の result sort が `Prop` なら全 fiber が `1` なので proof product が `1`。
  それ以外は graph introduction。
- application の result sort が `Prop` なら function membership から全 fiber が `1`。
  それ以外は graph elimination。primitive rule にない `B[a/x]::q` は3.3節で導いた sorting と
  semantic substitution を使う。
- conversion は注釈された二 path の reduction invariance と共通終点の coherence。
- provability / proof mark は `(proof_mem)`。
- power、subset、predicate、type lift は powerset、separation、subset membership。
- equality formation / reflexivity は truth law。
- equality elimination は equality premiseから `aVal=bVal` を得る。最後の premiseを beta と
  semantic substitution で `P(aVal)=1` にし、等しい値を代入して `P(bVal)=1`、逆向き beta で
  conclusionへ戻す。
- exists introduction は項値を witness にする。
- `RunStep` formation と二つの introduction は `U_0` の tagged-sum closure と injection の
  membership law。
- reflection formation / typing は `Comp` と `Set_0` がともに `U_0` であることと恒等解釈。
- `acc intro` の最後の premise は、proof product と equality の意味を展開すると
  `(acc-intro-law)` の仮定になる。`acc descent` は `(acc-descent-law)` そのものである。
- `run` では termination premise が `aVal in Acc_fVal` を与えるので、well-founded recursion の
  値が `BVal` に入る。`runCase` ではさらに invariant が `uVal=app(fVal,aVal)` を与える。
  `uVal` の tag で場合分けし、continue の場合は accessibility の descent、finish の場合は
  payload membership を使って、どちらも値が `BVal` に入る。

take set では existence premise から `x0 in XVal` を得る。function typing から `fVal` は
`XVal` から `TVal` への graph である。二重 proof product の定値性 premiseを展開すると、

```text
forall x,y in XVal, app(fVal,x)=app(fVal,y).
```

`y0=app(fVal,x0)` とすれば `y0 in TVal` で image は `{y0}`。`(take-law)` により
`Take(XVal,TVal,fVal)=y0 in TVal`。

take prop では function typing から proof product が `1`、従って各 `x in XVal` で
`TVal=1`。existence で一つの `x` を得て `TVal=1`、よって `bullet in TVal`。

take equal では第一 premise の canonical take origin から同じ `X,T,f` の take set premises を
回収する。上の議論で `fVal` が `XVal` 上の定値 graph と分かり、第二 premiseから
`tVal in XVal`。従って `(take-law)` により

```text
Take(XVal,TVal,fVal)=app(fVal,tVal),
```

なので equality value は `1`。異なる generation / formation derivation が与える値は低い rank
の coherence で合わせる。

phase 2 の非 root constructor は次で一括してよい。`SCong` の各 premise stepは strict childなので、
帰納法により対応する argument valueが等しい。binder bodyは全 `x in AVal` で pointwise に等しく、
従って replacementで作った family graphも外延性により等しい。2.5節末尾の外延性から `Pi`、
`Lam`、`App`、集合 constructor、`Acc`、`Run`、`RunCase` の結果値が等しい。`SContext` は phase 1の
context-transport invariance、`SLift` は base typingの値をそのまま使う。`PRefl/PCons` は path長の
帰納法、`Join` は左右 pathの終点が同じ raw expressionであることと、その endpoint derivationの
低い-rank coherenceを使う。従って phase 2で個別に残るのは以下の root caseだけである。

reduction invariance の root beta は、data branchなら graph beta と semantic substitution、
proof branchなら両辺が `bullet` であることを使う。どちらの branch かは3.3節の term-sort
uniqueness で一意に決まり、`Comp` branch は data branch に含まれる。

`Pred/Subset` reduction では generation から base `A` と `B` の denotation が等しく、
argument value が `B` に属することを得る。従って source value は

```text
truth(tVal in BVal and PVal(tVal)=1)=PVal(tVal),
```

これは target application の graph beta value に等しい。

reflection の root reduction では、`RfType` / `RfTerm` の恒等解釈と `(rf-law)` を使う。
`Rf-App` の異なる annotation `A,C` は typed source の generation と `(rf-injective)` により同じ
denotation を持ち、argument value は function graph の domain に入る。`Rf-Arrow` の非依存性により
codomain family は定値であり、fresh binder の valuation は source の意味に影響しない。

recursion の三つの root reduction は `(run-laws)` で意味を保存する。continue case では typed
source の generation から `AVal=CVal`、`BVal=DVal` を得るので、内側の
`continue_(C,D)(a')` の値は外側の tagged sum でも `(0,a'Val)` である。invariant から
`app(fVal,aVal)=(0,a'Val)` が得られ、termination から
`a'Val in Acc_fVal` を得る。従って target の `Run(fVal,a'Val)` は default branch ではなく
well-founded recursion の値である。target に外側の `A,B` を採用したので、source と同じ `Run`
演算になる。finish case でも `BVal=DVal` であり、invariant から current step が `(1,bVal)`
であるため source value は target `bVal` に等しい。`run` の unfold rule は `Run` の定義式そのものである。

coherence では、二導出の weakening、conversion、type elem / type sort、type lift intro / weak
を canonical origin まで有限回剥がす。conversion は低い rank の path invariance、type lift
intro / weak は共通の base typing が表す項値に帰着する。同じ outer constructor の二つの core
rule は、strict premise の coherence と `Pi`、`Lam`、`Subset`、`Acc`、`Run` の外延性で一致する。
同じ raw term が異なる表示型を持つ場合も、二つの canonical origin に同じ議論を行う。term-sort
uniqueness により proof branch と data branch が混在せず、一般の type uniqueness は必要ない。
provability の二導出は fundamental property により命題値がともに `1` なので一致する。これで
上の5の cross-typing case を含む全 coherence case が閉じる。

### 6.1 fundamental property の全39 case

「主要 case」以外を暗黙に残さないため、各 primitive rule の conclusion value と、それを保証する
2節の lawを一行ずつ示す。`A0,e0` などは対応する premise の値である。

| # | rule | conclusion value と membership / truth の理由 |
| ---: | --- | --- |
| 1 | empty | `h_empty` に対し空 tuple は定義から `ValidCtx(h_empty,[])` |
| 2 | axiom | `[[s1]]=S_s1 in D_s2` は sort axiom closure |
| 3 | start | `A0 in D_s` と `v in A0` を加えた tuple が validity の定義を満たす |
| 4 | weak sort | tail valuation を捨てる semantic weakening と support |
| 5 | weak type | 同上。型値と項値の membership も不変 |
| 6 | variable | valuation の末尾 `v` は validity の定義により `v in A0` |
| 7 | conversion | source membership、左右 path の phase 2、common endpoint の phase 5から `A0=B0` |
| 8 | dep form | `Pi_z(A0,B0)` の各 sort case は2.2節の universe / truth closure |
| 9 | dep intro | `z=Prop` なら `bullet`、それ以外は `Lam_z(A0,m0)` の graph-introduction law |
| 10 | dep elim | semantic substitution と `App_q` の elimination lawにより fiber membership |
| 11 | type elem | `[[s]]=S_s` と `A0 in D_s`、および `D_s=S_s` の membership equivalence |
| 12 | type sort | typing premiseの項値をそのまま使い `A0 in D_s` |
| 13 | provable | typing membership `p0 in P0` と `(proof_mem)` から `P0=1` |
| 14 | proof term | `P0=1` なので `bullet in P0` |
| 15 | power set form | `A0 in U_i` なら `Power(A0) in U_i` |
| 16 | power set intro (`Ty` form) | `B0 in Power(A0)` から `B0 subset A0` かつ `B0 in U_i`; `[[Ty(A,B)]]=B0` |
| 17 | predicate | `truth(t0 in B0) in {0,1}` |
| 18 | subset form | `Subset(A0,P0) subset A0`、従って `Subset(A0,P0) in Power(A0)` |
| 19 | subset intro | `Pred(A,B,t)=1` から `t0 in B0=[[Ty(A,B)]]` |
| 20 | subset weak | `t0 in B0` と `B0 subset A0` から `t0 in A0` |
| 21 | subset prop | `t0 in B0` なので `truth(t0 in B0)=1` |
| 22 | id form | `truth(a0=b0) in {0,1}` |
| 23 | id intro | `truth(a0=a0)=1` |
| 24 | id elim | equality premiseで `a0=b0`; semantic substitutionで `P0(a0)=1` を `P0(b0)=1` へ移す |
| 25 | exists form | `truth(exists x in A0) in {0,1}` |
| 26 | exists intro | witness `e0 in A0` により existence value は `1` |
| 27 | take elim set | existence、graph typing、定値性から image は singleton; `(take-law)` で値は `T0` に属す |
| 28 | take elim prop | existenceで `x in X0`; proof product typingから `T0=1`; 値 `bullet in T0` |
| 29 | take equal | take-set origin と `t0 in X0` から `Take(X0,T0,f0)=app(f0,t0)`、従って equality は `1` |
| 30 | run step form | tagged finite sum `RunStep(A0,B0) in U_0` |
| 31 | continue intro | `a0 in A0` から `(0,a0) in RunStep(A0,B0)` |
| 32 | finish intro | `b0 in B0` から `(1,b0) in RunStep(A0,B0)` |
| 33 | acc form | `truth(a0 in Acc_f0) in {0,1}` |
| 34 | acc intro | 最後の premiseを展開すると `acc-intro-law` の左辺、その lawで value は `1` |
| 35 | acc descent | equality premiseは `b0 <_f0 a0`; `acc-descent-law` で value は `1` |
| 36 | reflection type | `A0 in D_Comp=U_0=D_Set_0`、かつ `[[RfType(A)]]=A0` |
| 37 | reflection term | `m0 in A0`、かつ `[[RfTerm_A(m)]]=m0` |
| 38 | run | terminationから `a0 in Acc_f0`; well-founded recursion の result-membership lemmaで `Run(f0,a0) in B0` |
| 39 | run case | invariantで `u0=app(f0,a0)`; tag場合分けと `run-laws` により `RunCase(f0,a0,u0) in B0` |

各行が phase 4 で参照する premise は `DCore/DConv` の strict childなので rank が小さい。
7番だけは `DConv` に格納した `TypedConv` と、その中の `TypedJoin` の phase 2、endpoint の phase 5を
参照するが、いずれも `DConv` の recursive descendantなのでやはり rank が小さい。phase 5 の coherence では、同じ
番号同士なら各 premise の coherenceへ、異なる origin tagなら `OWeak`、`OConv`、`OTypeElem`、
`OTypeSort`、`OLiftIntro`、`OLiftWeak` の strict childへ進む。provability同士はこの表の phase 4で双方が `1` と
分かる。従って列挙したどの行にも同 rank の phase 5への循環はない。

以上で `system.md` の PTS / WF 12規則、provability 2規則、power / subset / type lift 7規則、
equality 3規則、choice 5規則、一般再帰 10規則がすべて尽きる。

### 6.2 phase 0--3 と phase 5 の全 case

6.1節の39行は phase 4 の primitive rule caseを尽くす。この節では残る phaseが4節のどの
constructorで尽きるかと、各 recursive callの減少先を固定する。

phase 0 の WF / validity coherenceは次の二 caseだけである。同じ raw contextについて empty と
startが向き合うことはない。

| 左右の WF outer tag | validity の一致 | recursive call |
| --- | --- | --- |
| empty / empty | 両方とも空 tupleだけを valid とする | なし |
| start / start | prefix validityを合わせ、declaration sortingの二 witnessを phase 3 / 5で同じ集合に合わせ、`(valid-cons)` を両方向に使う | 二つの prefix WF と declaration sorting。いずれも start ownerの strict child |

phase 1 は `SubstitutionPlus` と `ContextConversionPlus` の constructor、および weakening / supportを
処理する。構造的に対応する二導出だけを比較するので、任意の別導出に対する coherenceは使わない。

| phase 1 constructor 群 | semantic invariance | recursive call / measure |
| --- | --- | --- |
| renaming の variable hit / miss | valuation componentのrenameと一致 | context positionが短くなる |
| substitution の variable hit | `u` の typing witnessを代入先の変数値として使う | argument typing child |
| substitution の newer / older variable | valuation lookupを一つずらす、または保つ | context suffixが短くなる |
| substitution の binder | binderをfreshにし、`(rho,xVal)` 上で body substitutionを使う | source binder child |
| `SubstRule_r` | `r` の各 premise valueにIHを使い、同じ2節の演算を適用する | source nodeの各 recursive child |
| `CtxHere` | declaration型の `TypedConv` の phase 2で二型値を合わせ、同じ `v` の membershipを移す | 保存された typed conversion child |
| `CtxThere` | prefix validityと最後の declaration denotationを順に輸送する | context suffixが短くなる |
| rule / step / path / origin の context transport | 各 recursive fieldを同じ target contextへ写し、constructorを再適用する | source certificateの strict child |
| weakening / support | valuationのunused tailを捨てる。raw expressionにない変数は意味演算の引数に現れない | weakening originまたはraw expressionの構造 |

phase 2 の constructorは `TypedStep` 四種、`TypedPath` 二種、`TypedJoin`、`TypedConv` で尽きる。

| phase 2 constructor | equality の理由 | recursive call |
| --- | --- | --- |
| `SRoot_k` | beta、`Pred`、`Rf-Arrow`、`Rf-App`、run unfold、continue、finishの七 case。各 lawは6節前半の phase 2 root 計算 | source / targetに保存された strict premiseの phase 3--5 |
| `SCong_(K,j)` | position `j` の値をIHで合わせ、binder familyはpointwise equality、その他は2節の演算の外延性 | child `TypedStep`、必要な substitution / context transport |
| `SStructural_l` | weak / conversion / type-elem / type-sortの低い stepへ移り、transport invarianceを使う | strict premise step と phase 1 child |
| `SValue_l` | type-lift intro / weak はbase termの項値を変えない | base typing step |
| `PRefl` | 同じ witness | endpoint derivation |
| `PCons` | 先頭 stepの等式と残り pathの等式の推移性 | `TypedStep` と短い `TypedPath` |
| `Join(C)` | 左右 endpointは同じ raw `C`; 二 endpoint derivationのphase 5で値を合わせる | 二 path と endpoint derivation |
| `CJoin` | 保持した join の二始点の等式をそのまま返す | `TypedJoin` |

`SRoot_k` の七 caseは6節前半で個別に計算済みであり、`SCong_(K,j)` は4節で全 raw constructorと
全 immediate positionに一 tagを置いたので、phase 2に暗黙の congruence caseは残らない。

phase 3 の denotation existenceは `DerivationPlus` の outer tagで次のように分割できる。

| phase 3 outer tag / rule 群 | witness の構成 | recursive call |
| --- | --- | --- |
| axiom / variable / weakening | `S_s`、valuation component、またはpremise witness | WF / premise child |
| product / lambda / subset binder | validな各 `xVal` にbodyのphase 3を使う。phase 5の一意性からfunctional relationとなりreplacementでfamily graphを得る | domain / body child。binder ownerより低い rank |
| application | function / argument witnessとsemantic substitutionから `App_q` | function、argument、codomain substitution child |
| proof mark / proposition take | `bullet` | regularity / provability child |
| power、type lift、predicate、equality、exists、set take | child witnessに2.3--2.4節の全域演算を適用 | 対応する formation / typing premise |
| `RunStep`、tag、reflection、`Acc` | tagged sum、injection、恒等値、`truth` | 対応する strict premise |
| `run` / `runCase` | 2.5節で malformed / inaccessible inputにも `0` を返すよう全域化した `Run` / `RunCase` | `A,B,f,a,u` の strict premise |
| type elem / type sort | 保存された sorting value / typing item value | detour の strict premise |
| type-lift intro / weak | base typingのitem valueと、各 ruleが作る表示型 value | base typing、power、membership child |
| `DConv` | target sorting witness `Aval` と source typing witness `eVal` を定義通り組にする | source typing と target sorting。membershipはまだ主張しない |
| provability node | `reg(h)` の sorting witness | regularity child |

ここでは演算値の存在だけを示し、universe membershipや truthはphase 4へ送る。従って phase 3が
phase 4を先取りすることはない。binder familyの一意性に使うphase 5はbody certificateのrankが低い。

最後に phase 5 の全 origin pairを監査する。tagを

```text
C=OCore, W=OWeak, V=OConv, E=OTypeElem,
S=OTypeSort, I=OLiftIntro, L=OLiftWeak
```

と略記する。次の対称表の記号が、各順序対で最初に適用する簡約を表す。

| left \ right | C | W | V | E | S | I | L |
| --- | --- | --- | --- | --- | --- | --- | --- |
| C | `core` | `weak` | `conv` | `elem` | `sort` | `intro` | `lift-weak` |
| W | `weak` | `weak` | `weak` | `weak` | `weak` | `weak` | `weak` |
| V | `conv` | `weak` | `conv` | `conv` | `conv` | `conv` | `conv` |
| E | `elem` | `weak` | `conv` | `elem` | `bridge` | `elem` | `elem` |
| S | `sort` | `weak` | `conv` | `bridge` | `sort` | `sort` | `sort` |
| I | `intro` | `weak` | `conv` | `elem` | `sort` | `intro` | `lift-weak` |
| L | `lift-weak` | `weak` | `conv` | `elem` | `sort` | `lift-weak` | `lift-weak` |

`weak` はその側の tailを捨てて supportを使い、`conv` は保存した typed conversionのphase 2を使って
source originへ、`elem` / `sort` は対応する strict premiseへ進む。`bridge` は sortingと
`M:s::t` typingが定義上同じ `M` valueを返す caseである。`intro` はbase typingへ、`lift-weak` は
入力 lifted typingを一段進める。表の優先順位は `weak > conv > elem/sort > lift > core` なので、
全49順序対を重複なく覆う。同じ優先順位の tag が両側にある対角成分では左側を先に簡約すると
定めるので、「最初に適用する簡約」も一意である。

`core/core` では同じ raw outer headを比較する。同じ headの rule tagは3.3節の core 表で一意で、
`Take` の set / propだけは term-sort uniquenessで分離される。sorting / typingでは対応する strict
premiseのphase 5と2節の外延性へ進む。product、lambda、subsetのbinder caseでは、まずdomain
premiseのphase 5で共通の `AVal` を得る。各 `xVal in AVal` について `(valid-cons)` とphase 0で二つの
延長 contextを合わせ、body childのphase 5を適用するのでfamilyはpointwiseに一致し、replacementと
外延性から同じ graphになる。同じ raw termで表示型だけが異なる cross-typingでも、項値を
作る raw constructorとterm-sortは同じなので同じ議論が使える。provabilityの八 terminal tagは
phase 4で双方の値が `1` と分かる。二 witnessの一意性は同じ originをこの表の対角成分で比較する
special caseである。

`core` は両 rule premiseへ、他の記号は少なくとも一方の origin strict childへ進むので、6節冒頭の
`(rank,phase,origin-height-sum)` が真に減る。以上で phase 0--5 の全 constructorが列挙され、6.1節の
39行がphase 4だけを監査していた不足はない。

> [!important]
> **Soundness。** judgement の正則導出に保存された WF certificate を `hGamma` とする。
> `ValidCtx(hGamma,rho)` のもとで
>
> ```text
> Gamma |- A::s       => [[A]]rho in D_s,
> Gamma |- e:A::s     => [[A]]rho in D_s and [[e]]rho in [[A]]rho,
> Gamma |= P          => [[P]]rho=1.
> ```

元の導出を正則化して上の同時定理を適用する。同じ raw `Gamma` の別の正則化を選んだ場合、valuation
の valid 性は `(valid-coherence)`、各意味値は phase 5 coherenceにより一致する。従って boxed statement
では「`Gamma` の valid valuation」を、任意の（同値には、ある）WF elaboration `hGamma` に対して
`ValidCtx(hGamma,rho)` となること、と導出選択に依存せず略記できる。

### 6.3 一般再帰が偽命題を作らない理由

`f@a ->* continue(a)` となる `f,a` に対し、operational rule だけを見れば自己ループ

```text
run(f,a) -> runCase(f,a,f@a) ->* runCase(f,a,continue(a)) -> run(f,a)
```

は可能である。しかし、この raw term に `run` typing を与えるには `Acc_F(a)` の証明が要る。
集合モデルで自己ループは `a <_F a` を意味する。`Acc_F` を `Phi_F` の transfinite iteration で
構成し、`a` が初めて現れる stage を `alpha+1` とする。`a <_F a` なら `Phi_F` の定義により
同じ `a` が stage `alpha` 以前に既に属さなければならず、stage の最小性に反する。従って
`a notin Acc_F` であり、その命題値は `0` である。soundness により、有限の
`acc intro` / `acc descent` 導出がこの値を `1` にすることはできない。

従って追加されたものは「任意の不動点」ではなく、「Set 側で accessibility が証明された
deterministic transition の well-founded evaluator」である。ここで示したのは Prop の
soundness であって、well-typed term の強正規化までは主張しない。

## 7. `falseProp`

空文脈で `Prop::PropKind`。`P:Prop::PropKind` を文脈に加えると variable rule と type sort から
`P::Prop`。`(PropKind,Prop,Prop) in R` により

```text
falseProp=(P:Prop)->P :: Prop.
```

標準 formation derivation の空 valuation で

```text
[[falseProp]]
  = Pi_Prop(S_Prop, P |-> P)
  = truth(forall P in {0,1}, P=1)
  = 0,
```

最後は `0 in {0,1}` かつ `0!=1` による。別の formation derivation も coherence により同じ
値を持つ。

空文脈で `falseProp` が provable と仮定すると、定義から `ValidCtx(h_empty,[])` なので soundness から
`[[falseProp]]=1`。上の計算は `0` を与え、`0!=1` に反する。

また `Gamma` を空として `t:falseProp::s` があると仮定する。regularity と sort uniqueness から
`s=Prop`。soundness と formation coherence から

```text
[[t]] in [[falseProp]]=0,
```

となるが空集合に要素はない。従ってそのような項も存在しない。以上で、Soundness から
目標とする主定理が従うことが示された。□

従って、ZFC と1節の universe tower の存在が無矛盾であることに相対して、`system.md` の体系も、
`falseProp` の provability および inhabitance を矛盾とする意味で無矛盾である。

## 8. constructor 監査と結論

集合モデル側では、各 primitive rule を2節の law に代入すると membership が保存される。
とくに一般再帰については、`Acc_F` の段階 rank が continue edge ごとに真に減少するため、
無条件の不動点演算を導入してはいない。構文側と意味側の有限帰納法について、使った対象、
decreasing measure、terminal caseを最後に対応づける。

### 8.1 raw reduction

3.2節の `=>>` は全 constructor の congruence と八つの root schema（beta、`Pred` の primitive-only
と primitive-plus-beta、`Rf-Arrow`、`Rf-App`、`run`、continue、finish）を持つ。二つの `Pred`
schemaを分けたので、primitive step の inclusion と complete development の triangle の双方が
成り立つ。帰納 measure は parallel derivation の高さと source term の構造であり、
`parallel-subst` と `N=>>M*` の全 root caseは3.2節に列挙した。従って raw confluence は証明済みの
補題であり、後段の仮定ではない。

### 8.2 syntactic metatheory

3.3節では `core/weak/conv/type-elem/type-sort/lift-intro/lift-weak` からなる有限 origin traceを定義し、
raw headごとの terminal coreと regularity の全 rule群を表にした。trace edgeは常に strict premiseへ
向くので導出高が減る。type-lift edgeを conversion edgeと同一視していないため、一般には偽である
type uniquenessを使っていない。この traceから product、subset、take、reflection、tagged
constructor、run / runCase の必要な inversionが得られる。

3.4節では全 compatible positionを輸送表で、全 root ruleを個別に処理した。recursive callは source
ruleの strict premiseだけに行い、生成した target derivationへは行わない。従って regularity、
generation、sort / term-sort uniqueness、Compute rigidity、component generation、subject reduction
は相互に循環せず閉じている。

### 8.3 annotated soundness

4節の名前付き構文に対する有限な証明対象は次の八種類で尽きる。

```text
DerivationPlus, TypedStep, TypedPath, TypedConv, TypedJoin,
SubstitutionPlus, ContextConversionPlus, OriginPlus.
```

Lean の de Bruijn 構文では、これに変数 lookup の構造的輸送を記録する `LookupPlus` を加える。
名前付き構文では古い変数の使用が primitive variable と `weak type` の列に既に展開されているため、
この第九の object は4節の定理には不要である。

4節では各 constructor schemaと recursive childを明記した。構成順は

```text
annotated renaming/substitution
  -> context transport
  -> annotated one-step subject reduction
  -> finite path
  -> typed join -> typed conversion
  -> 元の有限導出から DerivationPlus への elaboration
```

であり、conversion ownerをその path endpointとして使わない。この有限木について全 recursive
childより1大きい rankを、6節では `(rank,phase,origin-height-sum)` の辞書式順序を使った。同一 rank の phase は

```text
validity -> transport -> step/path invariance
         -> denotation existence -> fundamental property -> coherence
```

の順である。6.1節の39行は phase 4 の各 fundamental caseについて参照先と集合論的 lawを示す。
6.2節は phase 0--3 の全 constructorと phase 5 の全49 origin-pairを列挙し、coherence の
origin-pair簡約では origin高さの和が真に減ることを示す。従って soundness の証明に循環はない。

> [!important]
> **相対無矛盾性定理。** ZFC と1節の Grothendieck universe tower を仮定する。このとき
> `system.md` の有限導出について、空文脈では
>
> ```text
> not (empty |= falseProp),
> not (exists t s, empty |- t:falseProp::s).
> ```
>
> **証明。** 4節で任意の有限導出を正則化し、6節の Soundness を適用する。7節の計算で
> `[[falseProp]]=0` だから、provability なら `0=1`、typing なら `[[t]] in empty` となり、
> いずれも矛盾する。□

ここで完了したのは `system.md` に書かれた名前付き構文に対する数学的証明である。別構文の Lean
datatypeへの転記と proof assistant による kernel check は、この定理の追加仮定ではなく、別の
機械検証作業である。
