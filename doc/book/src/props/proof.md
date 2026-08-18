モデルの構成と無矛盾性（ AI が書いた）

# `system.md` の体系の相対無矛盾性

## 1. 対象とする体系

この文書の目的は、[`doc/book/src/system.md`](../doc/book/src/system.md) で定義された体系の
相対無矛盾性だけを数学的に示すことである。Lean のデータ型、構成子、de Bruijn index、
実装用証明書、strict positivity、再帰定義の実装方法は扱わない。それらは
[`formalization/lean/formalization.md`](lean/formalization.md) に分離する。

以下では `system.md` の規則表を定義とする。特に次を変更しない。

- 変数は sort annotation を持つ名前付き変数である。束縛変数は alpha-renaming してよい。
- primitive weakening は sorting と typing の二規則である。provability weakening は後で
  admissible rule として導く。
- dependent elimination の primitive premise は function typing と argument typing の二つだけで、
  substituted codomain の sorting は premise ではない。これは regularity と substitution から導く。
- reduction は通常の beta reduction、その全 congruence、および

  ```text
  Pred(A,{x:B | P},t) -> (lambda x:B.P) t
  ```

  である。この規則に `A ≡beta B` という side condition は加えない。

sort を次の略記で書く。

```text
Set_i   = *^s_i,       Kind_i = square^s_i,
Prop    = *^p,         PropKind = square^p.
```

`Gamma |- A :: s` を sorting、`Gamma |- e : A :: s` を typing、`Gamma |= P` を
provability と書く。`M -> N` は一段 reduction、`->*` はその反射推移閉包、`≡beta` は
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
> **主定理。** この仮定のもとで、空文脈では
>
> ```text
> falseProp = (P : Prop) -> P
> ```
>
> は provable でなく、`falseProp` を型に持つ項も存在しない。

証明は、構文的メタ理論、集合モデル、soundness、`falseProp` の意味計算の順に行う。

## 2. 集合モデル

### 2.1 sort

意味値は `W` の要素である。各 sort の領域 `D_s` と sort term 自身の値 `S_s` を

```text
D_(Set_i)    = U_i,        S_(Set_i)    = U_i,
D_(Kind_i)   = U_(i+1),    S_(Kind_i)   = U_(i+1),
D_Prop       = {0,1},      S_Prop       = {0,1},
D_PropKind   = U_omega,    S_PropKind   = U_omega
```

とする。`0=empty`、`bullet=empty`、`1={bullet}` とする。tower の推移性と有限集合への
閉包から、すべての `S_s` は `W` の要素であり、

```text
a in S_s  iff  a in D_s
```

である。`U_i in U_(i+1)` と `{0,1} in U_omega` により `system.md` の二つの axiom
`(Set_i,Kind_i)` と `(Prop,PropKind)` が成り立つ。

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

proposition result の `(Prop,Prop,Prop)`、`(PropKind,Prop,Prop)`、
`(Set_i,Prop,Prop)` は `truth` の定義から閉じる。これで `R` の全 case が尽きる。

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

Grothendieck universe の pairing、replacement、powerset、separation、union により、ここまでの
すべての演算は `W`-valued である。ordinary argument の等号と、domain 上の family の
pointwise equality を保つ。特に `Pi`、`Lam`、`Subset` は family の domain 上の値だけに依存する。

> [!important]
> **モデル補題。** 上の演算は `system.md` の全 formation rule に必要な sort closure、
> introduction / elimination rule に必要な membership law、data beta law、および
> `Pred(A,Subset(B,P),t)` に必要な truth law を同時に満たす。

これは上の定義と universe closure を rule ごとに展開すれば得られる。`Pred` reduction の
意味保存にはさらに derivability から `A` と `B` の値が等しく、`t in B` であることを使う。
これは4節の subject reduction と5節の soundness で確認する。

## 3. 構文的メタ理論

この節では意味論を使わない。変数は capture を避けて alpha-renaming し、以下では束縛変数が
文脈に新しいものとして選ばれているとする。

### 3.1 renaming、weakening、substitution

> [!important]
> **補題（renaming と substitution）。** sorting、typing、provability は capture-avoiding
> renaming で保存される。また `Gamma |- u:A::r` のとき、
>
> ```text
> Gamma,x:A::r,Delta |- B::s       => Gamma,Delta[u/x] |- B[u/x]::s,
> Gamma,x:A::r,Delta |- e:B::s     => Gamma,Delta[u/x] |- e[u/x]:B[u/x]::s,
> Gamma,x:A::r,Delta |= P          => Gamma,Delta[u/x] |= P[u/x].
> ```

**証明。** 文脈 `Delta` の長さと導出の同時帰納法である。variable case は `x` 自身、`x` より
新しい変数、古い変数に分ける。binder の下では置換を lift する代わりに、名前付き表示では
束縛変数を fresh に取り直す。conversion case は reduction と beta equivalence が substitution
で保存されることを使う。take の定値性 premise では二つの binder の双方を fresh にする。□

`system.md` の weak sort / weak type を反復すると任意位置への weakening が得られる。
provability weakening は primitive rule ではないが、

```text
Gamma |= P
=> Gamma |- Proof P : P :: Prop
=> Gamma,x:A::s |- Proof P : P :: Prop
=> Gamma,x:A::s |= P
```

により admissible である。古い変数の rule も、variable rule と weak type の反復で得られる。

> [!important]
> **補題（context conversion）。** `Gamma |- A::s`、`Gamma |- A'::s`、`A≡beta A'` とする。
> well-formed context 中の宣言 `x:A::s` を `x:A'::s` に置き換えても、WF、sorting、typing、
> provability は同じ raw judgement のまま保存される。

**証明。** 置換位置より新しい宣言の個数と導出の同時帰納法。`x` の variable case では
variable rule が与える型 `A'` を conversion で `A` に戻す。新しい宣言の formation と binder
body も同時に輸送する。conversion が renaming で保存されるため任意位置で同じ議論ができる。□

### 3.2 confluence

parallel reduction `=>` を、全 term constructor の reflexive congruence、parallel beta、
および

```text
Pred(A,Subset(B,P),t) => (lambda x:B'.P') t',
Pred(A,Subset(B,P),t) => P'[t'/x]
```

で定める。prime は対応する subterm の parallel reduct であり、消える第一引数 `A` にも
parallel premise を置く。第二規則は `Pred` reduction と直後の beta を同時に縮める。

complete development `M*` は root redex を generic congruence より先に match して

```text
((lambda x:A.M) N)*       = M*[N*/x],
Pred(A,Subset(B,P),t)*     = P*[t*/x]
```

とし、他は全 immediate subterm に `*` を適用する。これは構造再帰であって normalization
ではない。

> [!important]
> **補題（complete development）。** `M=>N` なら `N=>M*`。

**証明。** `M` の構造と parallel derivation の同時帰納法。beta contraction は parallel
substitution を使う。`Pred/Subset` overlap は、congruence のまま進む場合、lambda application
まで進む場合、substitution 後まで進む場合の三つであり、第二の特殊規則、parallel beta、
parallel substitution でそれぞれ `P*[t*/x]` に進む。reduction により lambda や subset head が
新たに現れた場合はその redexを縮めず、congruence で complete development へ進める。□

一段 reduction は parallel reduction に含まれ、parallel reduction は `->*` に含まれる。
従って complete development 補題から diamond、さらに

> [!important]
> **定理（confluence）。** `M->*M1` かつ `M->*M2` なら共通 reduct が存在する。

が得られる。特に `A≡beta B` なら `A` と `B` は joinable である。

`sort`、variable、product、lambda、proof mark、power、subset、type lift、equality、exists、take
は単独では outer head を変える root reduction を持たない。従って二つの異なる不活性 head は
beta-convertible でなく、product、power、type lift の beta equivalence から対応する component
の joinability が得られる。

### 3.3 regularity、generation、sort uniqueness

> [!important]
> **補題（regularity）。** 導出可能な judgement の文脈は well formed であり、
>
> ```text
> Gamma |- e:A::s  => Gamma |- A::s,
> Gamma |= P       => Gamma |- P::Prop.
> ```

regularity と同時に、product 型を表示型に持つ typing、power 型を表示型に持つ subset typing、
および take typing について、conversion や structural detour より前の最後の formation / typing
rule とその premise を回収する generation lemma も示す。表示型が conversion を経ている場合は、
3.2節の confluence と不活性 head の識別により、対応する component が joinable であることまで
回収する。

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
作る。他の case は規則の premise または帰納法の仮定から直接従う。□

ここで canonical origin とは、weakening、conversion、type elem / type sort、type lift intro /
weak を有限回取り除き、raw term の outer constructor を作った最後の rule とその premise を
記録する generation lemma である。type lift intro / weak の前後の型を beta-convertible とは
しない。一般の type uniqueness は実際に偽である。

> [!important]
> **補題（sort と term-sort の一意性）。** 同じ raw expression の二つの sorting
> `Gamma|-A::s`、`Gamma|-A::t` から `s=t`。同じ raw term の二つの typing
> `Gamma|-e:A::s`、`Gamma|-e:B::t` からも `s=t`。

**証明。** 二つの canonical origin の高さの和に関する強い帰納法。direct formation rule は
raw head により一意である。product result は `R` の表の関数性、sort axiom は `A` の関数性、
power、predicate、type lift、equality、exists は規則に書かれた sort で決まる。lambda は body
の低い term-sort uniqueness と `R`、application は argument と function の低い uniqueness と
`R` を使う。take set と take prop の混在は同じ `T` の低い sort uniqueness で排除される。
type elem / type sort の往復は strict premise に進むので高さが減る。□

一般の type uniqueness は使わない。例えば `t:A` とし、
`B={x:A | x=x}` とすれば `t:A` と `t:TypeLift(A,B)` が導けるが、二型は一般には
beta-convertible でない。

### 3.4 subject reduction

> [!important]
> **定理（subject reduction）。** sorting、typing、provability は主式の一段 reduction で
> 保存される。また `Gamma|-e:A::s`、`A->A'` なら `Gamma|-e:A'::s`。

**証明。** 三 judgement の導出と reduction の同時帰納法。weakening は reduction を一段下の
term に反映して帰納法を適用する。binder domain の reduction には context conversion、body
には binder 下の帰納法を使う。application argument の reductionで表示型が `B[a/x]` から
`B[a'/x]` に変わる場合は substitution compatibility と conversion を使う。

root beta は application と lambda の generation から body typing、domain typing、codomain
formation を回収して substitution する。`Pred/Subset` root は subset generation により
構文上の base `B` と predicate側の base `A` が beta-convertible であることを回収する。
argument を `B` へ convert して target application を形成する。

take domain / codomain / function の reductionでは、function typing、existence、定値性 premise を
それぞれ subject reduction と context conversion で輸送する。定値性 proposition で `f` が二回
現れる場合は、一方ずつ進めた二つの一段 congruence を conversion で連結する。生成した target
導出へ帰納法を再適用せず、source の strict premise だけへ再帰するため整礎的である。□

## 4. conversion を展開した有限導出

soundness の conversion case で「beta-convertible な型は同じ意味」と言うには reduction の
意味保存が必要であり、reduction の beta case には subterm の typing soundness が必要になる。
これらを別々に先取りすると循環する。

この循環を避けるため、各 conversion use `A≡beta B` を、confluence が与える共通 reduct `C` と

```text
A=A0 -> A1 -> ... -> C,
B=B0 -> B1 -> ... -> C
```

に展開する。subject reduction により全中間点に同じ sort の sorting derivationを付ける。
また各 typing / provability derivation に、regularity が与える型 / proposition formation と
文脈 WF を付ける。このようなものを**正則導出**と呼ぶ。

元の有限導出から正則導出を作れる。conversion 以外は premise を先に正則化して同じ rule を
適用する。conversion は source type formation と target sorting に joinability と subject
reduction を適用する。逆に注釈を忘れれば元の導出になる。

正則導出と、その中に付けた finite path、endpoint derivation、context transport、substitution
derivationをすべて有限木の node と数える。node の rank を

```text
1 + max(rank of its proper annotated subobjects)
```

とする。元の導出を正則化するときは、先に完成した premise と有限 path から新しい node を
一度だけ作り、node 自身をその subobject に戻さない。従って rank は well founded である。
以下では、この数学的な有限展開が有限かつ整礎的であることだけを使う。

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

context valuation は

```text
Valid(empty,[]),
Valid(Gamma,x:A::s; rho,v)
  iff Valid(Gamma,rho)
      and SortDenotes(A,rho,Aval)
      and v in Aval
```

である。同じ raw context の異なる WF derivation に対する validity の一致は、6節の coherence と
同時に示す。

解釈 clause は2節の演算を rule に従って適用する。

- sort axiom は `S_s`。
- variable は valuation の対応成分。
- type elem は sorting premise の値、type sort は typing premise の項値。
- product、lambda、application は `Pi_z`、`Lam_z`、`App_q`。
- proof mark と proposition-valued take は `bullet`。
- power、subset、predicate、type lift、equality、exists、set-valued take は2節の同名演算。
- conversion は source term の項値を保ち、target sorting の型値と組にする。

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

## 6. soundness と coherence

正則導出の rank に関する強い帰納法で、次を同時に証明する。

1. 同じ raw context の WF derivation は同じ valuation を valid とする。
2. 各 sorting、typing、provability denotation が存在する。
3. sorting value は `D_s` に入り、typing は `Aval in D_s` と `eVal in Aval` を満たし、
   provability value は `1` である。
4. 注釈された一段 reduction、finite path、conversion join の両端は同じ値を表す。
5. 同じ judgement の二つの正則導出、および同じ導出の二 witness は同じ値を表す。さらに、
   同じ raw term の二つの typing は、表示型が異なっていても同じ項値を表す。

帰納法の同じ rank では 1、context transport、reduction / path invariance、existence、
fundamental property、coherence の順に証明する。後の段階が前の段階を使う場合を除き、
すべての呼出しは proper annotated subobject に対するものなので rank が減る。coherence が
同じ rank の fundamental propertyを使うのは provability の二値が双方 `1` であると示す場合
だけである。

主要 rule case を確認する。

- weakening は valid valuation の tail と semantic weakening。
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

reduction invariance の root beta は、data branchなら graph beta と semantic substitution、
proof branchなら両辺が `bullet` であることを使う。sortingされた type-level application の
term sort は axiom target、すなわち `Kind_i` または `PropKind` なので data branchである。

`Pred/Subset` reduction では generation から base `A` と `B` の denotation が等しく、
argument value が `B` に属することを得る。従って source value は

```text
truth(tVal in BVal and PVal(tVal)=1)=PVal(tVal),
```

これは target application の graph beta value に等しい。

coherence では、二導出の weakening、conversion、type elem / type sort、type lift intro / weak
を canonical origin まで有限回剥がす。conversion は低い rank の path invariance、type lift
intro / weak は共通の base typing が表す項値に帰着する。同じ outer constructor の二つの core
rule は、strict premise の coherence と `Pi`、`Lam`、`Subset` の domain 上の外延性で一致する。
同じ raw term が異なる表示型を持つ場合も、二つの canonical origin に同じ議論を行う。term-sort
uniqueness により proof branch と data branch が混在せず、一般の type uniqueness は必要ない。
provability の二導出は fundamental property により命題値がともに `1` なので一致する。これで
上の5の cross-typing case を含む全 coherence case が閉じる。

これで `system.md` の primitive 29規則、すなわち PTS / WF 12規則、provability 2規則、
power / subset / type lift 7規則、equality 3規則、choice 5規則の全 case が尽きる。

> [!important]
> **Soundness。** valid valuation `rho` のもとで
>
> ```text
> Gamma |- A::s       => [[A]]rho in D_s,
> Gamma |- e:A::s     => [[A]]rho in D_s and [[e]]rho in [[A]]rho,
> Gamma |= P          => [[P]]rho=1.
> ```

元の導出を正則化して上の同時定理を適用する。正則化の選択によらないことは coherence から
従う。

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

空文脈で `falseProp` が provable と仮定すると、空 valuation は valid なので soundness から
`[[falseProp]]=1`。上の計算は `0` を与え、`0!=1` に反する。

また `Gamma` を空として `t:falseProp::s` があると仮定する。regularity と sort uniqueness から
`s=Prop`。soundness と formation coherence から

```text
[[t]] in [[falseProp]]=0,
```

となるが空集合に要素はない。従ってそのような項も存在しない。これで主定理が示された。□

従って、ZFC と1節の universe tower の存在が無矛盾なら、`system.md` の体系も、少なくとも
`falseProp` の provability および inhabitance を矛盾とする意味で無矛盾である。
