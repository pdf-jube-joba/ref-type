# `system.md` の相対無矛盾性：集合モデルと残る条件

## 1. 証明すること

この文書では [`system.md`](../system.md) の現在の構文に合わせて、Set/Prop の PTS と
CBPV に基づく Program calculus を同時に解釈する。対象は次の規則である。

- `Sort` から `Acc と run` までに明記された構文、reduction、judgement
- `帰納型と CBPV` に明記された Program type、constructor、case、Set の鏡像、
  `Rf-Ind`、`Rf-Ctor`

ただし `system.md` 自身が課題としている次の部分は、まだ一意な formal system を定めていない。

- declaration environment の厳密な well-formedness と positivity judgement
- Set case / induction の raw syntax、typing、reduction
- それらを含む \(\Rightarrow_s\) の compatible closure

従って、まずこれらを使わない **core calculus** の集合モデルを与える。帰納型については、6節で
明記済みの五規則が sound であることを示し、未定義部分を標準的な strictly-positive 規則で
補った場合の拡張条件を述べる。「通常の規則」の選び方によらない無条件の定理は主張しない。

さらに現在の core にも、`system.md` の `CBPV` 課題欄に書かれている reflection の critical-pair
問題が残る。3.4節で具体的な非合流 peak を示す。このため、以下では

\[
\begin{aligned}
&\Gamma\vdash T_1:s,\quad \Gamma\vdash T_2:s,\quad T_1\equiv_sT_2\\
&\qquad\Longrightarrow
\llbracket T_1\rrbracket_\rho=\llbracket T_2\rrbracket_\rho
\end{aligned}
\tag{TC}
\]

が、表示した二つのsorting derivationの任意の選び方と \(\Gamma\) のすべてのvalid valuation
\(\rho\) について成り立つことを
**typed conversion soundness 条件**と呼ぶ。これは規則の soundness を仮定することではなく、
raw conversion と typing の接続について現在未完了のメタ定理を一つ切り出したものである。
3.4節では、conversion を typed congruence にする方法と、raw reduction を同期的に completion する
方法の二つを区別する。

以下の略記を使う。

```text
Set_i    = *^s_i,       Kind_i  = square^s_i,
Prop     = *^p,         PropKind = square^p.
```

sorting を `Gamma |- T :: s`、PTS typing を `Gamma |- t : T :: s`、provability を
`Gamma |= P` と書く。Program judgement は `A vtype`、`B ctype`、`V :v A`、`M :c B`
と略記する。\(\to_s^*\)、\(\to_c^*\) はそれぞれの reduction の反射推移閉包である。

外部理論として ZFC と、推移的な Grothendieck universe の列

```text
U_0 in U_1 in ... in U_omega in W
```

を仮定する。\(U_\omega\) はすべての \(U_i\) を含む Grothendieck universe であり、
\(W\) も Grothendieck universe とする。単なる \(\bigcup_iU_i\) では dependent product
への閉包が保証されないので、独立に \(U_\omega\) を仮定している。

> [!important]
> **主定理（typed conversion soundness に相対化した core の無矛盾性）。** 上の集合論的仮定と
> 条件 `(TC)` のもとで、`system.md` の core calculus について
>
> ```text
> falseProp = (P : Prop) -> P
> ```
>
> と置くと、
>
> ```text
> not (empty |= falseProp),
> not (exists t s, empty |- t : falseProp :: s)
> ```
>
> が成り立つ。conversion rule を除いた fragment、および3.4節で定義する typed congruence 版では
> `(TC)` は定理として成り立つので、追加条件を要しない。

ここでいう無矛盾性は proof-theoretic consistency であって、raw Program の強正規化ではない。
偽の `Acc` assumption を持つ open context では発散する `run` を型付けできる可能性がある。
定理が使うのは、空文脈、または意味論的に妥当な closing valuation の下での soundness である。

## 2. 集合モデル

### 2.1 sort と mixed context

\(0=\varnothing\)、\(\bullet=\varnothing\)、\(1=\{\bullet\}\) とする。sort の領域を

\[
\begin{aligned}
D_{\mathrm{Set}_i}&=U_i,
&S_{\mathrm{Set}_i}&=U_i,\\
D_{\mathrm{Kind}_i}&=U_{i+1},
&S_{\mathrm{Kind}_i}&=U_{i+1},\\
D_{\mathrm{Prop}}&=\{0,1\},
&S_{\mathrm{Prop}}&=\{0,1\},\\
D_{\mathrm{PropKind}}&=U_\omega,
&S_{\mathrm{PropKind}}&=U_\omega
\end{aligned}
\]

とする。すべての値は \(W\) の要素である。各 sort について

\[
\llbracket s\rrbracket_\rho=S_s,
\qquad
\llbracket x^s\rrbracket_\rho=\rho(x^s)
\]

と解釈する。さらに

\[
a\in S_s\quad\Longleftrightarrow\quad a\in D_s
\tag{sort-membership}
\]

が成り立つ。\(U_i\in U_{i+1}\) と \(\{0,1\}\in U_\omega\) により、
`system.md` の axiom はすべて sound である。

Program の型は PTS の sort では分類しない。その代わり、value type と computation type の
carrier をともに \(U_0\) の要素として解釈する。mixed context の valuation \(\rho\) は、
左から順に次を満たす tuple である。

| context entry | valuation の条件 |
| --- | --- |
| \(x^s:T:s\) | \(\rho(x^s)\in\llbracket T\rrbracket_\rho\) |
| \(X:\mathsf{vtype}\) | \(\rho(X)\in U_0\) |
| \(x^v:A:\mathsf{value}\) | \(\rho(x^v)\in\llbracket A\rrbracket_\rho\) |

前の entry だけを参照して右辺を解釈する。Program type は PTS term に依存せず、PTS term は
`RfType` と `RfTerm` を通して Program entry に依存できる。この向きは上の逐次的な定義と整合する。

meta-level proposition \(Q\) に対し、真なら \(1\)、偽なら \(0\) を返す集合を
\(\operatorname{truth}(Q)\) と書く。古典論理により

\[
\operatorname{truth}(Q)=1\Longleftrightarrow Q,
\qquad
v\in p\Longleftrightarrow(v=\bullet\land p=1)
\quad(p\in\{0,1\})
\tag{proof-membership}
\]

である。

### 2.2 PTS の product、lambda、application

family と関数は \(W\) 内の functional graph で表す。\(\operatorname{app}(f,x)\) は
\(f\) が domain に \(x\) を含む functional graph ならその値を返し、それ以外は \(0\) を
返す。この既定値により raw input に対しても全域になる。

product rule \((r,q,z)\in\mathcal R\) を一つ固定する。\(z\ne\mathrm{Prop}\) のとき

\[
\begin{aligned}
\Pi_z(A,B)
&=\{f\mid \operatorname{dom}(f)=A
       \land \forall x\in A.\ \operatorname{app}(f,x)\in B(x)\},\\
\operatorname{Lam}_z(A,m)
&=\{(x,m(x))\mid x\in A\},\\
\operatorname{App}_q(f,x)&=\operatorname{app}(f,x)
\end{aligned}
\]

とする。現在の \(\mathcal R\) では

\[
z=\mathrm{Prop}\quad\Longleftrightarrow\quad q=\mathrm{Prop}
\tag{prop-branch}
\]

なので、data branch では graph による通常の introduction、elimination、beta law が成り立つ。

\(z=\mathrm{Prop}\) のときは proof irrelevance を使い、

\[
\begin{aligned}
\Pi_{\mathrm{Prop}}(A,B)
  &=\operatorname{truth}(\forall x\in A.\ B(x)=1),\\
\operatorname{Lam}_{\mathrm{Prop}}(A,m)&=\bullet,\\
\operatorname{App}_{\mathrm{Prop}}(f,x)&=\bullet
\end{aligned}
\]

とする。\(f\in\Pi_{\mathrm{Prop}}(A,B)\) なら全 fiber が \(1\) なので、application の
値 \(\bullet\) は結論の fiber に属する。

sort table の閉包を全 case について確認する。表の「包含」は tower の推移性を、`Π-closure` は
該当 Grothendieck universe の dependent-product closure を表す。

| \((r,q,z)\) | closure の理由 |
| --- | --- |
| \((\mathrm{Set}_i,\mathrm{Set}_j,\mathrm{Set}_{\max(i,j)})\) | domain と全 fiber を \(U_{\max(i,j)}\) に含めて `Π-closure` |
| \((\mathrm{Set}_i,\mathrm{Kind}_j,\mathrm{Kind}_{\max(i,j)})\) | domain と fiber は \(U_{\max(i,j)+1}\) に入り、同 universe の `Π-closure` |
| \((\mathrm{Kind}_i,\mathrm{Kind}_j,\mathrm{Kind}_{\max(i,j)})\) | 両方を \(U_{\max(i,j)+1}\) に含めて `Π-closure` |
| \((\mathrm{Kind}_i,\mathrm{Set}_j,\mathrm{Set}_{\max(i+1,j)})\) | domain は \(U_{i+1}\)、fiber は \(U_j\) にあり、\(U_{\max(i+1,j)}\) の `Π-closure` |
| \((\mathrm{Prop},\mathrm{Prop},\mathrm{Prop})\) | `truth` の値は \(0\) または \(1\) |
| \((\mathrm{PropKind},\mathrm{Prop},\mathrm{Prop})\) | 同上。domain の大きさは `truth` の値域を変えない |
| \((\mathrm{PropKind},\mathrm{PropKind},\mathrm{PropKind})\) | domain と fiber は \(U_\omega\) にあり、その `Π-closure` |
| \((\mathrm{Set}_i,\mathrm{Prop},\mathrm{Prop})\) | `truth` の値は \(0\) または \(1\) |
| \((\mathrm{Set}_i,\mathrm{PropKind},\mathrm{PropKind})\) | \(U_i\subseteq U_\omega\) と \(U_\omega\) の `Π-closure` |

これで現在の \(\mathcal R\) の全 case が尽きる。特に
\((\mathrm{Prop},\mathrm{PropKind},\mathrm{PropKind})\) は規則表に存在しないので、Prop の proof
carrier 全体に依存する大きな type family を誤って追加していない。旧体系に存在した `Comp` sort と
`(Comp,Comp,Comp)` も使わない。

### 2.3 Set/Prop の追加演算

すべての \(W\)-valued input に対し、

\[
\begin{aligned}
\operatorname{Power}(A)&=\{B\mid B\subseteq A\},\\
\operatorname{Subset}(A,P)&=\{x\in A\mid \operatorname{app}(P,x)=1\},\\
\operatorname{Pred}(A,B,t)&=\operatorname{truth}(t\in B),\\
\operatorname{TypeLift}(A,B)&=B,\\
\operatorname{Eq}(a,b)&=\operatorname{truth}(a=b),\\
\operatorname{Exists}(A)&=\operatorname{truth}(A\ne\varnothing)
\end{aligned}
\]

とする。`Pred` の第一引数は annotation であり、値には使わない。\(A\in U_i\) なら
powerset と subset は \(U_i\) に属する。

set-valued `Take` は

\[
\operatorname{Take}(X,T,f)
=\bigcup\{\operatorname{app}(f,x)\mid x\in X\}
\]

とする。\(X\ne\varnothing\) かつ \(f\) が \(X\) 上で定値 \(y\in T\) なら image は
\(\{y\}\) なので

\[
\operatorname{Take}(X,T,f)=y\in T.
\tag{take-law}
\]

代表元を選ばないため global choice は使わない。proposition-valued `Take` の項値は
\(\bullet\) とする。存在 premise と \(f:X\to T\) の typing から \(T=1\) が従うので、
\(\bullet\in T\) である。

`Proof P` の値も \(\bullet\) とする。provability premise の soundness が \(P=1\) を
与えるため、これは \(P\) の要素になる。

### 2.4 CBPV の型と項

Program type environment が与える \(X\in U_0\) を用いて、

\[
\begin{aligned}
\llbracket X\rrbracket_\rho&=\rho(X),\\
\llbracket x^v\rrbracket_\rho&=\rho(x^v),\\
\llbracket \mathrm F A\rrbracket_\rho&=\llbracket A\rrbracket_\rho,\\
\llbracket \mathrm U\underline B\rrbracket_\rho
  &=\llbracket\underline B\rrbracket_\rho,\\
\llbracket A\Rightarrow\underline B\rrbracket_\rho
  &=\{f\mid\operatorname{dom}(f)=\llbracket A\rrbracket_\rho
       \land\forall a\in\llbracket A\rrbracket_\rho.\
          \operatorname{app}(f,a)\in\llbracket\underline B\rrbracket_\rho\}
\end{aligned}
\]

とする。Grothendieck universe の function set への閉包により、いずれも \(U_0\) の要素である。
`F` と `U` を同じ carrier に解釈するのは、構文的に型を同一視することではない。

項の解釈は

\[
\begin{aligned}
\llbracket\operatorname{return}(V)\rrbracket_\rho
  &=\llbracket V\rrbracket_\rho,\\
\llbracket\operatorname{thunk}(M)\rrbracket_\rho
  &=\llbracket M\rrbracket_\rho,\\
\llbracket\operatorname{force}(V)\rrbracket_\rho
  &=\llbracket V\rrbracket_\rho,\\
\llbracket\lambda x^v:A.M\rrbracket_\rho
  &=\{(a,\llbracket M\rrbracket_{\rho[x^v:=a]})
        \mid a\in\llbracket A\rrbracket_\rho\},\\
\llbracket M@^cV\rrbracket_\rho
  &=\operatorname{app}(\llbracket M\rrbracket_\rho,
                        \llbracket V\rrbracket_\rho),\\
\llbracket M\ \operatorname{to}\ x^v:A\ \operatorname{in}\ N\rrbracket_\rho
  &=\llbracket N\rrbracket_{\rho[x^v:=\llbracket M\rrbracket_\rho]},\\
\llbracket\operatorname{let}^v x^v=V\ \operatorname{in}\ N\rrbracket_\rho
  &=\llbracket N\rrbracket_{\rho[x^v:=\llbracket V\rrbracket_\rho]}
\end{aligned}
\]

である。従って force/thunk、CBPV beta、sequence、value let の四 root reduction は
well-typed input で意味を保存する。

\(A,B\in U_0\) に対して

\[
\begin{aligned}
\operatorname{RunStep}(A,B)
  &=(\{0\}\times A)\cup(\{1\}\times B),\\
\operatorname{continue}_{A,B}(a)&=(0,a),\\
\operatorname{finish}_{A,B}(b)&=(1,b)
\end{aligned}
\]

とする。二つの tag は disjoint かつ injective であり、carrier は \(U_0\) に属する。
Program syntaxの解釈 clauseは

\[
\begin{aligned}
\llbracket\operatorname{RunStep}(A,B)\rrbracket_\rho
  &=\operatorname{RunStep}(\llbracket A\rrbracket_\rho,
                            \llbracket B\rrbracket_\rho),\\
\llbracket\operatorname{continue}_{A,B}(V)\rrbracket_\rho
  &=(0,\llbracket V\rrbracket_\rho),\\
\llbracket\operatorname{finish}_{A,B}(V)\rrbracket_\rho
  &=(1,\llbracket V\rrbracket_\rho)
\end{aligned}
\]

である。annotation \(A,B\) はtagged sumのcarrierを決め、payload値は対応するsummandに入る。

### 2.5 accessibility と run

\(F:A\to\operatorname{RunStep}(A,B)\) という functional graph に対し、

\[
b<_F a\quad\Longleftrightarrow\quad
\operatorname{app}(F,a)=(0,b)
\]

と定める。\(\operatorname{Acc}_F\subseteq A\) を、単調作用素

\[
\Phi_F(X)=\{a\in A\mid
  \forall b\in A.\ b<_F a\Longrightarrow b\in X\}
\]

の最小不動点とする。\(X\subseteq Y\) なら、「すべてのpredecessorが \(X\) に入る」ことから
「すべてのpredecessorが \(Y\) に入る」ことが従うので、\(\Phi_F(X)\subseteq\Phi_F(Y)\) である。
存在を確認するため ordinal に沿って

\[
X_0=\varnothing,\qquad
X_{\alpha+1}=\Phi_F(X_\alpha),\qquad
X_\lambda=\bigcup_{\beta<\lambda}X_\beta
\]

と置く。単調性によりこの列は増大する。\(\mathcal P(A)\) は集合なので Hartogs の補題から
ある \(\theta\) で \(X_\theta=X_{\theta+1}\) となる。
\(\operatorname{Acc}_F=X_\theta\) と置けば、任意の pre-fixed point への transfinite induction
により最小性も従う。

ここを詳しく確認する。\(X_0\subseteq X_1\) は明らかである。successorでは
\(X_\alpha\subseteq X_{\alpha+1}\) に単調性を適用して
\(X_{\alpha+1}=\Phi_F(X_\alpha)\subseteq\Phi_F(X_{\alpha+1})=X_{\alpha+2}\) を得る。
limit \(\lambda\) では、\(a\in X_\lambda\) ならある \(\beta<\lambda\) について \(a\in X_\beta\) であり、
\(\beta+1<\lambda\) とそれ以前の増大性から
\(a\in X_{\beta+1}=\Phi_F(X_\beta)\subseteq\Phi_F(X_\lambda)=X_{\lambda+1}\) となる。
従って全ordinalで \(X_\alpha\subseteq X_{\alpha+1}\) である。もし Hartogs ordinal
まで一度も consecutive equality がなければ、\(\alpha\mapsto X_\alpha\) はその ordinal から
\(\mathcal P(A)\) への単射を与えて Hartogs の補題に反する。従って上の \(\theta\) が存在し、
\(X_\theta=\Phi_F(X_\theta)\) である。さらに \(\Phi_F(Y)\subseteq Y\) を満たす任意の
pre-fixed point \(Y\) に対し、transfinite induction で \(X_\alpha\subseteq Y\) が成り立つ。
successor case は

\[
X_{\alpha+1}=\Phi_F(X_\alpha)
\subseteq\Phi_F(Y)\subseteq Y
\]

であり、limit case は union で閉じる。従って \(X_\theta\) は最小の fixed point である。

\(a\in\operatorname{Acc}_F\) には、初めて \(X_{\alpha+1}\) に入る \(\alpha\) を
\(\operatorname{rank}_F(a)\) として割り当てられる。limit stageはそれ以前のunionなので、要素が
初めてlimit stageに入ることはなく、この \(\alpha\) は必ず存在する。\(b<_F a\) なら

\[
\operatorname{rank}_F(b)<\operatorname{rank}_F(a).
\]

実際、\(a\in X_{\alpha+1}=\Phi_F(X_\alpha)\) かつ \(b<_Fa\) なら \(b\in X_\alpha\) である。
よって \(b\) が初めて現れる stage は \(\alpha+1\) より真に前にある。

また不動点方程式から

\[
(\forall b\in A.\ b<_F a\Rightarrow b\in\operatorname{Acc}_F)
\Rightarrow a\in\operatorname{Acc}_F.
\tag{acc-intro-law}
\]

\[
a\in\operatorname{Acc}_F\land b<_F a
\Rightarrow b\in\operatorname{Acc}_F.
\tag{acc-descent-law}
\]

`Acc` は

\[
\llbracket\operatorname{Acc}_{A,B}(f,a)\rrbracket_\rho
=\operatorname{truth}(\llbracket a\rrbracket_\rho
   \in\operatorname{Acc}_{\llbracket f\rrbracket_\rho})
\]

と解釈する。`StepFun(A,B)` の carrier はちょうど
\(A\to\operatorname{RunStep}(A,B)\) であり、`continueFun` の値は
\(b\mapsto(0,b)\) である。従って

\[
\llbracket\operatorname{Next}_{A,B}(f,b,a)\rrbracket=1
\quad\Longleftrightarrow\quad b<_F a.
\tag{next-law}
\]

この式を proposition product の意味に代入すると、`acc intro` の最後の premise は
`acc-intro-law` の左辺そのものであり、`acc descent` は `acc-descent-law` になる。

次に rank に沿う well-founded recursion で

\[
\operatorname{Run}_{A,B}(F,a)=
\begin{cases}
\operatorname{Run}_{A,B}(F,a')&
  a\in\operatorname{Acc}_F,\ \operatorname{app}(F,a)=(0,a'),\
  \ a'\in\operatorname{Acc}_F,\\
b&a\in\operatorname{Acc}_F,\ \operatorname{app}(F,a)=(1,b),\ b\in B,\\
0&\text{otherwise}
\end{cases}
\]

と定める。第一caseのrecursive callはrankが真に小さい引数だけを許すので、
\(\operatorname{Acc}_F\) 上のwell-founded recursionとして一意に定まる。第三caseにより任意の
\(W\)-valued inputへ全域化される。well-formedな \(F:A\to\operatorname{RunStep}(A,B)\) と
\(a\in\operatorname{Acc}_F\) については最初の二caseのどちらかが必ず成立し、値は \(B\) に属する。

値域の主張は \(\operatorname{rank}_F(a)\) に関する整礎帰納法で示す。
\(\operatorname{app}(F,a)=(1,b)\) なら、\(F\) の function typing と tagged sum の定義から
\(b\in B\) である。\(\operatorname{app}(F,a)=(0,a')\) なら同様に \(a'\in A\) であり、
`acc-descent-law` と rank の真の減少から帰納法の仮定を \(a'\) に適用できる。従って
\(\operatorname{Run}_{A,B}(F,a')\in B\) である。二つの tag は disjoint で、typed な
\(F(a)\) は必ずどちらか一方なので、場合分けは排他的かつ全域である。

次に

\[
\operatorname{RunCase}_{A,B}(F,a,u)=
\begin{cases}
0&a\notin\operatorname{Acc}_F,\\
\operatorname{Run}_{A,B}(F,a')&a\in\operatorname{Acc}_F,\ u=(0,a'),\\
b&a\in\operatorname{Acc}_F,\ u=(1,b),\\
0&\text{otherwise}
\end{cases}
\]

Program termの解釈は

\[
\begin{aligned}
\llbracket\operatorname{run}_{A,B}(f,a)\rrbracket_\rho
&=\operatorname{Run}_{\llbracket A\rrbracket_\rho,
                       \llbracket B\rrbracket_\rho}
  (\llbracket f\rrbracket_\rho,\llbracket a\rrbracket_\rho),\\
\llbracket\operatorname{runCase}_{A,B}(f,a,M)\rrbracket_\rho
&=\operatorname{RunCase}_{\llbracket A\rrbracket_\rho,
                           \llbracket B\rrbracket_\rho}
  (\llbracket f\rrbracket_\rho,
   \llbracket a\rrbracket_\rho,
   \llbracket M\rrbracket_\rho)
\end{aligned}
\]

とする。次の各行の左に書いた条件のもとで law が成り立つ。

\[
\begin{aligned}
a\in\operatorname{Acc}_F
&\Rightarrow
\operatorname{Run}(F,a)
 =\operatorname{RunCase}(F,a,\operatorname{app}(F,a)),\\
a\in\operatorname{Acc}_F\land\operatorname{app}(F,a)=(0,a')
&\Rightarrow
\operatorname{RunCase}(F,a,(0,a'))=\operatorname{Run}(F,a'),\\
a\in\operatorname{Acc}_F\land\operatorname{app}(F,a)=(1,b)
&\Rightarrow
\operatorname{RunCase}(F,a,(1,b))=b.
\end{aligned}
\tag{run-laws}
\]

continue case の再帰先が accessible であることは `acc-descent-law` による。これが無条件の
一般不動点との違いである。`run-laws` の第一式は rank recursion の定義式、第二・第三式は
`RunCase` の tag 場合分けである。第二式の右辺が全域化時の既定値でないことは
`acc-descent-law` が保証する。

### 2.6 reflection

value type と computation type の carrier はともに \(U_0\) にあるので、well-formed input に
対して reflection を意味的な恒等写像にできる。

\[
\begin{aligned}
\llbracket\operatorname{RfType}(P)\rrbracket_\rho
  &=\llbracket P\rrbracket_\rho,\\
\llbracket\operatorname{RfTerm}_P(p)\rrbracket_\rho
  &=\llbracket p\rrbracket_\rho.
\end{aligned}
\tag{reflection-value}
\]

これは raw constructor を構文的に消す定義ではない。`RfType`、`RfTerm` の syntax は残り、
その denotation だけを同じ集合または要素に選んでいる。

`F` と `U` の carrier が恒等で、PTS と Program の関数を同じ functional graph で表したので、

\[
\begin{aligned}
\llbracket\operatorname{RfType}(\mathrm F A)\rrbracket
 &=\llbracket\operatorname{RfType}(A)\rrbracket,\\
\llbracket\operatorname{RfType}(\mathrm U\underline B)\rrbracket
 &=\llbracket\operatorname{RfType}(\underline B)\rrbracket,\\
\llbracket\operatorname{RfType}(A\Rightarrow\underline B)\rrbracket
 &=\llbracket\operatorname{RfType}(A)
      \to\operatorname{RfType}(\underline B)\rrbracket,\\
\operatorname{app}(\llbracket f\rrbracket,\llbracket a\rrbracket)
 &=\llbracket\operatorname{force}(f)@^ca\rrbracket,\\
\operatorname{app}(\llbracket M\rrbracket,\llbracket a\rrbracket)
 &=\llbracket M@^ca\rrbracket
\end{aligned}
\tag{reflection-laws}
\]

である。return/thunk の二つの `RfTerm` rule も `reflection-value` から直ちに従う。
Program の一段 reduction が意味を保存すれば、その step を payload に持つ `RfTerm` rule も
意味を保存する。従って `system.md` に列挙された reflection root rule はすべて sound である。

> [!important]
> **モデル演算補題。** 2.1--2.6節の演算はすべて \(W\)-valued input 上で全域であり、
> well-formed input では規則表が要求する universe membership を満たす。また、各演算は通常の
> 引数の等号と family graph の pointwise equality を保つ。

**証明。** `app`、malformed な `Run` / `RunCase` には明示した既定値 \(0\) を使う。
`Power`、`Subset`、tagged sum、functional graph は \(W\) の powerset、separation、pairing、
replacement への閉包で \(W\) に属する。`Acc` の iteration は \(\mathcal P(A)\) 内で行われ、
stabilization ordinal までの列とその union は replacement と union により集合である。`Run` の
graph は \(\operatorname{Acc}_F\) 上の well-founded recursion theorem と replacement により
集合になる。well-formed input の小さい universe への membership は2.2--2.5節で個別に示した。

外延性について、`Pi`、lambda graph、application、powerset、subset、tagged sum は定義から従う。
\(F=F'\)、\(A=A'\)、\(B=B'\) なら関係 \(<_F\) と \(<_{F'}\) は等しく、transfinite iteration の
各 stage が等しいので `Acc` も等しい。`Run` は同じ well-founded relation 上で同じ recursion
equation を満たすため、well-founded recursion の一意性から等しい。`RunCase` もその定義から
等しい。従って compatible context の引数を等しい値へ置き換えても結果値は変わらない。□

## 3. 構文的メタ理論

この節の補題は意味論を使わない。束縛変数は必要に応じて alpha-renaming し、常に fresh に取る。

### 3.1 mixed renaming、weakening、substitution

置換は変数 category ごとに三種類ある。

1. PTS typing \(\Gamma\vdash u:A:s\) による \(x^s\) の置換
2. value type \(A\) による Program type variable \(X\) の置換
3. value typing \(\Gamma\vdash_vV:A\) による \(x^v\) の置換

第三の置換は Program term だけでなく、`RfTerm` の payload と `Acc`、`Next`、`Terminates`、
`RunInv` の内部にも入れる。第二の置換は Program の全 annotation と、それを含む `RfType`、
`RfTerm` に入れる。第一の置換は PTS 部分に入り、現在の Program type grammar には入らない。

> [!important]
> **mixed substitution 補題。** well-formed な prefix で上のいずれかの置換項が型付けされて
> いるとする。このとき後続 context の WF と、PTS sorting / typing / provability、value type /
> computation type formation、value / computation typing は capture-avoiding substitution で
> 保存される。

**証明。** 第一 measure を後続 context の長さ、第二 measure を judgement derivation の高さとする
辞書式帰納法を使う。variable case は置換対象、対象より前、対象より後の三つに分ける。対象自身
なら置換項の typing derivationを使い、後二つなら variable rule と必要な weakeningを付け直す。
各 rule family の処理は次の通りである。

| rule family | 置換後の導出の構成 |
| --- | --- |
| PTS / Program の context start | entry の formation に IH を適用し、freshness を renaming で回復して start を再適用 |
| weak rule | strict premise と WF premise に IH を適用して同じ weak rule を再適用 |
| PTS product / lambda | binder を置換項の自由変数から fresh に取り直し、domain と binder body の IH から規則を再適用 |
| PTS application | function と argument の IH、および codomain に対する capture-avoiding substitution の合成則を使う |
| conversion | source typing と target sorting に IH を適用する。raw reduction と \(\equiv_s\) が三種類の substitution で保存されることは reduction derivation の構造帰納法による |
| subset / equality / take | 全 ordinary argument に IH を適用する。`id elim` と take の定値性 premise の binder は先に fresh にする |
| Program lambda / sequence / value let | value binder を fresh にし、各 computation premise の IH から同じ typing rule を再適用 |
| `return` / `thunk` / `force` / Program application | immediate premise の IH から同じ typing rule を再適用 |
| `RunStep` / tag / reflection | type annotation と payload の双方に対応する IH を適用する |
| `Acc` / `run` / `runCase` | `Next`、`Terminates`、`RunInv` を展開し、全引数と proof premise に IH を適用する |
| `acc intro` | PTS binder \(b\) を fresh にしてから binder 下の provability IH を使う |
| datatype constructor / case | parameter、field、scrutinee、全 branch に IH を適用し、branch binder を一斉に fresh にする |

Program type substitutionでは signature 中の全 \(X\) と reflected annotation も置換する。
Program value substitutionでは `RfTerm` 内の valueだけでなく、その valueを含む computation 全体を
置換する。PTS substitutionは現在の Program grammarには入らない。どの表の行でも recursive call は
元の strict premise、または真に短い context suffixへ向くため、辞書式 measure は真に減少する。□

同じ帰納法から三 category の renaming が得られる。primitive weakening と context extension rule
を繰り返せば、任意位置への weakening も admissible である。PTS judgement を Program entry の上へ
運ぶときは `weak sort/type over Program`、Program judgement には `Program weak` を使う。
provability の weakening は

```text
Gamma |= P
=> Gamma |- Proof P : P :: Prop
=> Gamma,e |- Proof P : P :: Prop
=> Gamma,e |= P
```

により導ける。

PTS context declaration \(x:A:s\) は、\(A\equiv_sA'\) かつ両方が \(s\) に sort される
なら context conversion できる。より正確には、\(\Gamma,x:A:s,\Delta\) の WF derivation とその上の
judgement derivationから、\(\Gamma,x:A':s,\Delta\) の対応する導出を作れる。証明は
\((|\Delta|,h)\) に関する辞書式帰納法である。\(x\) 自身のvariable caseでは、新しいdeclarationから
まず \(x:A':s\) を得て、\(A'\equiv_sA\) と \(A:s\) によりtyping conversionで \(x:A:s\) へ戻す。
後続entryのstart caseでは、そのentryのformation derivationに同じ帰納法を適用してWFを作り直す。
それ以外のterminal ruleでは全strict premiseにIHを適用してruleを再適用する。Program typeはPTS
variableに依存しないが、mixed context中のProgram entryもWF premiseを作り直して保存する。
各再帰呼出しでは後続context長または導出高が真に減るので、この同時帰納法は停止する。

また

\[
\Gamma\vDash P,\quad
\Gamma\vdash Q:\mathrm{Prop},\quad
P\equiv_sQ
\quad\Longrightarrow\quad
\Gamma\vDash Q
\tag{prov-conv}
\]

は `Proof P` に typing conversion を適用してから provable rule を使えばよい。

### 3.2 regularity、generation、category / branch uniqueness

導出に関する同時強帰納法で次を得る。

> [!important]
> **regularity。** 導出可能な judgement の context は well formed であり、
>
> \[
> \Gamma\vdash t:T:s\Rightarrow\Gamma\vdash T:s,
> \qquad
> \Gamma\vDash P\Rightarrow\Gamma\vdash P:\mathrm{Prop}.
> \]
>
> Program typing からは対応する type formation が得られる。すなわち
> \(V:_vA\Rightarrow A\,\mathsf{vtype}\) および
> \(M:_c\underline B\Rightarrow\underline B\,\mathsf{ctype}\) である。

\(\epsilon(s)=\mathsf{proof}\) を \(s=\mathrm{Prop}\) のとき、
\(\epsilon(s)=\mathsf{data}\) をそれ以外のときと定める。同じ同時帰納法に、モデルの分岐に必要な
次の四性質を含める。

> [!important]
> **sortability separation / branch uniqueness。** 同じ raw PTS termについて
>
> \[
> \begin{aligned}
> \Gamma\vdash t:r,\quad\Gamma\vdash t:T:s
> &\Longrightarrow \epsilon(s)=\mathsf{data},\\
> \Gamma\vdash t:s,\quad\Gamma\vdash t:s'
> &\Longrightarrow \epsilon(s)=\epsilon(s'),\\
> \Gamma\vdash t:T:s,\quad\Gamma\vdash t:T':s'
> &\Longrightarrow \epsilon(s)=\epsilon(s'),\\
> \Gamma\vdash t:s,\quad\Gamma\vdash t:r:q,\quad r\in\mathcal S
> &\Longrightarrow \epsilon(s)=\epsilon(r).
> \end{aligned}
> \]
>
> ここでは universe levelを含む末尾sortの完全な一意性も、表示型の一意性も主張しない。
> 後者は少なくとも `subset intro/weak` のため成り立たない。Program では value type と
> computation type のcategoryはdisjointで、同じvalueまたはcomputationの型はalpha同値まで
> 一意である。
> 帰納型を含める場合、このProgram側の主張は一意なsignatureを持つ固定済みのdeclaration
> environmentに相対化する。

**証明。** regularity、上の四性質、generationについて、比較する導出高の和に関する同時強帰納法を
使う。weakeningはstrict premiseへ、PTS conversionはsource typingへ、`type elem/type sort` は
保存されたsorting / typing premiseへ進む。`subset intro/weak` は同じraw termのbase typingへ進む。
このdetourを有限回剥がすと、raw outer constructorに対応するcore ruleへ到達する。

core caseでbranchを決める情報は次の通りである。

| raw head | branchを一致させる理由 |
| --- | --- |
| variable | superscriptのsortとcontext declarationが固定する |
| product formation | `prop-branch` によりresultがProp iff codomain sortがProp。bodyのsorting IHを使う |
| lambda typing | `prop-branch` によりterminal sortがProp iff bodyのterminal sortがProp。bodyのtyping IHを使う |
| application typing | 各function productでcodomain sortがProp iff product result sortがProp。二つのfunction typingにtyping IHを使う |
| `type elem` | axiomのcodomainはKindまたはPropKindで、常にdata branch。別のtypingとの比較にはsortability separationの相互IHを使う |
| `type sort` | 保存されたtypingと、四つ目のsorting/typing bridge IHを使う |
| proof term | terminal sortはPropに固定され、同じraw headを持つ他のcore typing ruleはない |
| Set/Propのspecial form | `Power`、`Pred`、subset、equality、`Exists`、`RfType`、`Acc` は各formation ruleがbranchを固定する |
| Set/Propのspecial term | subset / equality / `Take` / reflectionのtyping ruleがterminal branchを固定する |

applicationの行が完全なtype uniquenessを使わずに済む点が重要である。二つのfunction premiseの
表示型が異なるproductでも、そのterminal sortのbranchはIHで一致する。各productについて
`prop-branch` が「codomain sortはProp iff product result sortはProp」を与えるので、二つの
application conclusionのbranchも一致する。set版とprop版の `Take` が同じraw termに適用できると
仮定すると、共通のtarget \(T\) にdata sortingとProp sortingが得られ、sorting branch IHに反する。
sortability separationと四つ目のbridgeも、同じ表のsorting ruleとtyping ruleを交差して比較すれば
閉じる。bridgeのtypingが `type elem` ならそのsorting premiseへ進み、conversion等のdetourなら
source typingへ進む。raw headが異なるcore ruleは適用できず、同じheadの場合は表のstrict premiseへ
進むためである。従って四性質と
regularity / generationの同時帰納法は循環しない。

Program 側はconversionを持たず、各raw outer constructorに対応するtyping ruleが一つだけである。
variableはcontext declarationの一意性、function applicationはfunction premiseのIH、caseは各branch
のIHを使う。`continue`、`finish`、`run`、`runCase` はraw annotationが型を固定する。これでcategory
separationとProgram type uniquenessも従う。□

dependent elimination では、function の generation から product formation を回収し、argument
typing と substitution から substituted codomain の sorting を作る。このため primitive premise に
codomain sorting を追加する必要はない。`subset weak/prop` と `take equal` は入力 typing の
canonical origin を辿って、対応する `Power` または `Take` premise を回収する。

regularity のうち premise に結論の型形成が直接書かれていない caseを列挙する。

| conclusion rule | formation を回収する方法 |
| --- | --- |
| PTS variable | WF derivationの最後のcontext entryを反転する |
| dep intro | product formation premiseそのもの |
| dep elim | product generation、argument typing、mixed substitution |
| conversion | target sorting premise |
| proof term / provable | provability / typing premiseに相互IHを適用 |
| subset weak / subset prop | lifted typingのcanonical originから \(B:\Power A\) とbase typingを回収 |
| id elim | motive sortingと二つのargument typingからtarget applicationを形成 |
| take equal | `Take` typingのoriginから \(X,T,f\) と定値性を回収し、\(t:X\) と合わせる |
| Program variable | WF derivationの最後のvalue entryを反転する |
| return / thunk / force / function / sequence / let | immediate typing premiseのIHと対応するtype formation rule |
| reflection term | Program typingのregularityとreflection type formation |
| acc descent | first premiseから \(f,a\)、`Next` のequality/application generationから \(b:\operatorname{RfType}(A)\) を回収 |
| run / runCase | \(f:\operatorname{StepFun}(A,B)\) のregularityを反転して \(A,B\) のformationを回収 |

残るruleではformation premiseが明記されているか、conclusion自体がformation judgementである。
従って表とdirect caseで規則表全体が尽きる。

Program の formation と typing は conversion を持たず syntax-directed である。このため、

- value type と computation type の category は交わらない。
- 同じ Program value または computation に二つの型が付くなら、その型は alpha 同値である。
- `continue` / `finish` の型から payload の型と外側の `A,B` をそのまま回収できる。
- `run` / `runCase` の型から `F B` と、規則に明記された全 premise を回収できる。

最後の二点では raw annotation が component を固定している。旧 `Comp` PTS のような type-level
conversion、Compute rigidity、`RfType` の構文的 injectivity は必要ない。

PTS 側では通常の generation に加えて次を使う。

```text
Gamma |- RfTerm_P(p) : RfType(Q) :: Set_0
  => p has Program type P and
     RfType(P) equiv_s RfType(Q)

Gamma |= Acc_(A,B)(f,a)
  => f :v StepFun(A,B),
     a : RfType(A) :: Set_0
```

一行目の `P` と `Q` を構文的に同一視してはならない。PTS conversion が reflection 後の型を
同一視する可能性があるためである。subject reduction と soundness に必要なのは、表示された
`RfType` の convertibility と、その意味値の一致だけである。

regularity と generation の帰納法では、最後の rule が weakening、conversion、`type elem`、
`type sort`、`subset intro/weak` のいずれかなら strict premise へ進み、それ以外なら raw head に
対応する formation / introduction rule を反転する。この origin trace は有限導出の strict premise
だけを辿るので停止する。一般の PTS type uniqueness は仮定しない。

### 3.3 subject reduction

> [!important]
> **Program subject reduction。** \(\Gamma\vdash_cM:\underline B\) かつ
> \(M\Rightarrow_cM'\) なら \(\Gamma\vdash_cM':\underline B\) である。

**証明。** evaluation context と root rule の場合分けによる。

- force/thunk、function beta、sequence、value let は mixed substitution 補題で閉じる。
- `run(f,a)` から作る `runCase(f,a,force(f) @^c a)` の `RunInv` は等式反射律で得られる。
  `Terminates` premise はそのまま使う。
- `runCase(f,a,return(continue(a')))` の invariant と reflection reduction から
  `Next(f,RfTerm_A(a'),RfTerm_A(a))` を得る。`acc descent` により
  `Terminates(f,a')` が従うので、target の `run(f,a')` を型付けできる。
- finish case は constructor generation から \(b:_vB\) を得て `return(b):F B` とする。
- \(M\Rightarrow_cM'\) を `runCase` の第三引数で進める場合、reflection rule により
  `RfTerm(M) ->_s RfTerm(M')` なので、`prov-conv` で `RunInv` を輸送する。
- application と sequence の evaluation context は帰納法で計算 premise を輸送する。
- datatype case root は branch の value substitution 補題による。

continue case の二つ目では、`Rf-U-App`、force/thunk、Program beta、`Rf-F` を順に使うと
`continueFun` 側が `RfTerm(return(continue(a')))` へ進む。従って source の `RunInv` と同じ
equality まで conversion できる。

同じevaluation-context帰納法で、valid valuation \(\rho\) に対する

\[
\llbracket M\rrbracket_\rho=\llbracket M'\rrbracket_\rho
\tag{program-step-sound}
\]

も同時に示せる。四つのCBPV rootは2.4節の定義式、`run` / `runCase` は `run-laws`、datatype
caseはsemantic substitutionを使う。evaluation context caseはfunction application、binder
substitution、`RunCase` の外延性を使う。continue caseで `run-laws` の前提になる
\(a'\in\operatorname{Acc}_F\) は、source typingの `Terminates` と `RunInv` をSoundnessで
解釈して `acc-descent-law` を適用すれば得られる。従ってこの意味保存のstatementは4節の
fundamental theoremと同時に、Program step derivationの高さを副measureとして証明する。ここで
fundamental theoremを先取りして単独の仮定にはしない。

PTS 側では次の syntactic compatibility 条件が必要になる。

```text
(PC-Power)
Power(A) equiv_s Power(B)
  => A equiv_s B

(PC-Pi)
Pi x:A.B equiv_s Pi x:A'.B'
  => A equiv_s A'
     and B equiv_s B' under context conversion A equiv_s A'
```

両 clauseでは左右のouter termがwell-sortedであることを仮定する。この二つを合わせて `(PC)` と
呼ぶ。通常はconfluenceと `Power` / product headのinjectivityから得る補題である。reflection typeの
root reductionは右辺がproductを露出するため、`Rf-U-App` / `Rf-C-App` のgenerationには
`(PC-Pi)` をそのcommon reductに適用する。

> [!important]
> **条件付き PTS subject reduction。** `(PC)` のもとで、
> \(\Gamma\vdash t:T:s\) かつ \(t\Rightarrow_st'\) なら
> \(\Gamma\vdash t':T:s\) である。sorting についても同様である。

**証明。** compatible position に関する帰納法と root rule の場合分けによる。PTS beta は
substitution、`Pred` は subset generation、`(PC)`、application typingを使う。reflection rule は
Program の formation / typing generation と、直前の Program subject reduction を使う。
特に computation payload の rule

```text
M ->c M'
-------------------------------
RfTerm_B(M) ->s RfTerm_B(M')
```

は Program subject reduction をそのまま reflection typing に渡せる。`Rf-U-App` と `Rf-C-App` は
function / argument generation から target computation を型付けする。`RfType(F A)`、
`RfType(U B)`、`RfType(A => B)` は各 formation rule を PTS の `Set_0` formation に写す。
datatype の `Rf-Ind`、`Rf-Ctor` は宣言 signature と constructor generation を使う。□

3.4節で示す通り、現在の raw reduction について full confluence はまだ得られていないため、
`(PC)` もこの文書では未証明の syntactic 条件である。4--5節の集合モデルによる条件付き定理は
`(TC)` を直接仮定し、PTS subject reduction を前提には使わない。

`runCase` の continue reduction に `Acc` premiseが本質的である。これを落とすと target の
recursive `run` を型付けできず、subject reduction は成立しない。

### 3.4 raw conversion の未解決点

Program reduction は weak call-by-value evaluation context が次の redex を一意に選ぶため決定的で
あり、従って confluent である。datatype case を加えても scrutinee は value であり、constructor
tag は一意なのでこの結論は変わらない。

PTS reduction では、function position の reflection と Program step の peak は合流する。例えば

```text
RfTerm_(A=>B)(M) @ RfTerm_A(V),    M ->c M'
```

は、どちらを先に進めても `RfTerm_B(M' @c V)` へ進む。`RfTerm_U(A=>B)(thunk(M))` に
`Rf-Thunk` と `Rf-U-App` のどちらを先に使う peak も、force/thunk reduction により
`RfTerm_B(M @c V)` へ合流する。

しかし **argument position** には、現在の規則だけでは合流しない peak がある。\(\underline D\)
を computation type、\(\underline B\) を computation type とすると、

```text
S = RfTerm_((U D)=>B)(M) @ RfTerm_(U D)(thunk(N))
```

から

```text
S ->s RfTerm_B(M @c thunk(N))
```

と `Rf-C-App` を先に使える一方、argument の `Rf-Thunk` を先に使うと

```text
S ->s RfTerm_((U D)=>B)(M) @ RfTerm_D(N)
```

となる。後者の argument は computation reflection であって value reflection ではないため、
`Rf-C-App` の左辺には一致しない。例えば mixed context で

```text
D = F X,
h :v U D,
g :v U ((U D) => B),
N = force(h),
M = force(g)
```

とすれば両 reduct は open な stuck term になり、列挙済みの root ruleだけでは共通 reduct を持たない。
同じ peak は `Rf-U-App` の argument にもある。帰納型を加えると、argument の `Rf-Ctor` と
`Rf-App` の間にも同型の peak が生じる。

従って、現在の raw \(\Rightarrow_s\) について confluence を主張することはできない。ただし、
非合流だけから `(TC)` の反例が従うわけでもない。上の二 reduct は2節のモデルでは同じ値を持つ。
問題は、raw conversion path が型の付かない中間項を通り得るため、「typed root step の意味保存」
だけでは path 全体の意味保存を導けないことである。

この問題を閉じる方法は少なくとも二つある。

1. definitional equality を、両辺の sorting / typing derivation を持つ root equality、対称性、
   推移性、typed congruence から生成される judgement
   \(\Gamma\vdash T\simeq U:s\) と
   \(\Gamma\vdash t\simeq u:T:s\) として定義する。この場合、2節の root law に関する
   導出帰納法で `(TC)` が直接得られる。
2. raw reduction に synchronized reflection development を加える。具体的には、argument が
   `RfTerm_A(V)` から reflection reduction で進んだ履歴を witness として保持し、function application
   と argument reflection を一つの parallel redex として development する。追加 step は元の
   conversion で既に結ばれた二 reductを向き付けるので equational theory を広げないが、全 reflection
   constructor と datatype case を含む triangle proof が別途必要である。

一つ目を採用した体系では `(TC)` は次の単純な帰納法で証明できる。各 typed root equality は
2.4--2.6節の law、beta は semantic substitution、congruence は集合演算の外延性、対称性と推移性は
集合の等号を使う。二つ目は `system.md` の現在の raw \(\equiv_s\) を保つ方針だが、課題欄にある
critical-pair analysis を完了するまでは `(TC)` が残る。

typed congruence版の議論を定理として固定しておく。

> [!important]
> **typed equality soundness。** \(\Gamma\vdash T\simeq U:s\) なら、すべてのvalid
> valuation \(\rho\) で
> \(\llbracket T\rrbracket_\rho=\llbracket U\rrbracket_\rho\) である。typing equalityにも
> 同じ主張が成り立つ。

**証明。** typed equality derivationの構造帰納法による。generatorを尽くすと次の表になる。
この帰納法は独立にfundamental theoremを先取りするものではなく、4.1節の整礎化でphase 1として
`program-step-sound`、semantic substitution、fundamental theoremと同時に遂行する。

| equality constructor | 意味値が等しい理由 |
| --- | --- |
| reflexivity / symmetry / transitivity | 集合の等号の三性質 |
| ordinary constructor congruence | immediate argumentのIHとモデル演算補題の外延性 |
| binder congruence | domainのIHと、各 \(a\) でのbody IHによるfamily graphのpointwise equality |
| PTS beta | semantic substitutionとgraph beta。Prop branchでは両辺が \(\bullet\) |
| `Pred` root | 4.4節のdomain外で \(0\) を返すgraph applicationの計算 |
| `RfType` / return / thunk root | `reflection-value` |
| `Rf-U-App` / `Rf-C-App` | `reflection-laws` |
| reflected Program step | source typing / step certificateのrankが小さいこととphase 5の `program-step-sound` |
| `Rf-Ind` / `Rf-Ctor` | 6.1節の `inductive-reflection-laws` |

typed root equalityは定義により両endpointのsorting / typing derivationを保持するので、raw pathで
問題になったuntyped intermediateは生じない。表はcoreの全root schemaを覆い、帰納型の二schemaも
明記した。従って帰納法が閉じる。特にtype equalityへ適用すれば `(TC)` が得られる。□

## 4. soundness

### 4.1 導出に沿う解釈

PTS の lambda と application は result sort が `Prop` かどうかで data / proof branch が変わるため、
解釈は sorting / typing derivation に沿って定義する。sorting derivation
\(h:\Gamma\vdash t:s\) がproduct、lambda、applicationのどのsort branchを選んだかを解釈にも
記録し、それ以外のconstructorは2節の対応する演算を使う。typing derivationではregularityが返す
typeのsorting derivationを併せて保持する。Program interpretationはsyntax-directedだが、同じmixed
valuationを使う。

3.2節のbranch uniquenessにより、同じraw expressionに対する二導出がproof branchとdata branchを
別々に選ぶことはない。それでもpremiseのformation derivationは異なり得るため、次のcoherenceを
fundamental theoremと同時に示す。

> [!important]
> **導出 coherence。** 同じraw contextの二つのWF derivationは同じvalid valuation集合を定める。
> 同じraw PTS expressionの二sorting derivation、および二typing derivationは、表示型や
> universe levelが異なっても同じ値を定める。Programでは同じraw formation / typing judgementの
> 二導出が同じ値を定める。さらに \(\Gamma\vdash t:s\) と
> \(\Gamma\vdash t:s:t'\) のsorting/typing bridgeでもraw term \(t\) の値は一致する。

循環を避けるため、まず各有限導出を3.1--3.2節の構成に沿って有限なcertificateへ展開する。
certificate nodeは元のrule tag、全strict premise、regularityが選んだformation premise、generation
の有限origin trace、substitutionを使うcaseではその入力derivation、typed congruence版のconversion
caseではtyped equality derivationを保持する。これは元の導出高に
関する帰納法で構成され、各edgeは元のstrict premiseまたはorigin traceの一段短いnodeへ向く。
nodeのrankを「全child rankの最大値より1大きい数」と定める。従って生成されたderivationの見かけの
高さが元より大きくなっても、semantic inductionのrankが逆転することはない。同じrank内を次の
phase順に証明する。

```text
0  interpretation existence と support
1  typed equality soundness（typed congruence 版）
2  semantic substitution / renaming
3  context validity の coherence
4  fundamental membership / truth
5  typed Program step の意味保存
6  derivation coherence
```

順序は `(rank, phase)` の辞書式順序である。phase 1のbeta caseはbody / argumentのstrict childから
作る低rankのphase 2 semantic substitutionを使う。reflected Program stepは、root equalityが
保持するsource typing / step certificateのrankが小さいため、低rankのphase 5を使える。phase 4の
rule caseがpremise値の一致を必要とするとき、そのpremise derivationはstrict childなのでrankが
下がる。phase 5の `run` / `runCase` はsource typingのtermination / invariant premiseにphase 4を
適用するが、やはりrankが下がる。phase 6で二つのprovability derivationを比較するときだけ同rankの
phase 4を使い、両方の命題値が \(1\) である
ことから一致を得る。それ以外のcoherence callはstrict premiseへ進むのでrankが下がる。

phase 6の処理を明示する。weakeningならsupportにより追加valuation成分を捨てる。conversionでは
raw版なら `(TC)`、typed congruence版ならstrict childのphase 1で表示型の値を合わせ、source
typingへ進む。`type elem/type sort` は保存された
sorting/typing premiseへ、`subset intro/weak` はbase typingへ進む。これらを有限回剥がした両側が
core ruleなら、raw outer constructorは同じである。branch uniquenessと3.2節のgenerationにより
同じsemantic rule familyになり、対応するstrict premiseには「同じraw expressionでbranchが一致する」
というphase 6のIHを適用できる。モデル演算補題の外延性から結果値も一致する。`Take` のset/prop
ruleはtarget sortingのbranch uniquenessで区別される。
provabilityの異なるterminal ruleは
phase 4によりいずれも同じ命題値 \(1\) を与える。各detourは少なくとも一方のstrict premiseへ
進むので、このorigin比較も有限である。

phase 0のsupport statementは、二つのvaluationがraw expressionの全自由変数で一致すれば意味値も
一致する、というものである。raw syntaxの構造帰納法で、variableは仮定、binderはfreshな同じ値を
両valuationへ追加し、残りはモデル演算補題の外延性を使う。`run` typingのtermination proofや
`subset intro` のmembership proofのようにrule premiseだけに現れてraw termに保存されない証明は、
導出可能性を制限するがtermの解釈 clauseの引数にはならない。従ってそれらが追加context entryを
参照していてもsupportを壊さない。これがweakening caseでvaluation末尾を捨てられる理由である。

typed congruence 版では3.4節末尾の帰納法が `(TC)` の証明になる。現在のraw conversion版では
`(TC)` をこの同時定理の唯一の外部メタ条件として使う。

substitution の意味補題

\[
\llbracket e[u/x]\rrbracket_\rho
=\llbracket e\rrbracket_{\rho[x:=\llbracket u\rrbracket_\rho]}
\tag{semantic-substitution}
\]

は三 category の置換について同時構造帰納法で成り立つ。binder では family graph の外延性、
`RfType/RfTerm` では `reflection-value`、`run` では表示された \(A,B,F,a\) の値だけに演算が
依存することを使う。conversion caseは `(TC)` を使い、`RfTerm` のpayloadにはProgram構文についての
同じstructural IHを適用する。typed congruence版のconversionでは、strict childであるequality
certificateの低rank phase 1を使う。binder bodyと置換項のcertificateもstrict childなので、
上のmeasureに適合する。

### 4.2 fundamental theorem

> [!important]
> **条件付き Soundness。** `(TC)` を仮定する。
> 各 \(h:\operatorname{WF}(\Gamma)\) は2.1節の再帰によりvalid valuation集合
> \(\operatorname{Val}_h(\Gamma)\) を定め、同じcontextの二つのWF derivationが定める集合は等しい。
> さらに \(\rho\in\operatorname{Val}_h(\Gamma)\) なら、
>
> \[
> \begin{aligned}
> \Gamma\vdash T:s
> &\Rightarrow \llbracket T\rrbracket_\rho\in D_s,\\
> \Gamma\vdash t:T:s
> &\Rightarrow \llbracket T\rrbracket_\rho\in D_s
>      \land\llbracket t\rrbracket_\rho\in\llbracket T\rrbracket_\rho,\\
> \Gamma\vDash P
> &\Rightarrow \llbracket P\rrbracket_\rho=1,\\
> \Gamma\vdash A\ \mathsf{vtype}
> &\Rightarrow \llbracket A\rrbracket_\rho\in U_0,\\
> \Gamma\vdash\underline B\ \mathsf{ctype}
> &\Rightarrow \llbracket\underline B\rrbracket_\rho\in U_0,\\
> \Gamma\vdash_vV:A
> &\Rightarrow \llbracket V\rrbracket_\rho\in\llbracket A\rrbracket_\rho,\\
> \Gamma\vdash_cM:\underline B
> &\Rightarrow \llbracket M\rrbracket_\rho\in\llbracket\underline B\rrbracket_\rho.
> \end{aligned}
> \]

**証明。** 4.1節の `(rank, phase)` 帰納法のphase 4である。WF caseではcontext validityを、
formation / typing / provability caseでは対応するstrict premiseのphase 4と、必要ならphase 2・3、
または低rankのphase 6を使う。conversion caseはraw版では `(TC)`、typed congruence版ではstrict
childであるphase 1を使う。provable と proof term の相互参照も
premiseの導出高が真に小さい。各primitive ruleのmembership計算は次節の監査表で尽くす。従って
未処理のterminal ruleはない。□

### 4.3 primitive rule の監査

`system.md` の core rule を順に検査する。複数 rule を一行にまとめた箇所でも、各 conclusion に
使う law を分けて記す。

| rule | soundness の理由 |
| --- | --- |
| empty | 空 tuple が valid |
| axiom | \(U_i\in U_{i+1}\)、\(\{0,1\}\in U_\omega\) |
| PTS start | premise の carrier の要素を valuation に追加 |
| weak sort / weak type | valuation の末尾を捨てる semantic weakening |
| weak sort / weak type over Program | 同上。raw PTS term の support だけを使う |
| PTS variable | context validity の対応成分 |
| conversion | `(TC)` で source/target type の値が等しい |
| dep form | 2.2節の全 sort case の product closure |
| dep intro | graph lambda、または Prop branch の \(\bullet\) |
| dep elim | graph application、または Prop fiber の `proof-membership` |
| type elem / type sort | `sort-membership` |
| provable | \(t\in P\)、\(P\in\{0,1\}\) から \(P=1\) |
| proof term | \(P=1\) から \(\bullet\in P\) |
| power set form | Grothendieck universe の powerset closure |
| power set intro | `TypeLift(A,B)=B` と \(B\subseteq A\) |
| predicate | `truth(t in B)` は Prop の要素 |
| subset form | separation と powerset membership |
| subset intro | membership proofから \(t\in B\)、従って \(t\in\operatorname{TypeLift}(A,B)\) |
| subset weak | \(B\subseteq A\) |
| subset prop | lifted termの membership \(t\in B\) |
| id form | `truth(a=b)` は Prop の要素 |
| id intro | reflexivity により equality value は \(1\) |
| id elim | equality premiseで \(a=b\)、semantic substitution で motive の値を輸送 |
| exists form | `truth(A nonempty)` は Prop の要素 |
| exists intro | witness \(e\in A\) により \(A\ne\varnothing\) |
| take elim set | existence、定値性、`take-law` |
| take elim prop | existence と function typing から target proposition が \(1\) |
| take equal | \(t\in X\) と `take-law` |
| value type start | 任意の \(U_0\) の要素を type valuation に追加 |
| value type variable | context validity の対応する \(U_0\) 成分 |
| value start | \(a\in\llbracket A\rrbracket\) を valuation に追加 |
| Program weak | valuation の末尾を捨てる |
| `F` form / `U` form | carrier を変えない |
| function form | \(U_0\) の function-set closure |
| run step form | \(U_0\) の finite tagged-sum closure |
| Program value variable | context validity の対応成分 |
| return / thunk / force | 三つとも carrier 上の恒等値 |
| Program function intro | functional graph introduction |
| Program function elim | functional graph elimination |
| sequence | first computation の値を valid な binder valuation に使う |
| value let | value premiseを valid な binder valuation に使う |
| continue intro | \(a\in A\) から \((0,a)\in\operatorname{RunStep}(A,B)\) |
| finish intro | \(b\in B\) から \((1,b)\in\operatorname{RunStep}(A,B)\) |
| reflection value/computation type | Program carrier は \(U_0=D_{\mathrm{Set}_0}\) に属する |
| reflection value/computation term | `reflection-value` と Program typing の IH |
| acc form | `truth` の値は Prop に属する |
| acc intro | `next-law` と `acc-intro-law` |
| acc descent | `next-law` と `acc-descent-law` |
| run | termination premiseと rank recursion により結果が \(B\) に属する |
| run case | invariant \(u=F(a)\)、tag場合分け、`run-laws` |

これで `Acc と run` までに明記された全 primitive rule を覆った。

表のうち複数のpremiseを組み合わせるcaseを展開する。

**dependent introduction。** data branchでは、任意の \(a_0\in A_0\) に対するbody premiseのIHから
\(m_0(a_0)\in B_0(a_0)\) を得る。従ってlambda graphのdomainは \(A_0\) で、各値が対応fiberに
入るため、\(\operatorname{Lam}_z(A_0,m_0)\in\Pi_z(A_0,B_0)\) である。Prop branchでは同じIHと
\(B_0(a_0)\in\{0,1\}\) から全 \(a_0\) について \(B_0(a_0)=1\) が従う。ゆえにproductの値は
\(1\) であり、lambdaの値 \(\bullet\) はその唯一の要素である。

**dependent elimination。** function premiseのIHによりdata branchでは
\(f_0\in\Pi_z(A_0,B_0)\)、argument premiseから \(a_0\in A_0\) を得る。graph
eliminationで \(\operatorname{app}(f_0,a_0)\in B_0(a_0)\) となり、semantic substitutionにより
\(B_0(a_0)=\llbracket B[a/x]\rrbracket\) である。Prop branchではfunction membershipから
全fiberが \(1\) と分かり、`proof-membership` により \(\bullet\) がtarget fiberに属する。

**equality elimination。** equality premiseのphase 4から
\(\operatorname{truth}(a_0=b_0)=1\)、従って \(a_0=b_0\) を得る。motive sortingとsemantic
substitutionにより、最後のprovability premiseは \(P_0(a_0)=1\) を表す。集合の等号でargumentを
置き換えると \(P_0(b_0)=1\) であり、もう一度semantic substitutionを使えばconclusionの
proposition値が \(1\) になる。

**`Take`。** set caseではexistence premiseから \(x_0\in X_0\) を一つ得る。function typingに
より \(f_0:X_0\to T_0\) はfunctional graphである。定値性premiseの二重productを展開すると

\[
\forall x,y\in X_0.\ \operatorname{app}(f_0,x)=\operatorname{app}(f_0,y).
\]

従ってimageは \(\{\operatorname{app}(f_0,x_0)\}\) であり、`take-law` から `Take` の値は
\(T_0\) に属する。prop caseでは \(f:X\to T\) 自体がproof productである。そのmembershipは
全 \(x\in X_0\) で \(T_0=1\) を意味し、existenceと合わせて \(\bullet\in T_0\) を得る。
`take equal` では第二premiseの \(t_0\in X_0\) と同じ定値性から
\(\operatorname{Take}(X_0,T_0,f_0)=\operatorname{app}(f_0,t_0)\) が従う。

**`Acc`。** `acc intro` のbinder contextを任意の \(b_0\in A_0\) で評価する。内側のimplication
の値が \(1\) であることは、`next-law` により

\[
b_0<_F a_0\Longrightarrow b_0\in\operatorname{Acc}_F
\]

と同値である。外側のproductを展開して全 \(b_0\) を量化すると `acc-intro-law` の前提になり、
conclusionは \(a_0\in\operatorname{Acc}_F\) となる。`acc descent` は二premiseを
`next-law` で展開すれば `acc-descent-law` そのものである。

**`run` と `runCase`。** `Terminates` のphase 4は
\(a_0\in\operatorname{Acc}_F\) を与える。従って2.5節のrank帰納法から
\(\operatorname{Run}(F,a_0)\in B_0\) である。`runCase` ではさらに `RunInv` から
\(u_0=\operatorname{app}(F,a_0)\) を得る。tagがcontinueなら `acc-descent-law` を使って再帰先に
rank帰納法を適用し、finishならfunction typingからpayloadが \(B_0\) に属する。よってどちらも
\(\operatorname{RunCase}(F,a_0,u_0)\in B_0\) である。

### 4.4 reduction の意味保存

conversion caseで使った意味保存を root ごとに確認する。

- PTS beta は `semantic-substitution` と graph beta による。proof branch では両辺が
  \(\bullet\) である。
- `Pred(A,{x:B | P},t)` の値は

  \[
  \operatorname{truth}(t\in B\land\operatorname{app}(P,t)=1).
  \]

  ここで右辺のlambdaはproof termを作るlambdaではない。body \(P\) をtermとして
  \(P:\mathrm{Prop}:\mathrm{PropKind}\) と型付けするため、product formationは
  \((\mathrm{Set}_i,\mathrm{PropKind},\mathrm{PropKind})\) のdata branchを使う。従って右辺の
  lambda graph は domain が \(B\) であり、domain 外では application が \(0\) を返す。
  従ってこれは `((lambda x:B.P) @ t)` の値と等しい。`A` と `B` の構文的一致を仮定しない。
- Program の force/thunk、beta、sequence、let は2.4節の定義式による。
- `run` と二つの `runCase` root は `run-laws` による。continue case の accessibility は typed
  source の termination と invariant から得る。
- reflection の各 root は `reflection-laws` による。computation payload の step は Program
  reduction の意味保存を使う。
- compatible step は、変化しない引数の IH、binder family の pointwise equality、集合演算の
  外延性による。

これらは各 **typed** root equality と typed congruence の意味保存を示す。従って3.4節の
typed congruence 版では、有限 path とその逆向きを含む conversion の両端は同じ値を持つ。
現在の raw \(\equiv_s\) については、型の付かない中間項を除去する completion が未完了なので、
この節だけから `(TC)` を導いたことにはならない。

## 5. `falseProp`

空文脈で `Prop :: PropKind` である。`P:Prop:PropKind` を追加すると variable rule から
`P :: Prop` となり、`(PropKind,Prop,Prop)` が \(\mathcal R\) に属するので

\[
\mathit{falseProp}=(P:\mathrm{Prop})\to P:\mathrm{Prop}
\]

を形成できる。その標準導出による空 valuation での意味は

\[
\begin{aligned}
\llbracket\mathit{falseProp}\rrbracket
&=\Pi_{\mathrm{Prop}}(\{0,1\},P\mapsto P)\\
&=\operatorname{truth}(\forall P\in\{0,1\}.\ P=1)\\
&=0.
\end{aligned}
\]

最後の等号は \(0\in\{0,1\}\) かつ \(0\ne1\) による。別の formation derivation も
同じ値を与えることを確認する。上の標準導出を \(h_0:\varnothing\vdash
\mathit{falseProp}:\mathrm{Prop}\) とする。任意の
\(h:\varnothing\vdash\mathit{falseProp}:s\) に3.2節のsorting branch uniquenessを
\(h_0\) とともに適用すると \(\epsilon(s)=\mathsf{proof}\)、従って \(s=\mathrm{Prop}\) である。
raw版では \(\mathit{falseProp}\equiv_s\mathit{falseProp}\) と `(TC)` を \(h_0,h\) に適用し、
typed congruence版では4.1節のphase 6を適用すれば、どちらも
\(\llbracket\mathit{falseProp}\rrbracket_h=0\) を得る。

`(TC)` を仮定する。もし \(\varnothing\vDash\mathit{falseProp}\) なら、空 valuation は valid
なので条件付き Soundness から
\(\llbracket\mathit{falseProp}\rrbracket=1\) となり、上の \(0\) と矛盾する。

もし \(\varnothing\vdash t:\mathit{falseProp}:s\) なら、条件付き Soundness から

\[
\llbracket t\rrbracket\in
\llbracket\mathit{falseProp}\rrbracket=\varnothing
\]

となるが、空集合に要素はない。従って主定理が示された。\(\square\)

## 6. 帰納型拡張

### 6.1 `system.md` に明記済みの規則

有限個の constructor を持つ well-formed な strictly-positive declaration を固定する。
各parameter carrier \(A_\ell^0\in U_0\) と、recursive carrierの候補 \(Z\in U_0\) を固定する。
value / computation type expressionのcarrier \(E^v_A(Z)\)、\(E^c_{\underline B}(Z)\) を

\[
\begin{aligned}
E^v_{X_\ell}(Z)&=A_\ell^0,
&E^v_{I^v(\vec X)}(Z)&=Z,\\
E^v_{\mathrm U\underline B}(Z)&=E^c_{\underline B}(Z),
&E^v_{\operatorname{RunStep}(A,B)}(Z)
  &=(\{0\}\times E^v_A(Z))\cup(\{1\}\times E^v_B(Z)),\\
E^c_{\mathrm F A}(Z)&=E^v_A(Z),
&E^c_{A\Rightarrow\underline B}(Z)
  &=(E^c_{\underline B}(Z))^{E^v_A(Z)}
\end{aligned}
\]

と構造再帰で定める。最後のfunction spaceでrecursive occurrenceはdomain \(A\) に現れない。
これは `system.md` のstrict positivity条件が保証すべき正確なvariance条件である。constructor
signatureから

\[
P_{\vec A^0}(Z)
=\coprod_i\prod_{j<k_i}E^v_{A_{ij}}(Z)
\]

を得る。これは固定した小さいdomainからの正のfunction fieldを許すstrictly-positive functorである。
そのinitial algebraは対応するW-type、すなわちconstructor tagとfieldを持つwell-founded treeの集合
として構成できる。Grothendieck universeはsmall W-typeに閉じているので、carrier

\[
\mu P_{\vec A^0}\in U_0
\]

を取れる。constructor mapはtagged tupleを作り、W-type recursionによりcase / recursorが一意に
定まる。negative occurrenceを許すと上の \(P\) は共変functorにならず、この構成は使えない。

Program datatype と Set の鏡像を同じ carrier に解釈し、両側の constructor を同じ tagged tuple に
解釈する。

\[
\begin{aligned}
\llbracket I^v(\vec A)\rrbracket
&=\mu P_{\llbracket\vec A\rrbracket}
=\llbracket I^s(\operatorname{RfType}(\vec A))\rrbracket,\\
\llbracket C_i^v[\vec A](\vec V)\rrbracket
&=(i,\llbracket\vec V\rrbracket)
=\llbracket C_i^s[\operatorname{RfType}(\vec A)]
  (\overrightarrow{\operatorname{RfTerm}(V)})\rrbracket.
\end{aligned}
\tag{inductive-reflection-laws}
\]

二つ目の等式はreflected argumentが実際に \(\operatorname{RfTerm}(V_j)\) の場合である。
一般のSet constructor ruleに現れる \(t_j\) についても、premiseから
\(\llbracket t_j\rrbracket\in E^v_{A_{ij}}(\mu P)\) を得るので、同じtagged tupleが
\(\mu P\) に属する。

Program case は tag を読み、対応 branch を field values で評価する。従って Program の
inductive type formation、constructor introduction、case typing、reflected type formation、
reflected constructor introduction は sound である。case reduction は semantic substitution、
`Rf-Ind` と `Rf-Ctor` は `inductive-reflection-laws` により意味を保存する。

この解釈は `Acc` と `run` を変えない。state または result carrier が \(\mu P\) でも、step
function は依然として \(A\to\operatorname{RunStep}(A,B)\) という functional graphであり、
2.5節の rank recursionをそのまま適用できる。

### 6.2 完成した帰納型規則への拡張条件

Set case / induction を加えた体系全体へ主定理を拡張するには、まず次の1--4をdeclarationごとに
満たす必要がある。raw \(\equiv_s\) を保つ場合だけ、さらに5が必要である。

1. positivity judgement が negative occurrence を拒否し、各 declaration が上の
   \(P_{\vec A}\) を一意に定める。
2. declaration 名、constructor 名、parameter と field signature が一意である。
3. 生成される Set case / induction の raw syntax、typing、reduction、compatible context が有限個の
   schema として固定される。
4. mixed substitution、generation、Program/PTS subject reduction が生成規則について成り立つ。
5. coreのsynchronized completionを含むparallel reductionについて、追加critical peakがすべて
   joinableである。

最後の条件で新たに現れる代表的な peak は、constructor を `Rf-Ctor` で Set 側へ写してから Set
case を進める path と、Program case を先に進めてその結果を `RfTerm` で反映する path である。
両 path が対応 branch の

```text
RfTerm(M_i[fields/x_i])
```

へ進むよう、生成される reflection/case rule を定める必要がある。Set induction の soundness は
\(\mu P\) の W-type rank に関する整礎帰納法と Prop の proof irrelevance から従う。

typed congruence版では1--4と各typed rootの `inductive-reflection-laws` だけで、3--4節の帰納法に
各declarationの有限個のcaseを追加できる。raw conversion版では1--5を使う。どちらも5節の
`falseProp` の計算は変わらないため、その**完成後の体系**へ対応する主定理が拡張される。現状の
`system.md` では1と3が未定義であり、raw版ではcoreを含む5も未完了なので、この段落は条件付きの
拡張定理である。

## 7. 一般再帰についての帰結

operational rule だけなら、ある \(f,a\) に対して

```text
run(f,a)
  -> runCase(f,a,force(f) @c a)
  ->* runCase(f,a,return(continue(a)))
  -> run(f,a)
```

という raw loop は作れる。しかし、この term の `run` typing には
\(a\in\operatorname{Acc}_F\) を表す termination proof が必要である。自己 loop は
\(a<_Fa\) を意味するので、\(a\) が accessibility iteration に初めて現れる stage より前に
同じ \(a\) が現れなければならず、rank の最小性に反する。従ってこの場合
\(a\notin\operatorname{Acc}_F\) であり、条件付き Soundness により `(TC)` のもとでは空文脈で
termination proof を構成できない。

従って現在の `run` は任意の一般不動点ではなく、Set 側で accessibility が証明された
deterministic CBPV step function の well-founded evaluator である。集合モデルと全 primitive rule
の membership law は構成済みであり、残る core の条件は `(TC)` である。従って

- conversion-free fragment と typed congruence 版は、ZFC と1節の universe tower に相対して
  `falseProp` の provability と inhabitance の意味で無矛盾である。
- `system.md` に現在書かれた raw \(\equiv_s\) をそのまま使う版は、3.4節の synchronized
  critical-pair completion、またはそれと同等な `(TC)` の別証明を完了した時点で同じ結論を得る。
- 帰納型全体については、これに加えて6.2節の未定義な生成規則を固定する必要がある。
