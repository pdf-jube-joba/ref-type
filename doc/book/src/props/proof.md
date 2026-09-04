# `system.md` の相対無矛盾性

## 1. 方針と主定理

[`system.md`](../system.md) の Set/Prop calculus 全体を \(\mathcal S_\Box\)、そこから
`Box`、`box`、`Force`、boxed application とその規則を除いた体系を \(\mathcal S_0\) とする。
それぞれの Set reduction と conversion を
\(\Rightarrow_\Box,\equiv_\Box\) と \(\Rightarrow_0,\equiv_0\) と書く。

証明は次の二段階に分かれる。

1. raw syntax 上の Box 消去により、\(\mathcal S_\Box\) の Set/Prop 導出を
   \(\mathcal S_0\) の導出へ移す。
2. \(\mathcal S_0\) に集合モデルを与え、`falseProp` が証明不能であることを示す。

Program syntax は Box payload に使うが、\(\mathcal S_0\) の object language には含めない。
また、未定義の Set case / induction を除く core calculus をまず対象とする。

Box-free conversion について次を仮定する。

> [!important]
> **Box-free typed conversion soundness (`TC0`)。**
> \[
> \Gamma\vdash_0T:s,\quad\Gamma\vdash_0T':s,\quad T\equiv_0T'
> \]
> なら、任意の valid valuation \(\rho\) で
> \(\llbracket T\rrbracket_\rho=\llbracket T'\rrbracket_\rho\) である。

typed equality を採用すればこれは equality derivation の帰納法で従う。raw
\(\equiv_0=(\Rightarrow_0\cup\Leftarrow_0)^*\) を使う場合は、Box-free reduction の
confluence と subject reduction、または同等の lemma が別途必要である。

外部理論として ZFC と Grothendieck universe
\[
U_0\in U_1\in\cdots\in U_\omega\in W
\]
を仮定する。

> [!important]
> **主定理。** `TC0` と上の集合論的仮定のもとで
> \[
> \mathit{falseProp}:=(P:*^p)\to P
> \]
> と置くと
> \[
> \neg(\emptyset\vDash_\Box\mathit{falseProp}),\qquad
> \neg\exists t,s.\ \emptyset\vdash_\Box t:\mathit{falseProp}:s
> \]
> が成り立つ。

## 2. raw reflection

Box 消去を raw conversion に適用するため
\[
\operatorname{RfTerm}:\mathsf{ProgramTermSyntax}\to\mathsf{SetTermSyntax}
\tag{raw-RfTerm}
\]
を raw syntax 上の全域写像とする。`system.md` の定義式は型添字を使わない。
型 \(P\) は写像の引数ではなく、reflected term の typing property に現れる。

Program variable は既存の Set variable と衝突しない専用名へ injective に写し、binder は
alpha-renaming する。構造帰納法により
\[
\begin{aligned}
\operatorname{RfType}(P[X:=A])
&=_\alpha\operatorname{RfType}(P)[X:=\operatorname{RfType}(A)],\\
\operatorname{RfTerm}(p[x^v:=V])
&=_\alpha\operatorname{RfTerm}(p)[x:=\operatorname{RfTerm}(V)]
\end{aligned}
\tag{Rf-substitution}
\]
が成り立つ。

Program type formation の導出帰納法から
\[
\begin{aligned}
\Delta\vdash A\ \mathsf{vtype}
&\Rightarrow\operatorname{RfCtx}(\Delta)\vdash_0\operatorname{RfType}(A):*^s_0,\\
\Delta\vdash\underline B\ \mathsf{ctype}
&\Rightarrow\operatorname{RfCtx}(\Delta)\vdash_0\operatorname{RfType}(\underline B):*^s_0
\end{aligned}
\tag{Rf-formation}
\]
を得る。一般の Program typing から reflected term の Set typing が従うとは主張しない。
Program `run` に Acc premiseがないためであり、その不足を埋めるのが well-termination である。

> **Raw Program simulation.**
> \[
> p\Rightarrow_cp'\Rightarrow
> \operatorname{RfTerm}(p)\Rightarrow_0^*\operatorname{RfTerm}(p').
> \tag{Rf-simulation}
> \]

**証明。** Program reduction の導出帰納法による。force/thunk は0 step、beta、sequence、let は
`Rf-substitution` と Set beta、`run` と二つの `runCase` は対応する Set root に写る。
evaluation context は Set compatible context に写る。□

## 3. Box 消去と保守性

通常の Set/Prop constructor には準同型に作用させ、Box constructor では
\[
\begin{aligned}
\lfloor\operatorname{Box}(P)\rfloor&:=\operatorname{RfType}(P),&
\lfloor\operatorname{box}_P(p)\rfloor&:=\operatorname{RfTerm}(p),\\
\lfloor\operatorname{Force}_P(t)\rfloor&:=\lfloor t\rfloor,&
\lfloor f@^{\operatorname{Box}}a\rfloor&:=\lfloor f\rfloor@\lfloor a\rfloor
\end{aligned}
\tag{Box-clear}
\]
とする。context 中の型にも再帰的に作用させる。構造帰納法から
\[
\lfloor t[x:=u]\rfloor=_\alpha\lfloor t\rfloor[x:=\lfloor u\rfloor]
\tag{clear-substitution}
\]
を得る。

> **Reduction simulation.**
> \[
> t\Rightarrow_\Box t'\Rightarrow
> \lfloor t\rfloor\Rightarrow_0^*\lfloor t'\rfloor.
> \tag{clear-step}
> \]

**証明。** Box-free root は同じ root に写る。box step は `Rf-simulation` に写る。
force-box は両辺とも \(\operatorname{RfTerm}(r)\) なので0 stepである。boxed application も
\[
\operatorname{RfTerm}(M)@\operatorname{RfTerm}(V)
=\operatorname{RfTerm}(M@^cV)
\]
なので0 stepである。compatible context も消去後の compatible context に写る。□

従って、中間項の typing を仮定せず
\[
t\equiv_\Box t'\Rightarrow\lfloor t\rfloor\equiv_0\lfloor t'\rfloor
\tag{clear-conversion}
\]
が成り立つ。

> **Derivation clearing.**
> \[
> \begin{aligned}
> \operatorname{WF}_\Box(\Gamma)&\Rightarrow\operatorname{WF}_0(\lfloor\Gamma\rfloor),\\
> \Gamma\vdash_\Box T:s&\Rightarrow\lfloor\Gamma\rfloor\vdash_0\lfloor T\rfloor:s,\\
> \Gamma\vdash_\Box t:T:s&\Rightarrow
> \lfloor\Gamma\rfloor\vdash_0\lfloor t\rfloor:\lfloor T\rfloor:s,\\
> \Gamma\vDash_\Box P&\Rightarrow\lfloor\Gamma\rfloor\vDash_0\lfloor P\rfloor.
> \end{aligned}
> \]

**証明。** 四種の導出の同時帰納法による。conversion case は `clear-conversion` を使う。
box type は `Rf-formation`、box intro は well-termination の第二成分を weakening する。
force box の消去は premise そのものである。boxed application は
\(\operatorname{RfType}(A\Rightarrow\underline B)
=\operatorname{RfType}(A)\to\operatorname{RfType}(\underline B)\)
と通常の Set application を使う。□

Box-free judgement 上で消去は恒等なので
\[
\mathcal S_\Box\vdash J\Rightarrow\mathcal S_0\vdash J
\tag{conservativity}
\]
を得る。

## 4. Box-free Set/Prop の集合モデル

\(0=\varnothing,\bullet=\varnothing,1=\{\bullet\}\) とし
\[
\begin{aligned}
\llbracket *^s_i\rrbracket&=U_i,&
\llbracket\sq^s_i\rrbracket&=U_{i+1},\\
\llbracket *^p\rrbracket&=\{0,1\},&
\llbracket\sq^p\rrbracket&=U_\omega
\end{aligned}
\]
とする。context valuation は \(x:T:s\) に \(\llbracket T\rrbracket\) の要素を割り当てる。
\(\operatorname{truth}(Q)\) は \(Q\) が真なら1、偽なら0とする。

codomain sort が \(*^p\) でない product は functional graph の集合
\[
\Pi(A,B)=\{f\mid\operatorname{dom}(f)=A\land
\forall x\in A.\operatorname{app}(f,x)\in B(x)\}
\]
とし、lambda/application も graph の形成と適用で解釈する。codomain sort が \(*^p\) なら
\[
\Pi_p(A,B)=\operatorname{truth}(\forall x\in A.\ B(x)=1)
\]
とし、proof lambda と proof application の値を \(\bullet\) とする。
各 product rule の closure は、Set/Kind では該当する
\(U_{\max(i,j)},U_{\max(i,j)+1},U_{\max(i+1,j)}\)、PropKind では \(U_\omega\) の
dependent-product closureから従う。

追加演算は
\[
\begin{aligned}
\operatorname{Power}(A)&=\{B\mid B\subseteq A\},&
\operatorname{Subset}(A,P)&=\{x\in A\mid\operatorname{app}(P,x)=1\},\\
\operatorname{Ty}(A,B)&=B,&
\operatorname{Pred}(A,B,t)&=\operatorname{truth}(t\in B),\\
\operatorname{Eq}(a,b)&=\operatorname{truth}(a=b),&
\operatorname{Exists}(A)&=\operatorname{truth}(A\ne\varnothing)
\end{aligned}
\]
とする。set-valued `Take` は
\[
\operatorname{Take}(X,T,f)=\bigcup\{\operatorname{app}(f,x)\mid x\in X\}
\]
とする。\(X\) が非空で \(f\) が定値 \(y\in T\) ならこれは \(y\) である。
proposition-valued `Take` と `Proof` は \(\bullet\) と解釈する。

\[
\operatorname{RunStep}(A,B)=(\{0\}\times A)\cup(\{1\}\times B)
\]
とし、continue/finish は二つの tag への injection、recursor は tag による場合分けとする。
\(F:A\to\operatorname{RunStep}(A,B)\) に対し
\[
b<_Fa\Longleftrightarrow\operatorname{app}(F,a)=(0,b)
\]
とし、\(\Phi_F(X)=\{a\in A\mid\forall b<_Fa.\ b\in X\}\) の最小不動点を
\(\operatorname{Acc}_F\) とする。powerset 上の transfinite iteration と Hartogs の補題から存在し
\[
(\forall b<_Fa.\ b\in\operatorname{Acc}_F)\Rightarrow a\in\operatorname{Acc}_F,\qquad
a\in\operatorname{Acc}_F\land b<_Fa\Rightarrow b\in\operatorname{Acc}_F
\tag{acc-laws}
\]
を満たす。

accessible element の rank に関する well-founded recursion で
\[
\operatorname{Run}(F,a)=
\begin{cases}
\operatorname{Run}(F,a')&F(a)=(0,a'),\\
b&F(a)=(1,b)
\end{cases}
\quad(a\in\operatorname{Acc}_F)
\]
と定め、domain 外は0で全域化する。typed \(F\) と \(a\in\Acc_F\) について
\(\operatorname{Run}(F,a)\in B\) である。`RunCase` も tag により
\(\operatorname{Run}(F,a')\) または \(b\) を返す。
Acc と equality premise のもとで三つの Set `run` reduction equation が成立する。

解釈は typing derivation が選ぶ proof/data branch に沿って定義する。branch uniqueness と
semantic substitution を通常の同時帰納法で示し、conversion case に `TC0` を使う。

> **Box-free soundness.** valid \(\rho\) について
> \[
> \begin{aligned}
> \Gamma\vdash_0T:s&\Rightarrow\llbracket T\rrbracket_\rho\in\llbracket s\rrbracket,\\
> \Gamma\vdash_0t:T:s&\Rightarrow\llbracket t\rrbracket_\rho\in\llbracket T\rrbracket_\rho,\\
> \Gamma\vDash_0P&\Rightarrow\llbracket P\rrbracket_\rho=1.
> \end{aligned}
> \]

**証明。** WF、sorting、typing、provability の導出の同時帰納法による。
PTS rules は universe closure と graph/proof product、conversion は `TC0` を使う。
power/subset は powerset と separation、equality は集合の等号、Take は非空性と定値性、
RunStep は tagged sum、Acc は `acc-laws`、run/runCase は rank recursion を使う。
provable と proof term の相互参照も有限導出の高さが下がる。□

## 5. `falseProp`

\((\sq^p,*^p,*^p)\in\mathcal R\) であり
\[
\llbracket\mathit{falseProp}\rrbracket
=\operatorname{truth}(\forall P\in\{0,1\}.\ P=1)=0
\]
である。従って Box-free soundness から
\(\emptyset\nvDash_0\mathit{falseProp}\) であり、これを型とする項も存在しない。
`falseProp` は Box-free なので `conservativity` により \(\mathcal S_\Box\) でも同様である。□

## 6. 帰納型拡張

帰納型を含めるには次を要する。

1. declaration environment と positivity を厳密に定義する。
2. `F` / `U` の消去後も reflected signature が strictly positive だと保証する。
3. Set datatype を所定の \(U_i\) 内の tagged least fixed point として構成する。
4. Set case/induction の syntax、typing、reduction を定義し、その集合解釈を示す。
5. Program case の reflection が Set case reduction を simulation すると示す。
6. 生成規則を含めて `TC0` を示す。

\(I^v\) 自体の集合モデルは不要である。必要なのは reflection の構文的可換性であり、
集合モデルが直接解釈するのは \(I^s\) だけである。生成規則が未確定な現在、帰納型を含む主張は
上の条件に相対化する。

## 7. 残る条件

- Program typing 全体の soundness や強正規化は主張しない。
- Box payload の operational な停止性はここでは示さない。保守性に必要なのは
  well-termination の定義に含まれる Set typing である。
- raw Box-free conversion に対する `TC0` は独立したメタ定理として残る。
- datatype 規則が未完成な間、無条件の対象は core calculus である。

旧証明の raw `RfType` / `RfTerm` constructor 間の critical pair は存在しない。
reflection は raw Program syntax から Box-free Set syntax へのメタレベル写像であり、
Box 付き側の conversion は `clear-conversion` により一括して Box-free conversion へ移る。
