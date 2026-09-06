# `system.md` の相対無矛盾性

> [!warning]
> **現行規則の無矛盾性証明は未完成である。**
> 0 節の反例は、formation premise を明示する修正前の規則に対するものである。
> 現在の `system.md` では `run` / `runCase` を含む規則を修正済みであり、
> その反例の導出は使えない。ただし修正後の subject reduction とモデルの
> 健全性はまだ証明していない。残りを `TC0` だけに相対化して
> 証明済みとすることはできない。
> この反例は `falseProp` の導出を与えるものではなく、体系自体の矛盾を主張しない。

## 0. 修正前の規則に対する反例

0.1、0.2 節は修正前の規則の記録であり、現在の `system.md` の規則は使わない。
ここでの旧 `run` / `runCase` は \(k=\max(i,j)\) を共有し、
\(B:*^s_j\) の formation premise を持たなかった。
旧 `power set intro` も \(B:\Power A:*^s_i\) だけを premise とし、
\(A:*^s_i\) を別に要求しなかった。

### 0.1 `runCase` の結果 level が制約されていない

以下、変数の上付き sort を省略した場合も context の注釈を保持する。
\(A,B:*^s_1\)、\(a:A:*^s_1\)、\(b:B:*^s_1\) とし、

\[
f:A\to\operatorname{RunStep}(A,B):*^s_1
\]

を context に置く。さらに

\[
h:\operatorname{Acc}_{A,B}(f,a):*^p,
\qquad
e:(f@a=\operatorname{finish}_{A,B}(b)):*^p
\]

を追加し、この context を \(\Gamma\) とする。
Acc と equality の formation、context start により \(\operatorname{WF}(\Gamma)\)。
\(h,e\) の variable typing と `provable` によって
\(\Gamma\vDash\operatorname{Acc}_{A,B}(f,a)\) および
\(\Gamma\vDash f@a=\operatorname{finish}_{A,B}(b)\) を得る。

`finish intro` に実際の level \(1,1\) を用いると、

\[
\Gamma\vdash\operatorname{finish}_{A,B}(b):
\operatorname{RunStep}(A,B):*^s_1.
\]

ここで **`runCase` の規則の instance だけ** \(i=1,j=0,k=1\) と取る。
\(\max(1,0)=1\) なので、その全 premise は既に揃っている。
同規則には \(\Gamma\vdash B:*^s_j\) という premise がないため、

\[
\Gamma\vdash
r:=\operatorname{runCase}_{A,B}
(f,a,\operatorname{finish}_{A,B}(b)):B:*^s_0
\tag{bad-runCase}
\]

が導出される。一方、object calculus の root rule によって

\[
r\Rightarrow_s b.
\]

しかし \(\Gamma\nvdash b:B:*^s_0\) である。これを単に
「variable rule にない」からと結論してはいけない。conversion と refinement による
迂回を次のように排除する。

\(B\) は自由変数なので、それ自身は簡約されない。
sort、Ty、自由変数の head discrimination は、モデルや subject reduction に依存せず
[構文的補題 §2](metatheory.md#2-box-free-raw-conversion-の共通簡約先) の補助合流性から従う。
特に、Ty の外側の層を有限回剥がした先が \(B\) と raw-convertible な型は、
sort 定数と raw-convertible にならない。

裸の変数 \(b\) の typing 導出を調べると、構文に合う最終規則は
variable、weak type、conversion、subset intro、subset weak、type elem に限られる。
最初の五規則では、variable の \(*^s_1\) という分類を保存し、表示型は
conversion または外側の Ty の追加・除去によってだけ変化する。
`type elem` を使うには \(b:s\) という sorting が必要である。
裸の変数の sorting は `weak sort` を除けば `type sort` からしか出ないので、
それには先に \(b:s:t\) という、表示型が sort 定数の typing が必要になる。
そのような typing のうち最小高さのものを取ると、上記五規則と
head discrimination からは作れず、`type elem` から作ればさらに小さい同種の
typing が必要となって矛盾する。
従って `type elem` による分類の変更も起こらず、すべての typing は分類
\(*^s_1\) を保つ。これで \(b:B:*^s_0\) の非導出性が示された。

よって、修正前の規則に対する

\[
\Gamma\vdash t:T:s,\quad t\Rightarrow_s t'
\quad\Longrightarrow\quad\Gamma\vdash t':T:s
\]

は偽である。一般の datatype、Box、集合モデルを使わない反例である。
`run` にも同じ \(j\) の未制約がある。

### 0.2 集合モデルの sorting soundness も破れる

これは単に表示上の level の問題ではない。以下では 4 節の集合解釈を
そのまま使い、valid valuation で失敗する sorting を与える。

\(A,C:*^s_1\)、\(a:A:*^s_1\) とし、

\[
B:=\Power C,\qquad S:=\{x^{*^s_1}:C\mid x=x\}
\]

と置く。すると \(B:*^s_1\)、\(S:B:*^s_1\)。
\(f:A\to\operatorname{RunStep}(A,B):*^s_1\) と、
\(h:\operatorname{Acc}_{A,B}(f,a):*^p\)、
\(e:(f@a=\operatorname{finish}_{A,B}(S)):*^p\) を context に追加する。
0.1 節と同じ規則の instance から

\[
r:=\operatorname{runCase}_{A,B}(f,a,\operatorname{finish}_{A,B}(S)),
\qquad\Gamma\vdash r:\Power C:*^s_0.
\]

`power set intro` の premise はこれだけなので、

\[
\Gamma\vdash\Ty(C,r):*^s_0.
\tag{bad-sorting}
\]

4 節の universe tower において、valuation を

\[
\rho(A)=\{\varnothing\},\quad \rho(a)=\varnothing,\quad
\rho(C)=U_0
\]

と取る。\(U_0\in U_1\) より \(C:*^s_1\) の宣言に適合する。
\(\rho(f)\) は全入力で finish-tag 付きの \(U_0\) を返す関数とする。
\(\llbracket S\rrbracket_\rho=U_0\) なので、これは宣言された function type の要素である。
一段で finish するため Acc は真、equality も真であり、\(h,e\) に
\(\bullet\) を割り当てれば valid valuation になる。

ところが、

\[
\llbracket\Ty(C,r)\rrbracket_\rho
=\llbracket r\rrbracket_\rho
=\llbracket S\rrbracket_\rho
=U_0\notin U_0
=\llbracket *^s_0\rrbracket.
\]

\(U_0\notin U_0\) は集合論の正則性から従う。
したがって 4 節の sorting soundness は、修正前の規則のもとでは成立しない。
この計算は conversion の意味保存を仮定せず、表示された有限導出と
4 節の具体的な解釈だけを使う。

### 0.3 実施した修正と証明の状態

`run` と `runCase` の両方に

\[
\Gamma\vdash B:*^s_j
\]

を共通 premise として追加した。これにより上記の \(j=0\) の選択は許されない。
`runCase` だけを直しても、`run` による同様の誤分類が残る。
この変更は `dep elim` に追加した codomain formation と同じ役割を持つ。
さらに、universe の計算を formation rule に集約し、導入・消去規則は
個々の型の formation を明示する方針に揃えた。
`Acc` / `run` / `runCase` では function と RunStep の sort をそれぞれ
\(s_f,s_r\) とし、formation premise で検査する。
`Power` / subset でも元の集合の formation を共通 premise とした。

以下の Box 消去とモデルの旧稿は、修正後の証明に使う材料として残す。
**0.3 節の修正だけで全文の証明が完成する、とは主張しない。**
特に、型の generation、三判断の subject reduction、解釈の構成、
conversion soundness の依存関係を閉じる必要がある。

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
> **未証明の目標。** 上の集合論的仮定のもとで
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
を raw syntax 上の全域写像とする。写像が使う型注釈は Program 項自体に含まれる。
外部から与える全体の型 \(P\) は写像の引数ではなく、reflected term の typing property に現れる。

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
\lfloor f@^{\operatorname{Box}}a\rfloor&:=\lfloor f\rfloor @\lfloor a\rfloor
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
と定め、domain 外は0で全域化する。typed \(F\) と \(a\in\operatorname{Acc}_F\) について
\(\operatorname{Run}(F,a)\in B\) である。`RunCase` も tag により
\(\operatorname{Run}(F,a')\) または \(b\) を返す。
Acc と equality premise のもとで三つの Set `run` reduction equation が成立する。

解釈は typing derivation が選ぶ proof/data branch に沿って定義する。branch uniqueness と
semantic substitution を通常の同時帰納法で示し、conversion case に `TC0` を使う。

> **Box-free soundness の目標（修正後の規則について未証明）。** valid \(\rho\) について
> \[
> \begin{aligned}
> \Gamma\vdash_0T:s&\Rightarrow\llbracket T\rrbracket_\rho\in\llbracket s\rrbracket,\\
> \Gamma\vdash_0t:T:s&\Rightarrow\llbracket t\rrbracket_\rho\in\llbracket T\rrbracket_\rho,\\
> \Gamma\vDash_0P&\Rightarrow\llbracket P\rrbracket_\rho=1.
> \end{aligned}
> \]

**旧稿の証明案。** WF、sorting、typing、provability の導出の同時帰納法による。
PTS rules は universe closure と graph/proof product、conversion は `TC0` を使う。
power/subset は powerset と separation、equality は集合の等号、Take は非空性と定値性、
RunStep は tagged sum、Acc は `acc-laws`、run/runCase は rank recursion を使う。
provable と proof term の相互参照も有限導出の高さが下がる。

**この証明案は未成立。** 0.2 節の反例の原因となった規則は修正したが、
修正後の規則について帰納法の全 case を検証する必要がある。
branch uniqueness と semantic substitution を示すとした上の一文も、
その証明の代わりにはならない。

## 5. `falseProp`

\((\sq^p,*^p,*^p)\in\mathcal R\) であり
\[
\llbracket\mathit{falseProp}\rrbracket
=\operatorname{truth}(\forall P\in\{0,1\}.\ P=1)=0
\]
である。Box-free soundness が成立すれば
\(\emptyset\nvDash_0\mathit{falseProp}\) であり、これを型とする項も存在しない。
`falseProp` は Box-free なので `conservativity` により \(\mathcal S_\Box\) でも同様となる。
ただし、現在は前提となる soundness が未証明のため、これは無矛盾性証明ではない。

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
- datatype 規則が未完成な間、対象は core calculus に限る。
  0 節の反例に対応する規則は修正したが、core の無矛盾性定理もまだ証明していない。

旧証明の raw `RfType` / `RfTerm` constructor 間の critical pair は存在しない。
reflection は raw Program syntax から Box-free Set syntax へのメタレベル写像であり、
Box 付き側の conversion は `clear-conversion` により一括して Box-free conversion へ移る。
