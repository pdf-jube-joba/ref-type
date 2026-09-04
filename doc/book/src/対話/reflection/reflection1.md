# Reflection derivability と停止性

## 体系定義

Set/Prop と Program は `system.md` と同じく別の構文、context、judgement を持つ。
Program typing は停止性を要求しない。Reflection 可能な Program term だけを選ぶ
judgement として \(\vdash_{\mathrm{Rf}}\) を追加し、well-termination は
この judgement の導出可能性として定義する。

### 構文定義

Program type を \(P\)、Program value type を \(A\)、Program computation type を
\(\underline B\) とする。Program value と computation はそれぞれ \(V\)、\(M\) とする。
Set/Prop term は \(t\) とする。

Set/Prop term grammar には、Program syntax を payload とする次の raw term を置く。

\[
\begin{aligned}
t::=\cdots
&\mid \operatorname{RfType}(P) \\
&\mid \operatorname{RfTerm}_P(p).
\end{aligned}
\]

\(\operatorname{RfType}(P)\) と \(\operatorname{RfTerm}_P(p)\) は、
それぞれ Program type と Program term を構文として保持する。raw syntax を作れることと、
それを Set/Prop term として型付けできることは区別する。

Program context の reflection は次で定める。

\[
\begin{aligned}
\operatorname{RfCtx}(\emptyset)
&:=\emptyset,\\
\operatorname{RfCtx}(\Delta,X:\mathsf{vtype})
&:=\operatorname{RfCtx}(\Delta),
X^{\sq^s_0}:*^s_0:\sq^s_0,\\
\operatorname{RfCtx}(\Delta,x^v:A:\mathsf{value})
&:=\operatorname{RfCtx}(\Delta),
x^{*^s_0}:\operatorname{RfType}(A):*^s_0.
\end{aligned}
\]

Program datatype

\[
\operatorname{inductive}
I^v(\vec X)
\ \operatorname{where}\
C_i^v:
A_{i1}\to\cdots\to A_{ik_i}\to I^v(\vec X)
\]

には、Set 側の鏡像 \(I^s\) と \(C_i^s\) を対応させる。
\(I^s\) の parameter は任意の Set type を受け取る。

\[
\begin{aligned}
I^s(X^s_1:*^s_0,\ldots,X^s_n:*^s_0)&:*^s_0,\\
C_i^s&:
A^s_{i1}\to\cdots\to A^s_{ik_i}\to I^s(\vec X^s).
\end{aligned}
\]

\(A^s_{ij}\) は \(\operatorname{RfType}(A_{ij})\) に現れる
\(\operatorname{RfType}(X_\ell)\) を \(X^s_\ell\) で置き換えた Set type とする。

### Reduction 定義

Type reflection は Program type の構造を Set type へ写す。

\[
\begin{aligned}
\operatorname{RfType}(X)
&\Rightarrow_s X^{\sq^s_0},\\
\operatorname{RfType}(\text{F}A)
&\Rightarrow_s\operatorname{RfType}(A),\\
\operatorname{RfType}(\text{U}\underline B)
&\Rightarrow_s\operatorname{RfType}(\underline B),\\
\operatorname{RfType}(A\Rightarrow\underline B)
&\Rightarrow_s
\operatorname{RfType}(A)\to\operatorname{RfType}(\underline B),\\
\operatorname{RfType}(\operatorname{RunStep}(A,B))
&\Rightarrow_s
\operatorname{RunStep}
(\operatorname{RfType}(A),\operatorname{RfType}(B)),\\
\operatorname{RfType}(I^v(\vec A))
&\Rightarrow_s
I^s(\operatorname{RfType}(\vec A)).
\end{aligned}
\]

Term reflection は Program computation を glued form の内側に保持する。
Program reduction はその内側でも進める。

\[
\frac{M\Rightarrow_cM'}{
\operatorname{RfTerm}_{\underline B}(M)
\Rightarrow_s
\operatorname{RfTerm}_{\underline B}(M')}.
\tag{Rf-Cong}
\]

Program value variable は対応する Set variable へ写す。

\[
\operatorname{RfTerm}_A(x^v)
\Rightarrow_s x^{*^s_0}.
\tag{Rf-Var}
\]

\(\text{F}\) と \(\text{U}\) は type reflection で消えるため、対応する
introduction form も一層だけ消す。

\[
\begin{aligned}
\operatorname{RfTerm}_{\text{F}A}(\operatorname{return}(V))
&\Rightarrow_s\operatorname{RfTerm}_A(V),\\
\operatorname{RfTerm}_{\text{U}\underline B}(\operatorname{thunk}(M))
&\Rightarrow_s\operatorname{RfTerm}_{\underline B}(M).
\end{aligned}
\]

Reflected function の canonical form は glued form である。Set application の引数も
reflection の像である場合に Program application に戻す。

\[
\begin{aligned}
&\operatorname{RfTerm}_{\text{U}(A\Rightarrow\underline B)}(f)
@\operatorname{RfTerm}_A(a)\\
&\qquad\Rightarrow_s
\operatorname{RfTerm}_{\underline B}
(\operatorname{force}(f)@^c a),\\[4pt]
&\operatorname{RfTerm}_{A\Rightarrow\underline B}(M)
@\operatorname{RfTerm}_A(a)\\
&\qquad\Rightarrow_s
\operatorname{RfTerm}_{\underline B}(M@^c a).
\end{aligned}
\tag{Rf-U-App, Rf-C-App}
\]

従って \(\operatorname{RfTerm}_{A\Rightarrow\underline B}
(\lambda x^v:A.M)\) 自体は glued form のまま残るが、reflected argument に適用すると

\[
\begin{aligned}
&\operatorname{RfTerm}_{A\Rightarrow\underline B}
(\lambda x^v:A.M)
@\operatorname{RfTerm}_A(V)\\
&\qquad\Rightarrow_s
\operatorname{RfTerm}_{\underline B}
((\lambda x^v:A.M)@^cV)\\
&\qquad\Rightarrow_s
\operatorname{RfTerm}_{\underline B}(M[x^v:=V])
\end{aligned}
\]

と計算する。

#### Constructor の reflection

Program constructor の reflection は対応する Set constructor を一層だけ露出する。

\[
\begin{aligned}
&\operatorname{RfTerm}_{I^v(\vec A)}
\left(C_i^v[\vec A](\vec V)\right)\\
&\qquad\Rightarrow_s
C_i^s[\operatorname{RfType}(\vec A)]
\left(
\overrightarrow{
\operatorname{RfTerm}_{A_{ij}[\vec X:=\vec A]}(V_j)
}
\right).
\end{aligned}
\tag{Rf-Ctor}
\]

Set 側から glued constructor を直接観察する規則も生成する。

\[
\begin{aligned}
&\operatorname{case}^s_{I,S}
\left(
\operatorname{RfTerm}_{I^v(\vec A)}
(C_i^v[\vec A](\vec V));
h_0,\ldots,h_{k-1}
\right)\\
&\qquad\Rightarrow_s
h_i@\operatorname{RfTerm}_{A_{i1}}(V_1)
@\cdots
@\operatorname{RfTerm}_{A_{ik_i}}(V_{k_i}).
\end{aligned}
\tag{Rf-Ctor-Case}
\]

通常の Set constructor に対する case reduction と Rf-Ctor を異なる順序で適用しても、
両方が同じ branch application に到達する。

\(\operatorname{RunStep}\) の constructor も同じ向きに reflection する。

\[
\begin{aligned}
\operatorname{RfTerm}_{\operatorname{RunStep}(A,B)}
(\operatorname{continue}_{A,B}(a))
&\Rightarrow_s
\operatorname{continue}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}
(\operatorname{RfTerm}_A(a)),\\
\operatorname{RfTerm}_{\operatorname{RunStep}(A,B)}
(\operatorname{finish}_{A,B}(b))
&\Rightarrow_s
\operatorname{finish}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}
(\operatorname{RfTerm}_B(b)).
\end{aligned}
\tag{Rf-Continue, Rf-Finish}
\]

Set 側の \(\operatorname{prec}_{\operatorname{RunStep}}\) に glued form を直接観察する規則を
与えると、constructor reflection を先に行う path と合流する。

\[
\begin{aligned}
&\operatorname{prec}_{\operatorname{RunStep}
(\operatorname{RfType}(A),\operatorname{RfType}(B))}
\left(P,c,d,
\operatorname{RfTerm}_{\operatorname{RunStep}(A,B)}
(\operatorname{continue}_{A,B}(a))\right)\\
&\qquad\Rightarrow_s c@\operatorname{RfTerm}_A(a),\\[4pt]
&\operatorname{prec}_{\operatorname{RunStep}
(\operatorname{RfType}(A),\operatorname{RfType}(B))}
\left(P,c,d,
\operatorname{RfTerm}_{\operatorname{RunStep}(A,B)}
(\operatorname{finish}_{A,B}(b))\right)\\
&\qquad\Rightarrow_s d@\operatorname{RfTerm}_B(b).
\end{aligned}
\]

### Judgement 定義

Reflection derivability judgement は value と computation に分ける。

\[
\Delta\vdash_{\mathrm{Rf},v}V:A,
\qquad
\Delta\vdash_{\mathrm{Rf},c}M:\underline B.
\]

この judgement は Program typing judgement を含意する。Program typing judgement は
Reflection derivability judgement より弱く、停止性の情報を持たない。

#### Value

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| variable | \(\Delta,x^v:A:\mathsf{value}\vdash_{\mathrm{Rf},v}x^v:A\) | \(\operatorname{WF}_v(\Delta,x^v:A:\mathsf{value})\) | |
| thunk | \(\Delta\vdash_{\mathrm{Rf},v}\operatorname{thunk}(M):\text{U}\underline B\) | \(\Delta\vdash_{\mathrm{Rf},c}M:\underline B\) | |
| continue | \(\Delta\vdash_{\mathrm{Rf},v}\operatorname{continue}_{A,B}(a):\operatorname{RunStep}(A,B)\) | \(\Delta\vdash_{\mathrm{Rf},v}a:A\)<br>\(\Delta\vdash B\ \mathsf{vtype}\) | |
| finish | \(\Delta\vdash_{\mathrm{Rf},v}\operatorname{finish}_{A,B}(b):\operatorname{RunStep}(A,B)\) | \(\Delta\vdash A\ \mathsf{vtype}\)<br>\(\Delta\vdash_{\mathrm{Rf},v}b:B\) | |
| constructor | \(\Delta\vdash_{\mathrm{Rf},v}C_i^v[\vec A](\vec V):I^v(\vec A)\) | \(\Delta\vdash A_\ell\ \mathsf{vtype}\) for all \(\ell\)<br>\(\Delta\vdash_{\mathrm{Rf},v}V_j:A_{ij}[\vec X:=\vec A]\) for all \(j\) | \(I^v\) は well-formed な declaration |

#### Computation

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| return | \(\Delta\vdash_{\mathrm{Rf},c}\operatorname{return}(V):\text{F}A\) | \(\Delta\vdash_{\mathrm{Rf},v}V:A\) | |
| force | \(\Delta\vdash_{\mathrm{Rf},c}\operatorname{force}(V):\underline B\) | \(\Delta\vdash_{\mathrm{Rf},v}V:\text{U}\underline B\) | |
| function intro | \(\Delta\vdash_{\mathrm{Rf},c}\lambda x^v:A.M:A\Rightarrow\underline B\) | \(\Delta,x^v:A:\mathsf{value}\vdash_{\mathrm{Rf},c}M:\underline B\) | \(x^v\notin\Delta\) |
| function elim | \(\Delta\vdash_{\mathrm{Rf},c}M@^cV:\underline B\) | \(\Delta\vdash_{\mathrm{Rf},c}M:A\Rightarrow\underline B\)<br>\(\Delta\vdash_{\mathrm{Rf},v}V:A\) | |
| sequence | \(\Delta\vdash_{\mathrm{Rf},c}M\ \operatorname{to}\ x^v:A\ \operatorname{in}\ N:\underline B\) | \(\Delta\vdash_{\mathrm{Rf},c}M:\text{F}A\)<br>\(\Delta,x^v:A:\mathsf{value}\vdash_{\mathrm{Rf},c}N:\underline B\) | \(x^v\notin\Delta\) |
| value let | \(\Delta\vdash_{\mathrm{Rf},c}\operatorname{let}^v x^v=V\ \operatorname{in}\ N:\underline B\) | \(\Delta\vdash_{\mathrm{Rf},v}V:A\)<br>\(\Delta,x^v:A:\mathsf{value}\vdash_{\mathrm{Rf},c}N:\underline B\) | \(x^v\notin\Delta\) |
| case | \(\Delta\vdash_{\mathrm{Rf},c}\operatorname{case}^v(V;\overline{C_i^v(\vec x_i^v)\mapsto M_i}):\underline B\) | \(\Delta\vdash_{\mathrm{Rf},v}V:I^v(\vec A)\)<br>\(\Delta,\vec x_i^v:\vec A_i[\vec X:=\vec A]:\mathsf{value}\vdash_{\mathrm{Rf},c}M_i:\underline B\) for all \(i\) | 各 branch がちょうど一つ |

Function introduction の premise は、引数を Reflection derivability の仮定として追加した
context で本体を導出する。このため、Program lambda が weak reduction で既に normal form であること
だけでは function intro を導出できない。reflected argument に適用した後の computation まで
Reflection derivability が保存される。

#### Reflection derivation の Set representative

Reflection derivation

\[
\rho:\Delta\vdash_{\mathrm{Rf}}p:P
\]

に対し、その導出が構成する Set representative を \(\lVert\rho\rVert_s\) と書く。
これは有限な derivation に対するメタレベル関数である。
Value に関する主要な clause は次である。

\[
\begin{aligned}
\lVert\rho_x\rVert_s
&:=x^{*^s_0},\\
\lVert\rho_{\operatorname{thunk}(M)}\rVert_s
&:=\lVert\rho_M\rVert_s,\\
\lVert\rho_{\operatorname{continue}(a)}\rVert_s
&:=
\operatorname{continue}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}
(\lVert\rho_a\rVert_s),\\
\lVert\rho_{\operatorname{finish}(b)}\rVert_s
&:=
\operatorname{finish}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}
(\lVert\rho_b\rVert_s),\\
\lVert\rho_{C_i^v[\vec A](\vec V)}\rVert_s
&:=
C_i^s[\operatorname{RfType}(\vec A)]
(\overrightarrow{\lVert\rho_{V_j}\rVert_s}).
\end{aligned}
\]

Return の representative は payload value の representative とする。Lambda と、Set 構文に
直接対応する構成子を持たない computation form の representative は glued form
\(\operatorname{RfTerm}_P(p)\) とする。

各 Reflection derivation について次の coherence を要求する。

\[
\begin{aligned}
\operatorname{RfCtx}(\Delta)&\vdash
\lVert\rho\rVert_s:
\operatorname{RfType}(P):*^s_0,\\
\lVert\rho\rVert_s
&\equiv_s
\operatorname{RfTerm}_P(p).
\end{aligned}
\tag{Rf-Representative}
\]

Constructor の場合、二式目は

\[
C_i^s[\operatorname{RfType}(\vec A)]
(\overrightarrow{\lVert\rho_{V_j}\rVert_s})
\equiv_s
\operatorname{RfTerm}_{I^v(\vec A)}
(C_i^v[\vec A](\vec V))
\]

となる。これが \(C_i^s\) から \(\operatorname{RfTerm}(C_i^v)\) へ戻る方向である。
この方向は field ごとの Reflection derivation を添えた reification である。

Reflected function を representative に適用する場合も、同じ derivation を reification の
witness として用いる。

\[
\frac{
\rho_V:\Delta\vdash_{\mathrm{Rf},v}V:A
}{
\operatorname{RfTerm}_{A\Rightarrow\underline B}(M)
@\lVert\rho_V\rVert_s
\Rightarrow_{s,\rho_V}
\operatorname{RfTerm}_{\underline B}(M@^cV)
}.
\tag{Rf-Representative-App}
\]

\(\Rightarrow_{s,\rho_V}\) は Reflection derivation を参照する typed reduction である。
Rf-Representative と Rf-C-App が与える definitional equality を、Program application へ戻る
向きに orient している。raw term だけに対する reduction を保つ場合は、type checking 時に
\(\rho_V\) を保持する elaborated form へ変換し、この rule をその core reduction とする。
この rule の domain は Reflection derivation の Set representative に限られる。任意の
\(u:\operatorname{RfType}(A)\) は domain に含まれない。

Thunk された function に対しても同様に次を置く。

\[
\frac{
\rho_V:\Delta\vdash_{\mathrm{Rf},v}V:A
}{
\operatorname{RfTerm}_{\text{U}(A\Rightarrow\underline B)}(f)
@\lVert\rho_V\rVert_s
\Rightarrow_{s,\rho_V}
\operatorname{RfTerm}_{\underline B}(\operatorname{force}(f)@^cV)
}.
\tag{Rf-U-Representative-App}
\]

#### Run

Program の \(\operatorname{run}\) に対する Reflection derivability は、Set 側で
accessibility が証明されている場合に限って導出する。

\[
\frac{
\begin{gathered}
\Delta\vdash_{\mathrm{Rf},v}
f:\text{U}(A\Rightarrow\text{F}(\operatorname{RunStep}(A,B)))\qquad
\Delta\vdash_{\mathrm{Rf},v}a:A\\
\operatorname{RfCtx}(\Delta)\vDash
\operatorname{Acc}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}
\left(
\operatorname{RfTerm}_{\text{U}(A\Rightarrow\text{F}(\operatorname{RunStep}(A,B)))}(f),
\operatorname{RfTerm}_A(a)
\right)
\end{gathered}
}{
\Delta\vdash_{\mathrm{Rf},c}
\operatorname{run}_{A,B}(f,a):\text{F}B
}.
\tag{Rf-Run}
\]

この rule の accessibility premise は、先行する二つの premise から Set 側で型付けされた
reflected step function と reflected initial state に対する命題である。
この二つの Set typing derivation は Rf-Run の proper premise に対応する
Reflection derivation から得られるので、Rf-Run の結論を使った循環は生じない。

\(\operatorname{runCase}\) は reduction 中に現れる administrative form なので、
現在の state に対する accessibility と、一段計算との対応を保持する。

\[
\frac{
\begin{gathered}
\Delta\vdash_{\mathrm{Rf},v}
f:\text{U}(A\Rightarrow\text{F}(\operatorname{RunStep}(A,B)))\qquad
\Delta\vdash_{\mathrm{Rf},v}a:A\\
\Delta\vdash_{\mathrm{Rf},c}
M:\text{F}(\operatorname{RunStep}(A,B))\\
\operatorname{RfCtx}(\Delta)\vDash
\operatorname{Acc}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}
\left(
\operatorname{RfTerm}_{\text{U}(A\Rightarrow\text{F}(\operatorname{RunStep}(A,B)))}(f),
\operatorname{RfTerm}_A(a)
\right)\\
\operatorname{RfCtx}(\Delta)\vDash
\operatorname{RfTerm}_{\text{U}(A\Rightarrow\text{F}(\operatorname{RunStep}(A,B)))}(f)
@\operatorname{RfTerm}_A(a)
=\operatorname{RfTerm}_{\text{F}(\operatorname{RunStep}(A,B))}(M)
\end{gathered}
}{
\Delta\vdash_{\mathrm{Rf},c}
\operatorname{runCase}_{A,B}(f,a,M):\text{F}B
}.
\tag{Rf-RunCase}
\]

一段計算が \(\operatorname{continue}_{A,B}(a')\) を返したときは、上の equality と
\(\operatorname{Acc}\) の descent により次の state に対する accessibility を得る。
\(\operatorname{finish}_{A,B}(b)\) を返したときは \(\operatorname{return}(b)\) の
Reflection derivability に移る。

#### Reflection typing

Type reflection は Program type formation だけを必要とする。

| category | conclusion | premises |
| --- | --- | --- |
| value type | \(\operatorname{RfCtx}(\Delta)\vdash\operatorname{RfType}(A):*^s_0\) | \(\Delta\vdash A\ \mathsf{vtype}\) |
| computation type | \(\operatorname{RfCtx}(\Delta)\vdash\operatorname{RfType}(\underline B):*^s_0\) | \(\Delta\vdash\underline B\ \mathsf{ctype}\) |

Term reflection の Set typing は Reflection derivability から導く。

| category | conclusion | premises |
| --- | --- | --- |
| value | \(\operatorname{RfCtx}(\Delta)\vdash\operatorname{RfTerm}_A(V):\operatorname{RfType}(A):*^s_0\) | \(\Delta\vdash_{\mathrm{Rf},v}V:A\) |
| computation | \(\operatorname{RfCtx}(\Delta)\vdash\operatorname{RfTerm}_{\underline B}(M):\operatorname{RfType}(\underline B):*^s_0\) | \(\Delta\vdash_{\mathrm{Rf},c}M:\underline B\) |

Reflection derivability の規則は、この二つの typing rule より先に帰納的に生成される。
\(\operatorname{RfTerm}\) の typing derivation を generation すると対応する
\(\vdash_{\mathrm{Rf}}\) derivation が得られるので、次が成り立つ。

\[
\begin{aligned}
&\operatorname{RfCtx}(\Delta)\vdash
\operatorname{RfTerm}_A(V):\operatorname{RfType}(A):*^s_0\\
&\qquad\Longleftrightarrow
\Delta\vdash_{\mathrm{Rf},v}V:A,\\[4pt]
&\operatorname{RfCtx}(\Delta)\vdash
\operatorname{RfTerm}_{\underline B}(M):\operatorname{RfType}(\underline B):*^s_0\\
&\qquad\Longleftrightarrow
\Delta\vdash_{\mathrm{Rf},c}M:\underline B.
\end{aligned}
\tag{Reflection generation}
\]

右から左は Reflection typing rule、左から右は \(\operatorname{RfTerm}\) に対する
typing generation である。この同値は、独立に生成された
\(\vdash_{\mathrm{Rf}}\) と Set typing の対応を表す。

### Well-termination の定義

Well-termination の記法は Reflection derivability の別表記として定義する。

\[
\begin{aligned}
\Delta\Vdash_vV:A
&:\Longleftrightarrow
\Delta\vdash_{\mathrm{Rf},v}V:A,\\
\Delta\Vdash_cM:\underline B
&:\Longleftrightarrow
\Delta\vdash_{\mathrm{Rf},c}M:\underline B.
\end{aligned}
\tag{WT}
\]

従って Reflection typing rule の well-termination premise は
\(\vdash_{\mathrm{Rf}}\) の derivation を要求する。

この定義における computation type ごとの意味は次である。

- \(\Delta\Vdash_cM:\text{F}A\) は、任意の reflection 可能な closing substitution
  の下で \(M\) が \(\operatorname{return}(V)\) まで進み、結果の \(V\) も
  Reflection derivability を持つことを要求する。
- \(\Delta\Vdash_cM:A\Rightarrow\underline B\) は、任意の reflection 可能な closing
  substitution \(\sigma\) と任意の \(\emptyset\Vdash_vV:\sigma(A)\) に対して、
  \(\sigma(M)@^cV\) が \(\sigma(\underline B)\) で well-terminated であることを要求する。
- \(\Delta\Vdash_v\operatorname{thunk}(M):\text{U}\underline B\) は、任意の reflection
  可能な closing substitution \(\sigma\) に対して、内部の \(\sigma(M)\) が
  \(\sigma(\underline B)\) で well-terminated であることを要求する。

これらは \(\vdash_{\mathrm{Rf}}\) に対して示す fundamental property である。
従って、ここで well-terminated と呼ぶ範囲は operational に停止する Program 全体ではなく、
有限な Reflection derivation によって停止を証明できる Program である。

## 二つの方向

Program typing だけを premise とする次の schema は、発散する Program にも適用できる。

\[
\frac{\Delta\vdash_Pp:P}{
\operatorname{RfCtx}(\Delta)\vdash
\operatorname{RfTerm}_P(p):\operatorname{RfType}(P):*^s_0}
\]

発散する \(M:\text{F}A\) が存在すると、Rf-Cong によって Set 側にも
無限 reduction が入るからである。\(\operatorname{thunk}(M)\) は value だが、その reflection は
\(\operatorname{RfTerm}_{\underline B}(M)\) へ進むので、value typing に限定しても同じ問題が
残る。

必要な二方向は次である。

\[
\begin{aligned}
\Delta\vdash_{\mathrm{Rf}}p:P
&\Longrightarrow \Delta\vdash_Pp:P,\\
\Delta\vdash_{\mathrm{Rf}}p:P
&\Longrightarrow
\operatorname{RfCtx}(\Delta)\vdash
\operatorname{RfTerm}_P(p):\operatorname{RfType}(P):*^s_0,\\
\operatorname{RfCtx}(\Delta)\vdash
\operatorname{RfTerm}_P(p):\operatorname{RfType}(P):*^s_0
&\Longrightarrow
\Delta\vdash_{\mathrm{Rf}}p:P.
\end{aligned}
\]

最後の方向は \(\operatorname{RfTerm}\) に固有の typing rule に対する generation である。
これにより reflected term の Set typing derivation が Program typing と停止証明の両方を
含む。一方、通常の Program typing は reflection できない Program も型付けする。

## Lambda の abstract boundary

\(\operatorname{RfTerm}(\lambda x^v:A.M)\) は Set lambda へ展開せず、glued form を
canonical form とする。この glued form は Set 側では \(\operatorname{RfType}(A)\to
\operatorname{RfType}(\underline B)\) を持つが、Program application へ戻るのは引数が
明示的に reflection の像である場合だけである。

\[
\operatorname{RfTerm}_{A\Rightarrow\underline B}
(\lambda x^v:A.M)@u
\]

において、\(u\) が任意の Set term なら application は stuck でよい。
\(u\) が \(\operatorname{RfTerm}_A(V)\) なら Rf-C-App が発火する。また、\(u\) が
Reflection derivation \(\rho_V\) の Set representative なら Rf-Representative-App により
同じ Program application へ戻る。

Function intro の Reflection derivability は本体の derivation を要求するため、発散する本体を
持つ Program lambda を、lambda 自体が weak normal form であるという理由だけで Set function
として反映することはできない。

## Constructor と abstract boundary

Constructor について reflection の印を失う向きだけを採用すると、次の term に二つの
reduction path が生じる。

\[
\operatorname{RfTerm}(f)
@\operatorname{RfTerm}(C_i^v(\vec V)).
\]

外側の Rf-App を先に使えば Program application の reflection になる。一方、引数の
Rf-Ctor を先に使って \(C_i^s(\overrightarrow{\operatorname{RfTerm}(V)})\) にすると、
Rf-App の redex ではなくなる。

Reflection derivation \(\rho_{C_i^v(\vec V)}\) の Set representative は

\[
C_i^s(\overrightarrow{\lVert\rho_{V_j}\rVert_s})
\]

であり、Rf-Representative により

\[
C_i^s(\overrightarrow{\lVert\rho_{V_j}\rVert_s})
\equiv_s
\operatorname{RfTerm}(C_i^v(\vec V))
\]

である。従って Rf-Representative-App を使うと、この Set constructor を
Program constructor として reflected function に渡せる。Rf-Ctor の逆向きを無条件の
raw reduction にすると直ちに loop するため、この向きには field の Reflection derivation が
必要である。

従って \(C_i^s\) には二種類の使い方がある。

- field が任意の Set term である通常の Set constructor
- parameter と field が Reflection derivation の Set representative であり、対応する
  Program constructor へ reify できる constructor

後者だけが reflected Program function の computational argument になる。この制限は lambda の
abstract boundary と同じものである。

## Metatheory

この構成には少なくとも次の定理が必要である。

### Program typing の回収

\[
\begin{aligned}
\Delta\vdash_{\mathrm{Rf},v}V:A
&\Longrightarrow\Delta\vdash_vV:A,\\
\Delta\vdash_{\mathrm{Rf},c}M:\underline B
&\Longrightarrow\Delta\vdash_cM:\underline B.
\end{aligned}
\]

これは Reflection derivability の derivation に関する帰納法で示す。

### Reflection typing

\[
\begin{aligned}
\Delta\vdash_{\mathrm{Rf},v}V:A
&\Longrightarrow
\operatorname{RfCtx}(\Delta)\vdash
\operatorname{RfTerm}_A(V):\operatorname{RfType}(A):*^s_0,\\
\Delta\vdash_{\mathrm{Rf},c}M:\underline B
&\Longrightarrow
\operatorname{RfCtx}(\Delta)\vdash
\operatorname{RfTerm}_{\underline B}(M):\operatorname{RfType}(\underline B):*^s_0.
\end{aligned}
\]

Rf-Run では accessibility premise を使い、Rf-RunCase では accessibility と一段計算の
equality を使う。

### Reflection substitution

Reflection derivability を持つ closing substitution で置換しても derivability が保存される。

\[
\begin{aligned}
\Delta,x^v:A:\mathsf{value}\vdash_{\mathrm{Rf}}p:P,
\qquad
\Delta\vdash_{\mathrm{Rf},v}V:A\\
\Longrightarrow
\Delta\vdash_{\mathrm{Rf}}p[x^v:=V]:P[x^v:=V].
\end{aligned}
\]

Set 側では対応する substitution が成り立つ。

\[
\begin{aligned}
&\operatorname{RfTerm}_P(p)
[x^{*^s_0}:=\operatorname{RfTerm}_A(V)]\\
&\qquad\equiv_s
\operatorname{RfTerm}_{P[x^v:=V]}(p[x^v:=V]).
\end{aligned}
\]

従って open term の operational property は、Program variable を closed な
Reflection derivability を持つ value に写す closing substitution に相対化する。
Set/Prop の仮定を追加した一般の context まで許す場合は、その仮定を真にする closing
substitution に相対化する。

### Subject reduction

\[
\begin{aligned}
\Delta\vdash_{\mathrm{Rf},c}M:\underline B,
\quad M\Rightarrow_cM'
\quad\Longrightarrow\quad
\Delta\vdash_{\mathrm{Rf},c}M':\underline B.
\end{aligned}
\]

Run-Continue の場合は Rf-Run の accessibility premise と一段計算の equality から
Acc descent を使う。Run-Finish の場合は結果 value の Reflection derivability を回収する。

### 閉じた computation の停止

\[
\emptyset\vdash_{\mathrm{Rf},c}M:\text{F}A
\quad\Longrightarrow\quad
\exists V.\
M\Rightarrow_c^*\operatorname{return}(V)
\ \land\
\emptyset\vdash_{\mathrm{Rf},v}V:A.
\]

Function type については次の logical property を示す。

\[
\begin{aligned}
&\emptyset\vdash_{\mathrm{Rf},c}M:A\Rightarrow\underline B,
\qquad
\emptyset\vdash_{\mathrm{Rf},v}V:A\\
&\qquad\Longrightarrow
\emptyset\vdash_{\mathrm{Rf},c}M@^cV:\underline B.
\end{aligned}
\]

Rf-Run の場合は Set 側の accessibility proof に関する well-founded induction を使う。
Reflection reduction の simulation と constructor の adequacy により、Set 側で得た次状態が
Program 側の \(\operatorname{continue}\) の payload と一致することを示す。

### Reduction の整合性

次の critical pair が合流することを示す。

- Rf-C-App または Rf-U-App と Rf-Cong
- Rf-Ctor と Rf-Representative-App
- Rf-Ctor-Case と Program case の Rf-Cong
- Rf-Continue、Rf-Finish と \(\operatorname{RunStep}\) の recursor
- Rf-RunCase と Program run reduction の Rf-Cong

Rf-Ctor の逆向きは、Reflection derivation を保持する elaboration または typed reduction
として定める。これにより Set representative から Program value を回収する範囲が決まる。

## 位置付け

\(\vdash_{\mathrm{Rf}}\) は、Program typing が許す term のうち、Set 側の証明によって
停止性を保証でき、Set term として安全に利用できる部分を定める judgement である。

Well-termination はこの judgement の derivability そのものである。Set typing は
\(\vdash_{\mathrm{Rf}}\) から導かれ、その typing derivation を反転すると
\(\vdash_{\mathrm{Rf}}\) が回収される。
