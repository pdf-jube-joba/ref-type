## 体系定義

sort-labelled syntax を、context に依存しない二つの family

\[
\operatorname{Ty}^s,
\qquad
\operatorname{Tm}^s
\qquad(s\in\mathcal S)
\]

として定義する。意図する対応は

\[
\begin{aligned}
\Gamma\vdash A:s
&\Longrightarrow
A\in\operatorname{Ty}^s,\\
\Gamma\vdash t:A:s
&\Longrightarrow
t\in\operatorname{Tm}^s
\end{aligned}
\tag{Sorting-Soundness}
\]

である。\(\operatorname{Ty}^s\) は sort \(s\) の type expression、
\(\operatorname{Tm}^s\) は sort \(s\) に属する型の inhabitant の presyntax を
表す。どちらも \(\Gamma\) や実際の型 \(A\) を index に持たない。したがって、
構文は type と term の役割を区別するが、well-typedness は通常の judgement が
検査する。

### PTS signature

PTS signature は通常どおり

\[
\mathcal P=(\mathcal S,\mathcal A,\mathcal R),
\qquad
\mathcal A\subseteq\mathcal S^2,
\qquad
\mathcal R\subseteq\mathcal S^3
\]

とする。product、abstraction、application は

\[
r=(s_1,s_2,s_3)\in\mathcal R
\]

で直接 index する。

Set/Prop 側には現行体系の signature を使う。Program 側には

\[
\mathcal S_t
=
\{*^v_i,*^c_i,\sq^t_i\mid i\in\mathbb N\}
\]

を追加し、

\[
\mathcal A_t
=
\{
(*^v_i,\sq^t_i),
(*^c_i,\sq^t_i)
\mid i\in\mathbb N
\}
\]

とする。Program function と type polymorphism に使う rule は

\[
\begin{aligned}
r^{i,j}_{\mathrm{fun}}
&=
(*^v_i,*^c_j,*^c_{\max(i,j)}),\\
r^{i,j}_{\mathrm{poly}}
&=
(\sq^t_i,*^c_j,*^c_{\max(i+1,j)})
\end{aligned}
\]

である。value type と computation type のどちらを量化するかは、domain に
\(*^v_i\) と \(*^c_i\) のどちらを書くかによって区別する。同じ
\(r^{i,j}_{\mathrm{poly}}\) を使ってよい。

### sort と variable

axiom \((s_0,s_1)\in\mathcal A\) ごとに

\[
s_0\in\operatorname{Ty}^{s_1}
\tag{Sort-Syn}
\]

とする。例えば

\[
*^v_i\in\operatorname{Ty}^{\sq^t_i},
\qquad
*^c_i\in\operatorname{Ty}^{\sq^t_i}.
\]

term variable は

\[
x^s\in\operatorname{Tm}^s
\tag{Var-Syn}
\]

とする。annotation \(s\) は、context entry

\[
x^s:A:s
\]

の末尾の sort と一致しなければならない。この一致は variable の typing rule が
検査する。

### PTS constructor

\(r=(s_1,s_2,s_3)\in\mathcal R\) に対して、PTS の constructor を

\[
\frac{
 A\in\operatorname{Ty}^{s_1}
 \qquad
 B\in\operatorname{Ty}^{s_2}
}{
 \Pi_r x^{s_1}:A.B
 \in\operatorname{Ty}^{s_3}
}
\tag{Pi-Syn}
\]

\[
\frac{
 A\in\operatorname{Ty}^{s_1}
 \qquad
 t\in\operatorname{Tm}^{s_2}
}{
 \lambda_r x^{s_1}:A.t
 \in\operatorname{Tm}^{s_3}
}
\tag{Lam-Syn}
\]

\[
\frac{
 f\in\operatorname{Tm}^{s_3}
 \qquad
 u\in\operatorname{Tm}^{s_1}
}{
 f@_r u
 \in\operatorname{Tm}^{s_2}
}
\tag{App-Syn}
\]

で生成する。binder が導入する variable は常に

\[
x^{s_1}:A:s_1
\]

であり、以前の \(d\) や \(\partial r\) は使わない。

これらは context-free な presyntax の規則である。例えば
\(f\in\operatorname{Tm}^{s_3}\) だけから、\(f\) の実際の型が
\(\Pi_r x:A.B\) であることまでは分からない。App の typing rule が
function type、rule \(r\)、argument type の一致を検査する。

### type-as-term bridge

Russell-style PTS では、type は sort を型として持つ term としても使われる。
この役割の変更を、axiom \(a=(s_0,s_1)\in\mathcal A\) ごとに

\[
\frac{A\in\operatorname{Ty}^{s_0}}
     {\operatorname{asTm}_a(A)\in\operatorname{Tm}^{s_1}}
\tag{AsTm-Syn}
\]

\[
\frac{t\in\operatorname{Tm}^{s_1}}
     {\operatorname{asTy}_a(t)\in\operatorname{Ty}^{s_0}}
\tag{AsTy-Syn}
\]

として表示する。\(\operatorname{asTy}_a(t)\) の typing では、\(t\) の実際の型が
\(s_0\) であることを検査する。したがって AsTy-Syn は presyntax としては
over-approximation である。

raw syntax への erasure は

\[
\left|\operatorname{asTm}_a(A)\right|=|A|,
\qquad
\left|\operatorname{asTy}_a(t)\right|=|t|
\]

とする。二つは surface constructor ではなく、type checker が付ける role
annotation である。checked syntax 上では

\[
\begin{aligned}
\operatorname{asTy}_a(\operatorname{asTm}_a(A))
&\longrightarrow^{\mathrm{ty}}_{s_0} A,\\
\operatorname{asTm}_a(\operatorname{asTy}_a(t))
&\longrightarrow^{\mathrm{st}}_{s_1} t
\end{aligned}
\tag{Role-Cancel}
\]

とする。

この bridge は、現行体系の

\[
\frac{\Gamma\vdash A:s_0:s_1}
     {\Gamma\vdash A:s_0}
\tag{Type-Sort}
\]

を構文 family に反映したものである。特に polymorphic binder の variable を
type として使う箇所で必要になる。

### Program 固有の構文

Program type former は \(\operatorname{Ty}\) 間の constructor とする。

\[
\frac{A\in\operatorname{Ty}^{*^v_i}}
     {F A\in\operatorname{Ty}^{*^c_i}},
\qquad
\frac{\underline B\in\operatorname{Ty}^{*^c_i}}
     {U\underline B\in\operatorname{Ty}^{*^v_i}}.
\tag{FU-Syn}
\]

\[
\frac{
 A\in\operatorname{Ty}^{*^v_i}
 \qquad
 B\in\operatorname{Ty}^{*^v_j}
}{
 \operatorname{RunStep}(A,B)
 \in\operatorname{Ty}^{*^v_{\max(i,j)}}
}.
\tag{RunStep-Syn}
\]

Program term constructor は \(\operatorname{Tm}\) 間の constructor とする。

\[
\frac{V\in\operatorname{Tm}^{*^v_i}}
     {\operatorname{return}(V)\in\operatorname{Tm}^{*^c_i}},
\qquad
\frac{M\in\operatorname{Tm}^{*^c_i}}
     {\operatorname{thunk}(M)\in\operatorname{Tm}^{*^v_i}},
\qquad
\frac{V\in\operatorname{Tm}^{*^v_i}}
     {\operatorname{force}(V)\in\operatorname{Tm}^{*^c_i}}.
\tag{CBPV-Syn}
\]

sequence と value let は

\[
\frac{
 M\in\operatorname{Tm}^{*^c_i}
 \qquad
 A\in\operatorname{Ty}^{*^v_i}
 \qquad
 N\in\operatorname{Tm}^{*^c_j}
}{
 M\ \operatorname{to}\ x^{*^v_i}:A\ \operatorname{in}\ N
 \in\operatorname{Tm}^{*^c_j}
}
\tag{Seq-Syn}
\]

\[
\frac{
 V\in\operatorname{Tm}^{*^v_i}
 \qquad
 A\in\operatorname{Ty}^{*^v_i}
 \qquad
 t\in\operatorname{Tm}^{s}
}{
 \operatorname{let}^v x^{*^v_i}:A=V\ \operatorname{in}\ t
 \in\operatorname{Tm}^{s}
}
\tag{Let-Syn}
\]

とする。continue、finish、run、runCase も、型 annotation は
\(\operatorname{Ty}\)、value argument は \(\operatorname{Tm}^{*^v}\)、
computation argument と結果は \(\operatorname{Tm}^{*^c}\) に置く。

Program function type は Pi-Syn により

\[
\Pi_{r^{i,j}_{\mathrm{fun}}}
x^{*^v_i}:A.\underline B
\in
\operatorname{Ty}^{*^c_{\max(i,j)}}
\]

となる。非依存の場合に

\[
A\Rightarrow\underline B
\]

と書く。abstraction と application は

\[
\lambda_{r^{i,j}_{\mathrm{fun}}}x^{*^v_i}:A.M,
\qquad
M@_{r^{i,j}_{\mathrm{fun}}}V
\]

であり、独立した \(@^c\) mode は \(r^{i,j}_{\mathrm{fun}}\) に吸収される。

### Program type polymorphism

\(q\in\{v,c\}\) とし、

\[
a^q_i=(*^q_i,\sq^t_i)\in\mathcal A
\]

と置く。polymorphic product の domain は

\[
*^q_i\in\operatorname{Ty}^{\sq^t_i}
\]

なので、Pi-Syn が context に導入する variable は

\[
X^{\sq^t_i}:*^q_i:\sq^t_i
\]

である。したがって \(d=s_1=\sq^t_i\) のままでよい。

body で \(X\) を Program type として使うときは

\[
X^\sharp
\coloneqq
\operatorname{asTy}_{a^q_i}(X^{\sq^t_i})
\in
\operatorname{Ty}^{*^q_i}
\]

と読む。例えば

\[
F X^\sharp\in\operatorname{Ty}^{*^c_i}.
\]

polymorphic type と abstraction は

\[
\Pi_{r^{i,j}_{\mathrm{poly}}}
X^{\sq^t_i}:*^q_i.\underline B
\in
\operatorname{Ty}^{*^c_{\max(i+1,j)}}
\]

\[
\lambda_{r^{i,j}_{\mathrm{poly}}}
X^{\sq^t_i}:*^q_i.M
\in
\operatorname{Tm}^{*^c_{\max(i+1,j)}}
\]

である。

type argument \(P\in\operatorname{Ty}^{*^q_i}\) は、application の argument
category \(\operatorname{Tm}^{\sq^t_i}\) に合わせて

\[
\operatorname{asTm}_{a^q_i}(P)
\in
\operatorname{Tm}^{\sq^t_i}
\]

として渡す。

\[
M@_{r^{i,j}_{\mathrm{poly}}}
\operatorname{asTm}_{a^q_i}(P)
\in
\operatorname{Tm}^{*^c_j}.
\]

surface notation は

\[
\begin{aligned}
\Lambda X:*^q_i.M
&\coloneqq
\lambda_{r^{i,j}_{\mathrm{poly}}}
X^{\sq^t_i}:*^q_i.M,\\
M[P]
&\coloneqq
M@_{r^{i,j}_{\mathrm{poly}}}
\operatorname{asTm}_{a^q_i}(P)
\end{aligned}
\]

とする。surface body に現れる type variable \(X\) は、checked syntax では
\(X^\sharp\) に elaborate される。

### context と judgement

context は syntax family の parameter にはせず、

\[
\Gamma::=\varnothing
\mid\Gamma,x^s:A:s
\]

とする。type variable も同じ entry を使う。例えば Program type variable は

\[
\Gamma,X^{\sq^t_i}:*^q_i:\sq^t_i
\]

である。

judgement は

\[
\Gamma\vdash A:s,
\qquad
\Gamma\vdash t:A:s
\]

とする。Program term の principal level も

\[
\Gamma\vdash V:A:*^v_i,
\qquad
\Gamma\vdash M:\underline B:*^c_i
\]

のように末尾へ表示する。

PTS の主要な typing rule は、構文の \(r=(s_1,s_2,s_3)\) をそのまま検査する。

\[
\frac{
 \Gamma\vdash A:s_1
 \qquad
 \Gamma,x^{s_1}:A:s_1\vdash B:s_2
}{
 \Gamma\vdash
 \Pi_r x^{s_1}:A.B:s_3
}.
\tag{Pi}
\]

\[
\frac{
 \Gamma\vdash
 \Pi_r x^{s_1}:A.B:s_3
 \qquad
 \Gamma,x^{s_1}:A:s_1\vdash t:B:s_2
}{
 \Gamma\vdash
 \lambda_r x^{s_1}:A.t:
 \Pi_r x^{s_1}:A.B:s_3
}.
\tag{Lam}
\]

\[
\frac{
 \Gamma\vdash
 f:\Pi_r x^{s_1}:A.B:s_3
 \qquad
 \Gamma\vdash u:A:s_1
}{
 \Gamma\vdash
 f@_r u:B[x:=u]:s_2
}.
\tag{App}
\]

role bridge の typing は

\[
\frac{
 \Gamma\vdash A:s_0
 \qquad
 (s_0,s_1)\in\mathcal A
}{
 \Gamma\vdash
 \operatorname{asTm}_{(s_0,s_1)}(A):s_0:s_1
}
\tag{AsTm}
\]

\[
\frac{
 \Gamma\vdash t:s_0:s_1
 \qquad
 (s_0,s_1)\in\mathcal A
}{
 \Gamma\vdash
 \operatorname{asTy}_{(s_0,s_1)}(t):s_0
}
\tag{AsTy}
\]

とする。erasure 後には、これらは現行体系の type-as-term の読み方と
Type-Sort rule になる。

### substitution

term variable に対する substitution は、二つの family を同時に保存する。

\[
\begin{aligned}
B\in\operatorname{Ty}^{s_2}
\land
u\in\operatorname{Tm}^{s_1}
&\Longrightarrow
B[x^{s_1}:=u]\in\operatorname{Ty}^{s_2},\\
t\in\operatorname{Tm}^{s_2}
\land
u\in\operatorname{Tm}^{s_1}
&\Longrightarrow
t[x^{s_1}:=u]\in\operatorname{Tm}^{s_2}.
\end{aligned}
\tag{Substitution-Sorting}
\]

polymorphic substitution では
\(u=\operatorname{asTm}_{a^q_i}(P)\) である。body 中の type occurrence は

\[
\operatorname{asTy}_{a^q_i}(X^{\sq^t_i})
[X^{\sq^t_i}:=
  \operatorname{asTm}_{a^q_i}(P)]
\]

となり、Role-Cancel によって \(P\) へ簡約する。

### static reduction と conversion

type reduction と static term reduction を family ごとに

\[
\longrightarrow^{\mathrm{ty}}_s
\ \subseteq\
\operatorname{Ty}^s\times\operatorname{Ty}^s,
\qquad
\longrightarrow^{\mathrm{st}}_s
\ \subseteq\
\operatorname{Tm}^s\times\operatorname{Tm}^s
\]

として定義する。compatible closure は subexpression の
\(\operatorname{Ty}/\operatorname{Tm}\) category を保存する。

bridge の内側の reduction は外側の family に持ち上げる。

\[
\frac{
 t\longrightarrow^{\mathrm{st}}_{s_1}t'
}{
 \operatorname{asTy}_{(s_0,s_1)}(t)
 \longrightarrow^{\mathrm{ty}}_{s_0}
 \operatorname{asTy}_{(s_0,s_1)}(t')
},
\qquad
\frac{
 A\longrightarrow^{\mathrm{ty}}_{s_0}A'
}{
 \operatorname{asTm}_{(s_0,s_1)}(A)
 \longrightarrow^{\mathrm{st}}_{s_1}
 \operatorname{asTm}_{(s_0,s_1)}(A')
}.
\tag{Role-Cong}
\]

Set/Prop の static rule と Program polymorphism の beta は
\(\longrightarrow^{\mathrm{st}}\) に属する。

\[
(\lambda_r x^{s_1}:A.t)@_r u
\longrightarrow^{\mathrm{st}}_{s_2}
t[x^{s_1}:=u]
\tag{Beta-st}
\]

ただし \(r\) は static rule とする。polymorphic beta では

\[
(\Lambda X:*^q_i.M)[P]
\longrightarrow^{\mathrm{st}}_{*^c_j}
M[X^\sharp:=P]
\tag{Poly-Beta}
\]

となる。右辺は上の substitution と Role-Cancel の合成の surface notation
である。

type conversion は

\[
\equiv^{\mathrm{ty}}_s
\ \coloneqq\
(\longrightarrow^{\mathrm{ty}}_s
\cup
\longleftarrow^{\mathrm{ty}}_s)^*
\]

とする。typing の conversion rule は

\[
\frac{
 \Gamma\vdash t:A:s
 \qquad
 \Gamma\vdash B:s
 \qquad
 A\equiv^{\mathrm{ty}}_s B
}{
 \Gamma\vdash t:B:s
}.
\tag{Conv}
\]

\(\operatorname{Ty}^{*^v_i}\) と
\(\operatorname{Ty}^{*^c_j}\) は異なる family なので、両者の type conversion は
混ざらない。rule label \(r\) の erasure が一致することも conversion の根拠には
ならない。

### CBPV operational reduction

CBPV computation の実行は

\[
\longrightarrow^{\mathrm{op}}_i
\ \subseteq\
\operatorname{Tm}^{*^c_i}
\times
\operatorname{Tm}^{*^c_i}
\]

とする。weak call-by-value の evaluation context を使い、主要な root rule は

\[
(\lambda_{r^{i,j}_{\mathrm{fun}}}x^{*^v_i}:A.M)
@_{r^{i,j}_{\mathrm{fun}}}V
\longrightarrow^{\mathrm{op}}_j
M[x^{*^v_i}:=V],
\tag{Beta-op}
\]

\[
\operatorname{force}(\operatorname{thunk}(M))
\longrightarrow^{\mathrm{op}}_i M,
\tag{Force-Thunk}
\]

\[
\operatorname{return}(V)
\ \operatorname{to}\ x^{*^v_i}:A\ \operatorname{in}\ N
\longrightarrow^{\mathrm{op}}_j
N[x^{*^v_i}:=V]
\tag{Return-To}
\]

である。run と runCase もこの relation に属する。Program type conversion に
使うのは \(\longrightarrow^{\mathrm{ty}}_{*^q_i}\) であり、
\(\longrightarrow^{\mathrm{op}}_i\) ではない。

## この分離で得られるもの

\(\operatorname{Ty}^s/\operatorname{Tm}^s\) に分けることで、例えば

\[
F:
\operatorname{Ty}^{*^v_i}
\longrightarrow
\operatorname{Ty}^{*^c_i}
\]

となり、value term

\[
V\in\operatorname{Tm}^{*^v_i}
\]

から \(F V\) を presyntax として作ることはできない。同様に、
\(\operatorname{return}\) は type ではなく value term だけを受け取る。

一方、同じ family の内部では actual type を index に持たない。したがって、

\[
V\in\operatorname{Tm}^{*^v_i}
\]

だけから \(V:A\) と \(V:A'\) のどちらであるかは分からない。application、
sequence、reflection の annotation との一致は typing judgement が検査する。

type-as-term bridge を明示したことで、generic PTS binder は常に

\[
x^{s_1}:A:s_1
\]

を導入する。polymorphism のためだけに \(d\neq s_1\) とする必要はない。
computed type、type operator の application、type variable は、一度
\(\operatorname{Tm}\) として sort を inhabit し、必要な type position で
\(\operatorname{asTy}\) を通る。surface syntax と raw PTS term ではこの bridge は
消去される。

## reflection

reflection は type と term で constructor を分ける。

\[
\frac{A\in\operatorname{Ty}^{*^q_i}}
     {\operatorname{RfType}(A)
      \in\operatorname{Ty}^{*^s_i}}
\tag{RfType-Syn}
\]

\[
\frac{
 A\in\operatorname{Ty}^{*^q_i}
 \qquad
 t\in\operatorname{Tm}^{*^q_i}
}{
 \operatorname{RfTerm}_A(t)
 \in\operatorname{Tm}^{*^s_i}
}.
\tag{RfTerm-Syn}
\]

typing は

\[
\frac{\Gamma\vdash A:*^q_i}
     {\Gamma\vdash\operatorname{RfType}(A):*^s_i}
\tag{RfType}
\]

\[
\frac{\Gamma\vdash t:A:*^q_i}
     {\Gamma\vdash
      \operatorname{RfTerm}_A(t):
      \operatorname{RfType}(A):*^s_i}
\tag{RfTerm}
\]

であり、principal level \(i\) を保存する。

type former の reflection は type reduction に属する。

\[
\operatorname{RfType}(F A)
\longrightarrow^{\mathrm{ty}}_{*^s_i}
\operatorname{RfType}(A),
\qquad
\operatorname{RfType}(U\underline B)
\longrightarrow^{\mathrm{ty}}_{*^s_i}
\operatorname{RfType}(\underline B).
\]

Program computation の観測は term reflection の境界で Set の static reduction
に持ち上げる。

\[
M\longrightarrow^{\mathrm{op}}_i M'
\quad\Longrightarrow\quad
\operatorname{RfTerm}_{\underline B}(M)
\longrightarrow^{\mathrm{st}}_{*^s_i}
\operatorname{RfTerm}_{\underline B}(M').
\tag{Rf-Cong}
\]

polymorphic type の reflection には cross-sort rule

\[
r^{i,j}_{\mathrm{Rf}}
=
(\sq^t_i,*^s_j,*^s_{\max(i+1,j)})
\]

を使う。

\[
\begin{aligned}
&\operatorname{RfType}
\left(
 \Pi_{r^{i,j}_{\mathrm{poly}}}
 X^{\sq^t_i}:*^q_i.\underline B
\right)\\
&\qquad
\longrightarrow^{\mathrm{ty}}_{*^s_k}
\Pi_{r^{i,j}_{\mathrm{Rf}}}
X^{\sq^t_i}:*^q_i.
\operatorname{RfType}(\underline B),
\end{aligned}
\tag{Rf-Poly}
\]

ただし \(k=\max(i+1,j)\) とする。右辺の body に現れる Program type variable
\(X\) も、checked syntax では
\(\operatorname{asTy}_{a^q_i}(X^{\sq^t_i})\) として使われる。

## universe level

Program universe は non-cumulative とし、judgement は principal level を常に
表示する。

\[
\Gamma\vdash A:*^q_i
\not\Rightarrow
\Gamma\vdash A:*^q_{i+1}.
\]

universe-polymorphic declaration では

\[
\ell::=
0
\mid\alpha
\mid\operatorname{succ}(\ell)
\mid\max(\ell,\ell)
\]

を使い、sort、rule、\(\operatorname{Ty}/\operatorname{Tm}\) の index を
level expression に一般化する。elaboration が level constraint を解き、reflection
は同じ level expression を Set 側へ渡す。

## 必要な性質

1. family-preserving substitution:
   term substitution は \(\operatorname{Ty}^s\) と
   \(\operatorname{Tm}^s\) の両方を保存する。

2. role coherence:
   well-typed な \(\operatorname{asTy}/\operatorname{asTm}\) は erasure 上で恒等であり、
   Role-Cancel と substitution が可換になる。

3. sorting soundness:
   type formation は \(\operatorname{Ty}^s\)、term typing は
   \(\operatorname{Tm}^s\) に elaborate できる。

4. subject reduction:
   type/static reduction は family と principal level を保存し、operational
   reduction は computation type と principal level を保存する。

5. labelled confluence:
   各 family の static reduction は well-typed checked syntax 上で
   Church--Rosser property を持つ。

6. phase separation:
   Program computation の step は operational relation に属し、reflection
   boundary を通して Set 側から観測される。

7. erasure coherence:
   checked syntax の reduction は raw PTS syntax の reduction と対応し、
   role annotation の選択によって計算結果が変わらない。

## 変更の段階

1. checked syntax を
   \(\operatorname{Ty}^s/\operatorname{Tm}^s\) の二 family に分ける。
2. sort を跨ぐ type-as-term 利用に
   \(\operatorname{asTy}/\operatorname{asTm}\) annotation を付ける。
3. Pi、lambda、application に \(r\in\mathcal R\) を保持する。
4. Program type former と term constructor をそれぞれ
   \(\operatorname{Ty}/\operatorname{Tm}\) に移す。
5. type conversion、static term reduction、CBPV operational reduction を
   family ごとに定義する。
6. reflection と level elaboration を二 family に対応させる。
