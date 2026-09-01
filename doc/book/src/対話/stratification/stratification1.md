## 体系定義

`system.md` の core calculus を、context に依存しない二つの syntax family

\[
\operatorname{Ty}^s,
\qquad
\operatorname{Tm}^s
\qquad(s\in\mathcal S)
\]

で層別する。意図する sorting は

\[
\begin{aligned}
\Gamma\vdash A:s
&\Longrightarrow A\in\operatorname{Ty}^s,\\
\Gamma\vdash t:A:s
&\Longrightarrow t\in\operatorname{Tm}^s
\end{aligned}
\tag{Sorting-Soundness}
\]

である。\(\operatorname{Ty}^s\) は sort \(s\) の型の presyntax、
\(\operatorname{Tm}^s\) は sort \(s\) に属する型の inhabitant の presyntax である。
どちらも context や実際の型を index に持たない。以下では checked syntax に
sort、PTS rule、型 annotation を残し、それらの一致を typing judgement で検査する。

### sort と PTS signature

Set/Prop の sort を

\[
\mathcal S_{sp}
=
\{*^s_i,\sq^s_i\mid i\in\mathbb N\}
\cup\{*^p,\sq^p\}
\]

とし、Program の sort を

\[
\mathcal S_t
=
\{*^v_i,*^c_i,\sq^t_i\mid i\in\mathbb N\}
\]

とする。全 sort は

\[
\mathcal S=\mathcal S_{sp}\cup\mathcal S_t
\]

である。axiom は

\[
\begin{aligned}
\mathcal A_{sp}
={}&
\{(*^s_i,\sq^s_i)\mid i\in\mathbb N\}
\cup\{(*^p,\sq^p)\},\\
\mathcal A_t
={}&
\{(*^v_i,\sq^t_i),(*^c_i,\sq^t_i)\mid i\in\mathbb N\},\\
\mathcal A
={}&\mathcal A_{sp}\cup\mathcal A_t
\end{aligned}
\]

とする。

Set/Prop の product rule は

\[
\begin{aligned}
\mathcal R_{sp}
=\bigcup_{i,j\in\mathbb N}
\{&
(*^s_i,*^s_j,*^s_{\max(i,j)}),
(*^s_i,\sq^s_j,\sq^s_{\max(i,j)}),\\
&
(\sq^s_i,\sq^s_j,\sq^s_{\max(i,j)}),
(\sq^s_i,*^s_j,*^s_{\max(i+1,j)}),\\
&
(*^s_i,*^p,*^p),
(*^s_i,\sq^p,\sq^p)
\}\\
\cup\{&
(*^p,*^p,*^p),
(\sq^p,*^p,*^p),
(\sq^p,\sq^p,\sq^p)
\}
\end{aligned}
\]

とする。Program function、Program type polymorphism、polymorphic type の
reflection に使う rule をそれぞれ

\[
\begin{aligned}
r^{i,j}_{\mathrm{fun}}
&=(*^v_i,*^c_j,*^c_{\max(i,j)}),\\
r^{i,j}_{\mathrm{poly}}
&=(\sq^t_i,*^c_j,*^c_{\max(i+1,j)}),\\
r^{i,j}_{\mathrm{Rf}}
&=(\sq^t_i,*^s_j,*^s_{\max(i+1,j)})
\end{aligned}
\]

と置き、

\[
\mathcal R
=
\mathcal R_{sp}
\cup
\{r^{i,j}_{\mathrm{fun}},r^{i,j}_{\mathrm{poly}},r^{i,j}_{\mathrm{Rf}}
\mid i,j\in\mathbb N\}
\]

とする。\(r^{i,j}_{\mathrm{poly}}\) の domain に現れる \(*^q_i\) は
\(q\in\{v,c\}\) のどちらでもよい。domain の sort はどちらの場合も
\(\sq^t_i\) なので、同じ PTS rule を使える。

### 基本構文

axiom \(a=(s_0,s_1)\in\mathcal A\) ごとに

\[
s_0\in\operatorname{Ty}^{s_1}
\tag{Sort-Syn}
\]

とし、variable は

\[
x^s\in\operatorname{Tm}^s
\tag{Var-Syn}
\]

とする。

\(r=(s_1,s_2,s_3)\in\mathcal R\) ごとに、PTS constructor を

\[
\frac{
 A\in\operatorname{Ty}^{s_1}
 \qquad
 B\in\operatorname{Ty}^{s_2}
}{
 \Pi_r x^{s_1}:A.B\in\operatorname{Ty}^{s_3}
}
\tag{Pi-Syn}
\]

\[
\frac{
 A\in\operatorname{Ty}^{s_1}
 \qquad
 t\in\operatorname{Tm}^{s_2}
}{
 \lambda_r x^{s_1}:A.t\in\operatorname{Tm}^{s_3}
}
\tag{Lam-Syn}
\]

\[
\frac{
 f\in\operatorname{Tm}^{s_3}
 \qquad
 u\in\operatorname{Tm}^{s_1}
}{
 f@_r u\in\operatorname{Tm}^{s_2}
}
\tag{App-Syn}
\]

で生成する。binder は常に \(x^{s_1}:A:s_1\) を導入する。

Russell-style PTS における type と term の役割の変更は、axiom
\(a=(s_0,s_1)\in\mathcal A\) ごとの bridge

\[
\frac{A\in\operatorname{Ty}^{s_0}}
     {\operatorname{asTm}_a(A)\in\operatorname{Tm}^{s_1}},
\qquad
\frac{t\in\operatorname{Tm}^{s_1}}
     {\operatorname{asTy}_a(t)\in\operatorname{Ty}^{s_0}}
\tag{Role-Syn}
\]

で表示する。raw syntax への erasure は

\[
|\operatorname{asTm}_a(A)|=|A|,
\qquad
|\operatorname{asTy}_a(t)|=|t|
\]

である。

例えば \(a^q_i=(*^q_i,\sq^t_i)\) とすると、Program type variable は

\[
X^{\sq^t_i}\in\operatorname{Tm}^{\sq^t_i}
\]

であり、type position では

\[
X^\sharp
\coloneqq
\operatorname{asTy}_{a^q_i}(X^{\sq^t_i})
\in\operatorname{Ty}^{*^q_i}
\]

と読む。

### Set/Prop 固有の構文

以下で、旧体系の type lift constructor は syntax family
\(\operatorname{Ty}^s\) と区別するため \(\mathsf{Ty}(A,B)\) と書く。

power set、subset、predicate の構文は

\[
\frac{A\in\operatorname{Ty}^{*^s_i}}
     {\Power A\in\operatorname{Ty}^{*^s_i}},
\tag{Power-Syn}
\]

\[
\frac{
 A\in\operatorname{Ty}^{*^s_i}
 \qquad
 P\in\operatorname{Ty}^{*^p}
}{
 \{x^{*^s_i}:A\mid P\}
 \in\operatorname{Tm}^{*^s_i}
},
\tag{Subset-Syn}
\]

\[
\frac{
 A\in\operatorname{Ty}^{*^s_i}
 \qquad
 B\in\operatorname{Tm}^{*^s_i}
}{
 \mathsf{Ty}(A,B)\in\operatorname{Ty}^{*^s_i}
},
\tag{Lift-Syn}
\]

\[
\frac{
 A\in\operatorname{Ty}^{*^s_i}
 \qquad
 B,t\in\operatorname{Tm}^{*^s_i}
}{
 \Pred(A,B,t)\in\operatorname{Ty}^{*^p}
}.
\tag{Pred-Syn}
\]

proof mark、equality、existence は

\[
\frac{P\in\operatorname{Ty}^{*^p}}
     {\Proof P\in\operatorname{Tm}^{*^p}},
\tag{Proof-Syn}
\]

\[
\frac{
 a,b\in\operatorname{Tm}^{*^s_i}
}{
 a=b\in\operatorname{Ty}^{*^p}
},
\tag{Eq-Syn}
\]

\[
\frac{A\in\operatorname{Ty}^{*^s_i}}
     {\exists A\in\operatorname{Ty}^{*^p}}
\tag{Exists-Syn}
\]

とする。等号の共通型は raw syntax に記録せず、typing rule が検査する。

choice の checked constructor は、結果の sort を区別して

\[
\frac{
 X,T\in\operatorname{Ty}^{*^s_i}
 \qquad
 f\in\operatorname{Tm}^{*^s_i}
}{
 \Take^s_i(X,T,f)\in\operatorname{Tm}^{*^s_i}
},
\tag{Take-Set-Syn}
\]

\[
\frac{
 X\in\operatorname{Ty}^{*^s_i}
 \qquad
 T\in\operatorname{Ty}^{*^p}
 \qquad
 f\in\operatorname{Tm}^{*^p}
}{
 \Take^p_i(X,T,f)\in\operatorname{Tm}^{*^p}
}.
\tag{Take-Prop-Syn}
\]

両方の surface notation は \(\Take(X,T,f)\) とする。

### Program 固有の構文

Program type former は \(\operatorname{Ty}\) 間の constructor とする。

\[
\frac{A\in\operatorname{Ty}^{*^v_i}}
     {F A\in\operatorname{Ty}^{*^c_i}},
\qquad
\frac{\underline B\in\operatorname{Ty}^{*^c_i}}
     {U\underline B\in\operatorname{Ty}^{*^v_i}},
\tag{FU-Syn}
\]

\[
\frac{
 A\in\operatorname{Ty}^{*^v_i}
 \qquad
 B\in\operatorname{Ty}^{*^v_j}
}{
 \operatorname{RunStep}(A,B)
 \in\operatorname{Ty}^{*^v_k}
}
\qquad(k=\max(i,j)).
\tag{RunStep-Syn}
\]

Program term constructor は

\[
\frac{V\in\operatorname{Tm}^{*^v_i}}
     {\operatorname{return}(V)\in\operatorname{Tm}^{*^c_i}},
\qquad
\frac{M\in\operatorname{Tm}^{*^c_i}}
     {\operatorname{thunk}(M)\in\operatorname{Tm}^{*^v_i}},
\tag{Return-Thunk-Syn}
\]

\[
\frac{V\in\operatorname{Tm}^{*^v_i}}
     {\operatorname{force}(V)\in\operatorname{Tm}^{*^c_i}},
\tag{Force-Syn}
\]

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
},
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
}.
\tag{Let-Syn}
\]

旧体系の value let は、この presyntax のうち \(s=*^c_j\) の instance を使う。

Program function は PTS constructor の
\(r^{i,j}_{\mathrm{fun}}\) instance である。非依存の場合は

\[
\begin{aligned}
A\Rightarrow\underline B
&\coloneqq
\Pi_{r^{i,j}_{\mathrm{fun}}}
x^{*^v_i}:A.\underline B,\\
\lambda x^{*^v_i}:A.M
&\coloneqq
\lambda_{r^{i,j}_{\mathrm{fun}}}x^{*^v_i}:A.M,\\
M@^cV
&\coloneqq M@_{r^{i,j}_{\mathrm{fun}}}V
\end{aligned}
\]

と書く。

continue と finish は

\[
\frac{
 A\in\operatorname{Ty}^{*^v_i}
 \quad B\in\operatorname{Ty}^{*^v_j}
 \quad a\in\operatorname{Tm}^{*^v_i}
}{
 \operatorname{continue}_{A,B}(a)
 \in\operatorname{Tm}^{*^v_k}
},
\tag{Continue-Syn}
\]

\[
\frac{
 A\in\operatorname{Ty}^{*^v_i}
 \quad B\in\operatorname{Ty}^{*^v_j}
 \quad b\in\operatorname{Tm}^{*^v_j}
}{
 \operatorname{finish}_{A,B}(b)
 \in\operatorname{Tm}^{*^v_k}
}
\qquad(k=\max(i,j)).
\tag{Finish-Syn}
\]

run と runCase は

\[
\frac{
 A\in\operatorname{Ty}^{*^v_i}
 \quad B\in\operatorname{Ty}^{*^v_j}
 \quad f\in\operatorname{Tm}^{*^v_k}
 \quad a\in\operatorname{Tm}^{*^v_i}
}{
 \operatorname{run}_{A,B}(f,a)
 \in\operatorname{Tm}^{*^c_j}
},
\tag{Run-Syn}
\]

\[
\frac{
 A\in\operatorname{Ty}^{*^v_i}
 \quad B\in\operatorname{Ty}^{*^v_j}
 \quad f\in\operatorname{Tm}^{*^v_k}
 \quad a\in\operatorname{Tm}^{*^v_i}
 \quad M\in\operatorname{Tm}^{*^c_k}
}{
 \operatorname{runCase}_{A,B}(f,a,M)
 \in\operatorname{Tm}^{*^c_j}
}
\qquad(k=\max(i,j)).
\tag{RunCase-Syn}
\]

### Program type polymorphism

\(q\in\{v,c\}\) とし、\(a^q_i=(*^q_i,\sq^t_i)\) と置く。
polymorphic product と abstraction は

\[
\Pi_{r^{i,j}_{\mathrm{poly}}}
X^{\sq^t_i}:*^q_i.\underline B
\in
\operatorname{Ty}^{*^c_k},
\]

\[
\lambda_{r^{i,j}_{\mathrm{poly}}}
X^{\sq^t_i}:*^q_i.M
\in
\operatorname{Tm}^{*^c_k}
\qquad(k=\max(i+1,j)).
\]

type argument \(P\in\operatorname{Ty}^{*^q_i}\) は

\[
\operatorname{asTm}_{a^q_i}(P)
\in\operatorname{Tm}^{\sq^t_i}
\]

として渡す。surface notation は

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

とする。body の type occurrence \(X\) は checked syntax で \(X^\sharp\) に
elaborate される。

### reflection と accessibility の構文

reflection は type と term で constructor を分ける。

\[
\frac{A\in\operatorname{Ty}^{*^q_i}}
     {\operatorname{RfType}(A)\in\operatorname{Ty}^{*^s_i}},
\tag{RfType-Syn}
\]

\[
\frac{
 A\in\operatorname{Ty}^{*^q_i}
 \qquad
 t\in\operatorname{Tm}^{*^q_i}
}{
 \operatorname{RfTerm}_A(t)\in\operatorname{Tm}^{*^s_i}
}
\qquad(q\in\{v,c\}).
\tag{RfTerm-Syn}
\]

\(A\in\operatorname{Ty}^{*^v_i}\)、
\(B\in\operatorname{Ty}^{*^v_j}\)、\(k=\max(i,j)\) に対して、

\[
\frac{
 f\in\operatorname{Tm}^{*^v_k}
 \qquad
 a\in\operatorname{Tm}^{*^s_i}
}{
 \operatorname{Acc}_{A,B}(f,a)\in\operatorname{Ty}^{*^p}
}.
\tag{Acc-Syn}
\]

### 帰納型から生成される構文

declaration environment \(\Delta\) には、level 付きの Program datatype 宣言

\[
\operatorname{inductive}
I^v( X_1:*^v_{i_1},\ldots,X_n:*^v_{i_n}):*^v_k
\ \operatorname{where}\
C_h^v:
A_{h1}\to\cdots\to A_{hm_h}\to I^v(\vec X)
\]

を置く。各 field type は parameter context の下で value type であり、再帰
occurrence は strictly positive とする。すなわち

\[
X_1:*^v_{i_1},\ldots,X_n:*^v_{i_n}
\vdash A_{hj}:*^v_{d_{hj}}
\]

を要求し、self occurrence を \(U(A\Rightarrow\underline B)\) の function domain
に置く宣言は拒否する。declaration ごとに次の構文を生成する。

\[
I^v(\vec A)\in\operatorname{Ty}^{*^v_k},
\qquad
C_h^v[\vec A](\vec V)\in\operatorname{Tm}^{*^v_k},
\tag{Ind-Program-Syn}
\]

\[
\operatorname{case}^v
\left(
 V;
 \overline{C_h^v(\vec x_h)\mapsto M_h}
\right)
\in\operatorname{Tm}^{*^c_j}.
\tag{Case-Program-Syn}
\]

同じ宣言から Set 側の鏡像名 \(I^s,C_h^s\) を生成する。

\[
I^s(\operatorname{RfType}(\vec A))
\in\operatorname{Ty}^{*^s_k},
\qquad
C_h^s[\operatorname{RfType}(\vec A)](\vec t)
\in\operatorname{Tm}^{*^s_k}.
\tag{Ind-Set-Syn}
\]

Set case と induction の constructor も \(\Delta\) の各宣言から生成し、
scrutinee、motive、branch の \(\operatorname{Ty}/\operatorname{Tm}\) category と
sort index を declaration の level から決める。

### substitution

term substitution は二つの family を同時に保存する。

\[
\begin{aligned}
B\in\operatorname{Ty}^{s_2}
\land u\in\operatorname{Tm}^{s_1}
&\Longrightarrow
B[x^{s_1}:=u]\in\operatorname{Ty}^{s_2},\\
t\in\operatorname{Tm}^{s_2}
\land u\in\operatorname{Tm}^{s_1}
&\Longrightarrow
t[x^{s_1}:=u]\in\operatorname{Tm}^{s_2}.
\end{aligned}
\tag{Substitution-Sorting}
\]

polymorphic substitution では
\(u=\operatorname{asTm}_{a^q_i}(P)\) である。body の type occurrence は

\[
\operatorname{asTy}_{a^q_i}(X^{\sq^t_i})
[X^{\sq^t_i}:=\operatorname{asTm}_{a^q_i}(P)]
\]

となり、後述する Role-Cancel により \(P\) へ簡約する。

### reduction

type reduction と static term reduction は

\[
\longrightarrow^{\mathrm{ty}}_s
\ \subseteq\
\operatorname{Ty}^s\times\operatorname{Ty}^s,
\qquad
\longrightarrow^{\mathrm{st}}_s
\ \subseteq\
\operatorname{Tm}^s\times\operatorname{Tm}^s
\]

とする。どちらも、各 constructor の argument category を保つ compatible closure
を取る。

role annotation の cancellation と congruence は

\[
\begin{aligned}
\operatorname{asTy}_a(\operatorname{asTm}_a(A))
&\longrightarrow^{\mathrm{ty}}_{s_0}A,\\
\operatorname{asTm}_a(\operatorname{asTy}_a(t))
&\longrightarrow^{\mathrm{st}}_{s_1}t
\end{aligned}
\qquad(a=(s_0,s_1))
\tag{Role-Cancel}
\]

\[
\frac{t\longrightarrow^{\mathrm{st}}_{s_1}t'}
     {\operatorname{asTy}_a(t)
      \longrightarrow^{\mathrm{ty}}_{s_0}
      \operatorname{asTy}_a(t')},
\qquad
\frac{A\longrightarrow^{\mathrm{ty}}_{s_0}A'}
     {\operatorname{asTm}_a(A)
      \longrightarrow^{\mathrm{st}}_{s_1}
      \operatorname{asTm}_a(A')}
\tag{Role-Cong}
\]

とする。

\[
\mathcal R_{\mathrm{st}}
\coloneqq
\mathcal R\setminus
\{r^{i,j}_{\mathrm{fun}}\mid i,j\in\mathbb N\}
\]

とする。\(r\in\mathcal R_{\mathrm{st}}\) に対する beta は static reduction
であり、Program function の beta だけを operational reduction に置く。

\[
(\lambda_r x^{s_1}:A.t)@_r u
\longrightarrow^{\mathrm{st}}_{s_2}
t[x^{s_1}:=u].
\tag{Beta-st}
\]

特に

\[
(\Lambda X:*^q_i.M)[P]
\longrightarrow^{\mathrm{st}}_{*^c_j}
M[X^\sharp:=P]
\tag{Poly-Beta}
\]

と書く。右辺は substitution と Role-Cancel の合成の surface notation である。

subset predicate の root rule も type reduction とする。\(a^p=(*^p,\sq^p)\)、
\(r^i_{\mathrm{pred}}=(*^s_i,\sq^p,\sq^p)\) と置くと、checked syntax では

\[
\begin{aligned}
&\Pred(A,\{x^{*^s_i}:B\mid P\},t)\\
&\quad\longrightarrow^{\mathrm{ty}}_{*^p}
\operatorname{asTy}_{a^p}
\left(
 (\lambda_{r^i_{\mathrm{pred}}}x^{*^s_i}:B.
   \operatorname{asTm}_{a^p}(P))
 @_{r^i_{\mathrm{pred}}}t
\right).
\end{aligned}
\tag{Pred-Red}
\]

well-typed な左辺では \(A\) と \(B\) の convertibility を typing から回収する。

reflection の type reduction は

\[
\operatorname{RfType}(F A)
\longrightarrow^{\mathrm{ty}}_{*^s_i}
\operatorname{RfType}(A),
\qquad
\operatorname{RfType}(U\underline B)
\longrightarrow^{\mathrm{ty}}_{*^s_i}
\operatorname{RfType}(\underline B),
\tag{Rf-FU}
\]

\[
\begin{aligned}
\operatorname{RfType}(A\Rightarrow\underline B)
&\longrightarrow^{\mathrm{ty}}_{*^s_k}
\Pi_{r^{i,j}_{ss}}
x^{*^s_i}:\operatorname{RfType}(A).
\operatorname{RfType}(\underline B),\\
r^{i,j}_{ss}
&=(*^s_i,*^s_j,*^s_k),
\qquad k=\max(i,j),
\end{aligned}
\tag{Rf-Fun}
\]

とする。Rf-Fun の surface function typeは非依存な場合である。

polymorphic type に対しては

\[
\begin{aligned}
&\operatorname{RfType}
\left(
 \Pi_{r^{i,j}_{\mathrm{poly}}}
 X^{\sq^t_i}:*^q_i.\underline B
\right)\\
&\quad\longrightarrow^{\mathrm{ty}}_{*^s_k}
\Pi_{r^{i,j}_{\mathrm{Rf}}}
X^{\sq^t_i}:*^q_i.
\operatorname{RfType}(\underline B),
\qquad k=\max(i+1,j).
\end{aligned}
\tag{Rf-Poly}
\]

term reflection の static root rule は

\[
\operatorname{RfTerm}_{F A}(\operatorname{return}(V))
\longrightarrow^{\mathrm{st}}_{*^s_i}
\operatorname{RfTerm}_A(V),
\tag{Rf-Return}
\]

\[
\operatorname{RfTerm}_{U\underline B}(\operatorname{thunk}(M))
\longrightarrow^{\mathrm{st}}_{*^s_i}
\operatorname{RfTerm}_{\underline B}(M).
\tag{Rf-Thunk}
\]

\(r^{i,j}_{ss}=(*^s_i,*^s_j,*^s_k)\) とすると application の reflection は

\[
\begin{aligned}
&\operatorname{RfTerm}_{U(A\Rightarrow\underline B)}(f)
@_{r^{i,j}_{ss}}
\operatorname{RfTerm}_A(a)\\
&\quad\longrightarrow^{\mathrm{st}}_{*^s_j}
\operatorname{RfTerm}_{\underline B}
(\operatorname{force}(f)@^c a),
\end{aligned}
\tag{Rf-U-App}
\]

\[
\begin{aligned}
&\operatorname{RfTerm}_{A\Rightarrow\underline B}(M)
@_{r^{i,j}_{ss}}
\operatorname{RfTerm}_A(a)\\
&\quad\longrightarrow^{\mathrm{st}}_{*^s_j}
\operatorname{RfTerm}_{\underline B}(M@^c a).
\end{aligned}
\tag{Rf-C-App}
\]

Program operational reduction は

\[
\longrightarrow^{\mathrm{op}}_i
\ \subseteq\
\operatorname{Tm}^{*^c_i}\times\operatorname{Tm}^{*^c_i}
\]

とする。evaluation context は

\[
\begin{aligned}
E::={}&[\,]
\mid E@_{r^{h,i}_{\mathrm{fun}}}V\\
&\mid E\ \operatorname{to}\ x^{*^v_i}:A\ \operatorname{in}\ N\\
&\mid\operatorname{runCase}_{A,B}(f,a,E)
\end{aligned}
\]

である。level を明示すると、evaluation context は

\[
E:
\operatorname{Tm}^{*^c_h}
\rightsquigarrow
\operatorname{Tm}^{*^c_i}
\]

という input/output family を持つ。root rule は

\[
(\lambda_{r^{h,i}_{\mathrm{fun}}}x^{*^v_h}:A.M)
@_{r^{h,i}_{\mathrm{fun}}}V
\longrightarrow^{\mathrm{op}}_i
M[x^{*^v_h}:=V],
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
N[x^{*^v_i}:=V],
\tag{Return-To}
\]

\[
\operatorname{let}^v x^{*^v_i}:A=V\ \operatorname{in}\ N
\longrightarrow^{\mathrm{op}}_j
N[x^{*^v_i}:=V],
\tag{Let-v}
\]

\[
\operatorname{run}_{A,B}(f,a)
\longrightarrow^{\mathrm{op}}_j
\operatorname{runCase}_{A,B}
(f,a,\operatorname{force}(f)@^c a),
\tag{Run-Unfold}
\]

\[
\begin{aligned}
&\operatorname{runCase}_{A,B}
(f,a,\operatorname{return}(\operatorname{continue}_{A,B}(a')))\\
&\quad\longrightarrow^{\mathrm{op}}_j
\operatorname{run}_{A,B}(f,a'),
\end{aligned}
\tag{Run-Continue}
\]

\[
\begin{aligned}
&\operatorname{runCase}_{A,B}
(f,a,\operatorname{return}(\operatorname{finish}_{A,B}(b)))\\
&\quad\longrightarrow^{\mathrm{op}}_j
\operatorname{return}(b),
\end{aligned}
\tag{Run-Finish}
\]

および

\[
\frac{
 M\longrightarrow^{\mathrm{op}}_hM'
 \qquad
 E:\operatorname{Tm}^{*^c_h}
 \rightsquigarrow\operatorname{Tm}^{*^c_i}
}{
 E[M]\longrightarrow^{\mathrm{op}}_iE[M']
}
\tag{Op-Ctx}
\]

である。

Program case とその reflection は

\[
\begin{aligned}
&\operatorname{case}^v
\left(
C_h^v[\vec A](\vec V);
\overline{C_l^v(\vec x_l)\mapsto M_l}
\right)\\
&\quad\longrightarrow^{\mathrm{op}}_j
M_h[\vec x_h:=\vec V],
\end{aligned}
\tag{Case-v}
\]

\[
\operatorname{RfType}(I^v(\vec A))
\longrightarrow^{\mathrm{ty}}_{*^s_k}
I^s(\operatorname{RfType}(\vec A)),
\tag{Rf-Ind}
\]

\[
\begin{aligned}
&\operatorname{RfTerm}_{I^v(\vec A)}
\left(C_h^v[\vec A](\vec V)\right)\\
&\quad\longrightarrow^{\mathrm{st}}_{*^s_k}
C_h^s[\operatorname{RfType}(\vec A)]
\left(
\overrightarrow{
\operatorname{RfTerm}_{A_{hj}[\vec X:=\vec A]}(V_j)
}
\right).
\end{aligned}
\tag{Rf-Ctor}
\]

Program computation は reflection boundary で Set の static reduction に
持ち上がる。

\[
\frac{M\longrightarrow^{\mathrm{op}}_iM'}
     {\operatorname{RfTerm}_{\underline B}(M)
      \longrightarrow^{\mathrm{st}}_{*^s_i}
      \operatorname{RfTerm}_{\underline B}(M')}
\tag{Rf-Cong}
\]

type conversion は

\[
\equiv^{\mathrm{ty}}_s
\ \coloneqq\
(\longrightarrow^{\mathrm{ty}}_s
 \cup
 \longleftarrow^{\mathrm{ty}}_s)^*
\]

とする。\(\operatorname{Ty}^{*^v_i}\) と
\(\operatorname{Ty}^{*^c_j}\) は別の family なので、value type と computation
type の conversion は混ざらない。Program の operational step も type
conversion には使わない。

### context と judgement

declaration environment \(\Delta\) を固定し、通常は judgement から省略する。
context と judgement は

\[
\Gamma::=\varnothing\mid\Gamma,x^s:A:s,
\]

\[
\operatorname{WF}(\Gamma),
\qquad
\Gamma\vdash A:s,
\qquad
\Gamma\vdash t:A:s,
\qquad
\Gamma\vDash P
\]

とする。Program value variable は \(x^{*^v_i}\)、Program type variable は
\(X^{\sq^t_i}\) であり、どちらも同じ context entry を使う。

context formation、sort、variable、weakening は

\[
\operatorname{WF}(\varnothing),
\qquad
\frac{
 \operatorname{WF}(\Gamma)
 \quad \Gamma\vdash A:s
 \quad x^s\notin\Gamma
}{
 \operatorname{WF}(\Gamma,x^s:A:s)
},
\tag{Ctx}
\]

\[
\frac{
 \operatorname{WF}(\Gamma)
 \qquad(s_0,s_1)\in\mathcal A
}{
 \Gamma\vdash s_0:s_1
},
\tag{Sort}
\]

\[
\frac{\operatorname{WF}(\Gamma,x^s:A:s)}
     {\Gamma,x^s:A:s\vdash x^s:A:s},
\tag{Var}
\]

\[
\frac{
 \Gamma\vdash J
 \qquad
 \operatorname{WF}(\Gamma,x^s:A:s)
}{
 \Gamma,x^s:A:s\vdash J
}
\tag{Weak}
\]

とする。Weak の \(J\) は type formation または term typing で、binder は
\(J\) の自由変数を capture しない。

PTS の主要な rule は syntax に記録された
\(r=(s_1,s_2,s_3)\) を検査する。

\[
\frac{
 \Gamma\vdash A:s_1
 \qquad
 \Gamma,x^{s_1}:A:s_1\vdash B:s_2
}{
 \Gamma\vdash\Pi_r x^{s_1}:A.B:s_3
},
\tag{Pi}
\]

\[
\frac{
 \Gamma\vdash\Pi_r x^{s_1}:A.B:s_3
 \qquad
 \Gamma,x^{s_1}:A:s_1\vdash t:B:s_2
}{
 \Gamma\vdash
 \lambda_r x^{s_1}:A.t:
 \Pi_r x^{s_1}:A.B:s_3
},
\tag{Lam}
\]

\[
\frac{
 \Gamma\vdash f:\Pi_r x^{s_1}:A.B:s_3
 \qquad
 \Gamma\vdash u:A:s_1
}{
 \Gamma\vdash f@_r u:B[x^{s_1}:=u]:s_2
}.
\tag{App}
\]

role bridge の typing は

\[
\frac{
 \Gamma\vdash A:s_0
 \qquad
 a=(s_0,s_1)\in\mathcal A
}{
 \Gamma\vdash\operatorname{asTm}_a(A):s_0:s_1
},
\tag{AsTm}
\]

\[
\frac{
 \Gamma\vdash t:s_0:s_1
 \qquad
 a=(s_0,s_1)\in\mathcal A
}{
 \Gamma\vdash\operatorname{asTy}_a(t):s_0
}.
\tag{AsTy}
\]

conversion rule は

\[
\frac{
 \Gamma\vdash t:A:s
 \qquad
 \Gamma\vdash B:s
 \qquad
 A\equiv^{\mathrm{ty}}_sB
}{
 \Gamma\vdash t:B:s
}.
\tag{Conv}
\]

### Set/Prop の judgement

provability と proof mark は

\[
\frac{\Gamma\vdash t:P:*^p}{\Gamma\vDash P},
\qquad
\frac{\Gamma\vDash P}
     {\Gamma\vdash\Proof P:P:*^p}
\tag{Provable}
\]

とする。

power set と subset の rule は

\[
\frac{\Gamma\vdash A:*^s_i}
     {\Gamma\vdash\Power A:*^s_i},
\tag{Power}
\]

\[
\frac{
 \Gamma\vdash A:*^s_i
 \qquad
 \Gamma\vdash B:\Power A:*^s_i
}{
 \Gamma\vdash\mathsf{Ty}(A,B):*^s_i
},
\tag{Lift}
\]

\[
\frac{
 \Gamma\vdash B:\Power A:*^s_i
 \qquad
 \Gamma\vdash t:A:*^s_i
}{
 \Gamma\vdash\Pred(A,B,t):*^p
},
\tag{Pred}
\]

\[
\frac{
 \Gamma\vdash A:*^s_i
 \qquad
 \Gamma,x^{*^s_i}:A:*^s_i\vdash P:*^p
}{
 \Gamma\vdash
 \{x^{*^s_i}:A\mid P\}:\Power A:*^s_i
},
\tag{Subset-Form}
\]

\[
\frac{
 \Gamma\vdash B:\Power A:*^s_i
 \quad
 \Gamma\vdash t:A:*^s_i
 \quad
 \Gamma\vDash\Pred(A,B,t)
}{
 \Gamma\vdash t:\mathsf{Ty}(A,B):*^s_i
},
\tag{Subset-Intro}
\]

\[
\frac{\Gamma\vdash t:\mathsf{Ty}(A,B):*^s_i}
     {\Gamma\vdash t:A:*^s_i},
\qquad
\frac{\Gamma\vdash t:\mathsf{Ty}(A,B):*^s_i}
     {\Gamma\vDash\Pred(A,B,t)}.
\tag{Subset-Elim}
\]

identity の rule は

\[
\frac{
 \Gamma\vdash a:A:*^s_i
 \qquad
 \Gamma\vdash b:A:*^s_i
}{
 \Gamma\vdash a=b:*^p
},
\tag{Eq-Form}
\]

\[
\frac{\Gamma\vdash a:A:*^s_i}
     {\Gamma\vDash a=a},
\tag{Eq-Refl}
\]

\[
\frac{
 \Gamma\vdash a:A:*^s_i
 \quad
 \Gamma\vdash b:A:*^s_i
 \quad
 \Gamma\vDash a=b
 \quad
 \Gamma,x^{*^s_i}:A:*^s_i\vdash P:*^p
 \quad
 \Gamma\vDash P[x:=a]
}{
 \Gamma\vDash P[x:=b]
}.
\tag{Eq-Elim}
\]

existence と choice の rule は

\[
\frac{\Gamma\vdash X:*^s_i}
     {\Gamma\vdash\exists X:*^p},
\qquad
\frac{\Gamma\vdash e:X:*^s_i}
     {\Gamma\vDash\exists X},
\tag{Exists}
\]

\[
\frac{
 \Gamma\vdash X:*^s_i
 \quad
 \Gamma\vdash T:*^s_i
 \quad
 \Gamma\vdash f:X\to T:*^s_i
 \quad
 \Gamma\vDash\exists X
 \quad
 \Gamma\vDash
 (x_1:X)\to(x_2:X)\to
 f@x_1=f@x_2
}{
 \Gamma\vdash\Take^s_i(X,T,f):T:*^s_i
},
\tag{Take-Set}
\]

\[
\frac{
 \Gamma\vdash X:*^s_i
 \quad
 \Gamma\vdash T:*^p
 \quad
 \Gamma\vdash f:X\to T:*^p
 \quad
 \Gamma\vDash\exists X
}{
 \Gamma\vdash\Take^p_i(X,T,f):T:*^p
},
\tag{Take-Prop}
\]

\[
\frac{
 \Gamma\vdash\Take^s_i(X,T,f):T:*^s_i
 \qquad
 \Gamma\vdash t:X:*^s_i
}{
 \Gamma\vDash
 \Take^s_i(X,T,f)=f@t
}.
\tag{Take-Eq}
\]

ここで矢印、lambda、application は対応する
\(r\in\mathcal R_{sp}\) を持つ checked PTS syntax の surface notation である。

### Program の judgement

Program type former の typing は

\[
\frac{\Gamma\vdash A:*^v_i}
     {\Gamma\vdash F A:*^c_i},
\qquad
\frac{\Gamma\vdash\underline B:*^c_i}
     {\Gamma\vdash U\underline B:*^v_i},
\tag{FU}
\]

\[
\frac{
 \Gamma\vdash A:*^v_i
 \qquad
 \Gamma\vdash B:*^v_j
}{
 \Gamma\vdash\operatorname{RunStep}(A,B):*^v_k
}
\qquad(k=\max(i,j)).
\tag{RunStep}
\]

function formation、introduction、elimination は Pi、Lam、App の
\(r^{i,j}_{\mathrm{fun}}\) instance である。基本的な CBPV rule は

\[
\frac{\Gamma\vdash V:A:*^v_i}
     {\Gamma\vdash\operatorname{return}(V):F A:*^c_i},
\tag{Return}
\]

\[
\frac{\Gamma\vdash M:\underline B:*^c_i}
     {\Gamma\vdash\operatorname{thunk}(M):U\underline B:*^v_i},
\qquad
\frac{\Gamma\vdash V:U\underline B:*^v_i}
     {\Gamma\vdash\operatorname{force}(V):\underline B:*^c_i},
\tag{Thunk-Force}
\]

\[
\frac{
 \Gamma\vdash M:F A:*^c_i
 \qquad
 \Gamma,x^{*^v_i}:A:*^v_i\vdash N:\underline B:*^c_j
}{
 \Gamma\vdash
 M\ \operatorname{to}\ x^{*^v_i}:A\ \operatorname{in}\ N:
 \underline B:*^c_j
},
\tag{Sequence}
\]

\[
\frac{
 \Gamma\vdash V:A:*^v_i
 \qquad
 \Gamma,x^{*^v_i}:A:*^v_i\vdash N:\underline B:*^c_j
}{
 \Gamma\vdash
 \operatorname{let}^v x^{*^v_i}:A=V\ \operatorname{in}\ N:
 \underline B:*^c_j
}.
\tag{Let-v-Typing}
\]

continue と finish は

\[
\frac{
 \Gamma\vdash a:A:*^v_i
 \qquad
 \Gamma\vdash B:*^v_j
}{
 \Gamma\vdash
 \operatorname{continue}_{A,B}(a):
 \operatorname{RunStep}(A,B):*^v_k
},
\tag{Continue}
\]

\[
\frac{
 \Gamma\vdash A:*^v_i
 \qquad
 \Gamma\vdash b:B:*^v_j
}{
 \Gamma\vdash
 \operatorname{finish}_{A,B}(b):
 \operatorname{RunStep}(A,B):*^v_k
}
\qquad(k=\max(i,j)).
\tag{Finish}
\]

Program polymorphism も generic Pi、Lam、App rule の instance である。例えば

\[
\frac{
 \Gamma\vdash *^q_i:\sq^t_i
 \qquad
 \Gamma,X^{\sq^t_i}:*^q_i:\sq^t_i
 \vdash\underline B:*^c_j
}{
 \Gamma\vdash
 \Pi_{r^{i,j}_{\mathrm{poly}}}
 X^{\sq^t_i}:*^q_i.\underline B:*^c_k
}
\qquad(k=\max(i+1,j)).
\tag{Poly-Form}
\]

### reflection、Acc、run の judgement

reflection typing は principal level を保存する。

\[
\frac{\Gamma\vdash A:*^q_i}
     {\Gamma\vdash\operatorname{RfType}(A):*^s_i},
\qquad
\frac{\Gamma\vdash t:A:*^q_i}
     {\Gamma\vdash
      \operatorname{RfTerm}_A(t):
      \operatorname{RfType}(A):*^s_i}.
\tag{Reflection}
\]

\(A:*^v_i\)、\(B:*^v_j\)、\(k=\max(i,j)\) に対して略記を

\[
\begin{aligned}
\operatorname{StepFun}(A,B)
&\coloneqq
U\left(A\Rightarrow F(\operatorname{RunStep}(A,B))\right),\\
\operatorname{continueFun}_{A,B}
&\coloneqq
\operatorname{thunk}
\left(
\lambda x^{*^v_i}:A.
\operatorname{return}
(\operatorname{continue}_{A,B}(x^{*^v_i}))
\right)
\end{aligned}
\]

とする。このとき \(\operatorname{StepFun}(A,B):*^v_k\) である。
さらに

\[
\begin{aligned}
\operatorname{Next}_{A,B}(f,b,a)
\coloneqq{}&
 \operatorname{RfTerm}_{\operatorname{StepFun}(A,B)}(f)
 @_{r^{i,k}_{ss}} a\\
&=
 \operatorname{RfTerm}_{\operatorname{StepFun}(A,B)}
 (\operatorname{continueFun}_{A,B})
 @_{r^{i,k}_{ss}} b,\\
\operatorname{Terminates}_{A,B}(f,a)
\coloneqq{}&
\operatorname{Acc}_{A,B}
(f,\operatorname{RfTerm}_A(a)),\\
\operatorname{RunInv}_{A,B}(f,a,M)
\coloneqq{}&
 \operatorname{RfTerm}_{F(\operatorname{RunStep}(A,B))}
 (\operatorname{force}(f)@^c a)\\
&=
 \operatorname{RfTerm}_{F(\operatorname{RunStep}(A,B))}(M).
\end{aligned}
\]

\(\operatorname{Next}_{A,B}(f,b,a)\) の \(a,b\) は
\(\operatorname{RfType}(A)\) の Set term であり、
\(\operatorname{Terminates}_{A,B}(f,a)\) の \(a\) は Program value である。

Acc の rule は

\[
\frac{
 \Gamma\vdash f:\operatorname{StepFun}(A,B):*^v_k
 \qquad
 \Gamma\vdash a:\operatorname{RfType}(A):*^s_i
}{
 \Gamma\vdash\operatorname{Acc}_{A,B}(f,a):*^p
},
\tag{Acc-Form}
\]

\[
\frac{
 \Gamma\vdash f:\operatorname{StepFun}(A,B):*^v_k
 \quad
 \Gamma\vdash a:\operatorname{RfType}(A):*^s_i
 \quad
 \Gamma,b^{*^s_i}:\operatorname{RfType}(A):*^s_i
 \vDash
 \operatorname{Next}_{A,B}(f,b^{*^s_i},a)
 \to
 \operatorname{Acc}_{A,B}(f,b^{*^s_i})
}{
 \Gamma\vDash\operatorname{Acc}_{A,B}(f,a)
},
\tag{Acc-Intro}
\]

\[
\frac{
 \Gamma\vDash\operatorname{Acc}_{A,B}(f,a)
 \qquad
 \Gamma\vDash\operatorname{Next}_{A,B}(f,b,a)
}{
 \Gamma\vDash\operatorname{Acc}_{A,B}(f,b)
}.
\tag{Acc-Descent}
\]

run と runCase の typing は

\[
\frac{
 \Gamma\vdash f:\operatorname{StepFun}(A,B):*^v_k
 \quad
 \Gamma\vdash a:A:*^v_i
 \quad
 \Gamma\vDash\operatorname{Terminates}_{A,B}(f,a)
}{
 \Gamma\vdash\operatorname{run}_{A,B}(f,a):F B:*^c_j
},
\tag{Run}
\]

\[
\frac{
 \Gamma\vdash f:\operatorname{StepFun}(A,B):*^v_k
 \quad
 \Gamma\vdash a:A:*^v_i
 \quad
 \Gamma\vdash M:F(\operatorname{RunStep}(A,B)):*^c_k
 \quad
 \Gamma\vDash\operatorname{Terminates}_{A,B}(f,a)
 \quad
 \Gamma\vDash\operatorname{RunInv}_{A,B}(f,a,M)
}{
 \Gamma\vdash\operatorname{runCase}_{A,B}(f,a,M):F B:*^c_j
}.
\tag{RunCase}
\]

### 帰納型の judgement

well-formed な declaration
\(I^v(\vec X):*^v_k\) に対する Program rule は

\[
\frac{
 \Gamma\vdash A_l:*^v_{i_l}
 \quad(1\leq l\leq n)
}{
 \Gamma\vdash I^v(\vec A):*^v_k
},
\tag{Ind-v-Form}
\]

\[
\frac{
 \Gamma\vdash
 V_j:A_{hj}[\vec X:=\vec A]:*^v_{d_{hj}}
 \quad(1\leq j\leq m_h)
}{
 \Gamma\vdash
 C_h^v[\vec A](\vec V):I^v(\vec A):*^v_k
},
\tag{Ctor-v}
\]

\[
\frac{
 \Gamma\vdash V:I^v(\vec A):*^v_k
 \quad
 \Gamma,
 \overrightarrow{
 x_{hj}^{*^v_{d_{hj}}}:
 A_{hj}[\vec X:=\vec A]:*^v_{d_{hj}}
 }
 \vdash M_h:\underline B:*^c_j
 \quad(\text{各 }h)
}{
 \Gamma\vdash
 \operatorname{case}^v
 \left(V;\overline{C_h^v(\vec x_h)\mapsto M_h}\right):
 \underline B:*^c_j
}.
\tag{Case-v-Typing}
\]

case は各 constructor の branch をちょうど一つ持ち、branch binder は fresh とする。

Set の鏡像は

\[
\frac{\Gamma\vdash A_l:*^v_{i_l}\quad(1\leq l\leq n)}
     {\Gamma\vdash
      I^s(\operatorname{RfType}(\vec A)):*^s_k},
\tag{Ind-s-Form}
\]

\[
\frac{
 \Gamma\vdash A_l:*^v_{i_l}\quad(1\leq l\leq n)
 \qquad
 \Gamma\vdash
 t_j:\operatorname{RfType}(A_{hj}[\vec X:=\vec A]):*^s_{d_{hj}}
 \quad(1\leq j\leq m_h)
}{
 \Gamma\vdash
 C_h^s[\operatorname{RfType}(\vec A)](\vec t):
 I^s(\operatorname{RfType}(\vec A)):*^s_k
}.
\tag{Ctor-s}
\]

Set case と induction の formation、branch、computation rule は、同じ
declaration の parameter、field、result level を \(*^v_d\) から \(*^s_d\) へ
写して生成する。

### universe level

Program universe は non-cumulative とし、judgement は principal level を表示する。

\[
\Gamma\vdash A:*^q_i
\not\Longrightarrow
\Gamma\vdash A:*^q_{i+1}.
\]

universe-polymorphic declaration では level expression

\[
\ell::=
0
\mid\alpha
\mid\operatorname{succ}(\ell)
\mid\max(\ell,\ell)
\]

を使い、sort、PTS rule、\(\operatorname{Ty}/\operatorname{Tm}\) の index を
\(\ell\) に一般化する。elaboration が level constraint を解き、reflection は
Program 側の principal level expression を Set 側へそのまま渡す。

## Ty/Tm への分離で変わる点

旧体系の四つの Program judgement

\[
\Gamma\vdash A\ \mathsf{vtype},
\quad
\Gamma\vdash\underline B\ \mathsf{ctype},
\quad
\Gamma\vdash_vV:A,
\quad
\Gamma\vdash_cM:\underline B
\]

は、それぞれ

\[
\Gamma\vdash A:*^v_i,
\quad
\Gamma\vdash\underline B:*^c_i,
\quad
\Gamma\vdash V:A:*^v_i,
\quad
\Gamma\vdash M:\underline B:*^c_i
\]

になる。これに対応して、Program type entry と value entry は通常の context
entry に統合される。

\(F\) は

\[
F:
\operatorname{Ty}^{*^v_i}
\longrightarrow
\operatorname{Ty}^{*^c_i}
\]

なので、value term \(V\in\operatorname{Tm}^{*^v_i}\) から \(F V\) を作れない。
一方、同じ \(\operatorname{Tm}^{*^v_i}\) の内部では actual type を index に
持たないため、\(V:A\) と \(V:A'\) の区別は typing judgement が検査する。

同じ理由で、\(\Take\)、\(\Power\)、\(\Proof\)、subset は Set/Prop family から
Program family へ入らない。停止性の derivation ではこれらを使えるが、
\(\operatorname{run}_{A,B}(f,a)\) の \(f\) と \(a\) は Program term でなければならない。
したがって \(\operatorname{run}(f,\Take(\cdots))\) は sorting の段階で作れない。

一段関数 \(f:\operatorname{StepFun}(A,B)\) には pure-term restriction を課さない。
thunk された function body の中で、すでに typing された別の run を使える。外側の
Run derivation から見ると、その内側の run の typing は proper subderivation に現れる。

PTS binder の variable は一貫して domain sort \(s_1\) の term である。
Program polymorphism の \(X\) も

\[
X^{\sq^t_i}:*^q_i:\sq^t_i
\]

として導入され、type position だけ \(X^\sharp\) に elaborate される。
これにより binder の sort を変更する特例を使わずに、type operator の application
と type polymorphism を generic Pi、Lam、App で表せる。

reduction は type、static term、Program operational computation に分かれる。
Program の step は \(\longrightarrow^{\mathrm{op}}\) に閉じ、Set/Prop からの観測は
Rf-Cong を通す。この phase separation により、Program の実行を Program type の
definitional equality に混ぜずに済む。

## case と run への elaboration

surface language の構造再帰は、core の Program case と run へ elaborate する。
再帰呼び出し後に計算を続ける定義や複数の recursive field を処理する定義では、
Program state に未処理の field、途中結果、defunctionalize した continuation stack
を含める。

elaboration が生成する step function は case で state の外側を一層だけ観察し、
continue で次状態を返す。Set/Prop 側では reflected datatype の induction や tree
height を使って step relation の Acc proof を生成する。この proof が Run rule の
\(\operatorname{Terminates}\) premise になる。

## 必要な性質

1. family-preserving renaming、weakening、substitution：mixed context に対する操作が
   \(\operatorname{Ty}^s\) と \(\operatorname{Tm}^s\) の category と sort index を
   保存する。
2. role coherence：well-typed な \(\operatorname{asTy}/\operatorname{asTm}\) は erasure
   上で恒等であり、Role-Cancel と substitution が可換になる。
3. sorting soundness：type formation と term typing の導出から、それぞれ対応する
   \(\operatorname{Ty}^s\)、\(\operatorname{Tm}^s\) membership を復元できる。
4. category uniqueness：well-typed checked syntax の type/term category、Program の
   value/computation category、principal level が一意になる。
5. subject reduction：type/static reduction は family と principal level を保存し、
   operational reduction は computation type と principal level を保存する。
6. labelled confluence：各 family の static reduction が well-typed checked syntax
   上で Church--Rosser property を持つ。
7. phase separation：Program computation は operational relation だけで進み、
   reflection boundary を通して Set 側から観測される。
8. erasure coherence：checked reduction は raw PTS syntax の reduction と対応し、
   role annotation の選択で計算結果が変わらない。
9. declaration soundness：datatype declaration の positivity と level constraint が、
   生成される Program/Set constructor、case、induction の typing を保証する。
10. run soundness：RunInv が reduction と substitution で保存され、Acc-Descent と
    run/runCase が model 上で妥当になる。

## 課題

- dependent な Program function type を Rf-Fun で Set 側へ写すときの binder の対応。
  現在の Rf-Fun は旧体系と同じ非依存な \(A\Rightarrow\underline B\) を対象にする。
- datatype declaration environment の well-formedness、strict positivity、level
  constraint の形式化。
- Set の鏡像に対して生成する case と induction の raw syntax、typing、reduction
  schema の完全な定義。
- \(\mathsf{Ty}\) constructor の引数 \(A\) を erasure できる条件と、power set の
  universe level。
- Pred-Red、Rf-Thunk、Rf-U-App、Rf-C-App、Rf-Ind、Rf-Ctor、Role-Cancel の
  critical-pair analysis。
- type reduction と static term reduction の全 compatible context、および両者を
  bridge が跨ぐ場合の confluence。
- Acc assumption を含む open context での停止定理の定式化。Program normalization
  は空 context、または意味論的に妥当な closing substitution に相対化する。
