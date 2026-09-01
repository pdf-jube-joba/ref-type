## 体系定義

### PTS signature

#### Sort

- \(\mathcal S_{sp}=\{*^s_i,\sq^s_i\mid i\in\mathbb N\}\cup\{*^p,\sq^p\}\)
- \(\mathcal S_t=\{*^v_i,\sq^v_i,*^c_i,\sq^c_i\mid i\in\mathbb N\}\)
- \(\mathcal S=\mathcal S_{sp}\cup\mathcal S_t\)

#### Axiom

- \(\mathcal A_{sp}=\{(*^s_i,\sq^s_i)\mid i\in\mathbb N\}\cup\{(*^p,\sq^p)\}\)
- \(\mathcal A_t=\{(*^v_i,\sq^v_i),(*^c_i,\sq^c_i)\mid i\in\mathbb N\}\)
- \(\mathcal A=\mathcal A_{sp}\cup\mathcal A_t\)

#### Sort map

- \(\uparrow:\mathcal S\rightharpoonup\mathcal S\)
- \(\uparrow(s_0)=s_1\Longleftrightarrow(s_0,s_1)\in\mathcal A\)

\[
\begin{aligned}
\uparrow(*^s_i)&=\sq^s_i,
&\uparrow(*^p)&=\sq^p,\\
\uparrow(*^v_i)&=\sq^v_i,
&\uparrow(*^c_i)&=\sq^c_i.
\end{aligned}
\tag{Sort-Up}
\]

- \(\downarrow:\operatorname{im}(\uparrow)\to\operatorname{dom}(\uparrow)\)

\[
\downarrow(\uparrow(s))=s.
\tag{Sort-Down}
\]

#### Product rule

- Set/Prop

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

- Program

\[
\begin{aligned}
\mathcal R
=\mathcal R_{sp}
\cup\bigcup_{i,j\in\mathbb N}\{&
(*^v_i,*^c_j,*^c_{\max(i,j)}),\\
&(\sq^v_i,*^c_j,*^c_{\max(i+1,j)}),
(\sq^c_i,*^c_j,*^c_{\max(i+1,j)}),\\
&(\sq^v_i,*^s_j,*^s_{\max(i+1,j)}),
(\sq^c_i,*^s_j,*^s_{\max(i+1,j)})
\}.
\end{aligned}
\tag{Rules}
\]

#### Notation

- \(q\in\{v,c\}\)
- \((*^q_i,\sq^q_i)=(*^v_i,\sq^v_i)\) if \(q=v\)
- \((*^q_i,\sq^q_i)=(*^c_i,\sq^c_i)\) if \(q=c\)

### Presyntax

#### Family

- Context-independent
- \(s\in\mathcal S\)
- \(\operatorname{Ty}^s\): type presyntax
- \(\operatorname{Tm}^s\): term presyntax

#### Sort / variable

\[
\frac{(s_0,s_1)\in\mathcal A}
     {s_0\in\operatorname{Ty}^{s_1}},
\qquad
x^s\in\operatorname{Tm}^s
\tag{Sort-Var-Syn}
\]

#### PTS constructor

- \((s_1,s_2,s_3)\in\mathcal R\)
- Binder: \(x^{s_1}:A:s_1\)
- \(\Pi\)

\[
\frac{
 A\in\operatorname{Ty}^{s_1}
 \qquad
 B\in\operatorname{Ty}^{s_2}
}{
 \Pi_{(s_1,s_2,s_3)}x^{s_1}:A.B\in\operatorname{Ty}^{s_3}
},
\tag{Pi-Syn}
\]

- \(\lambda\)

\[
\frac{
 A\in\operatorname{Ty}^{s_1}
 \qquad
 t\in\operatorname{Tm}^{s_2}
}{
 \lambda_{(s_1,s_2,s_3)}x^{s_1}:A.t\in\operatorname{Tm}^{s_3}
},
\tag{Lam-Syn}
\]

- Application

\[
\frac{
 f\in\operatorname{Tm}^{s_3}
 \qquad
 u\in\operatorname{Tm}^{s_1}
}{
 f@_{(s_1,s_2,s_3)}u\in\operatorname{Tm}^{s_2}
}.
\tag{App-Syn}
\]

### Role bridge

#### Constructor

- Type to term

\[
\frac{
 s\in\operatorname{dom}(\uparrow)
 \qquad
 A\in\operatorname{Ty}^{s}
}{
 \operatorname{asTm}(A)\in\operatorname{Tm}^{\uparrow(s)}
},
\tag{AsTm-Syn}
\]

- Term to type

\[
\frac{
 \kappa\in\operatorname{im}(\uparrow)
 \qquad
 t\in\operatorname{Tm}^{\kappa}
}{
 \operatorname{asTy}(t)\in\operatorname{Ty}^{\downarrow(\kappa)}
}.
\tag{AsTy-Syn}
\]

#### Erasure

\[
|\operatorname{asTm}(A)|=|A|,
\qquad
|\operatorname{asTy}(t)|=|t|
\]

#### Type-variable notation

- Term position: \(X^{\sq^q_i}\in\operatorname{Tm}^{\sq^q_i}\)
- Type position: \(\operatorname{asTy}(X^{\sq^q_i})\in\operatorname{Ty}^{*^q_i}\)

### Set / Prop

#### Constructor

\[
\begin{aligned}
\Power
&:\operatorname{Ty}^{*^s_i}
  \longrightarrow\operatorname{Ty}^{*^s_i},\\
\mathsf{Ty}
&:\operatorname{Ty}^{*^s_i}
  \times\operatorname{Tm}^{*^s_i}
  \longrightarrow\operatorname{Ty}^{*^s_i},\\
\Pred
&:\operatorname{Ty}^{*^s_i}
  \times\operatorname{Tm}^{*^s_i}
  \times\operatorname{Tm}^{*^s_i}
  \longrightarrow\operatorname{Ty}^{*^p},\\
(-=-)
&:\operatorname{Tm}^{*^s_i}
  \times\operatorname{Tm}^{*^s_i}
  \longrightarrow\operatorname{Ty}^{*^p},\\
\exists
&:\operatorname{Ty}^{*^s_i}
  \longrightarrow\operatorname{Ty}^{*^p},\\
\Proof
&:\operatorname{Ty}^{*^p}
  \longrightarrow\operatorname{Tm}^{*^p}.
\end{aligned}
\tag{Set-Prop-Syn}
\]

#### Subset

\[
\frac{
 A\in\operatorname{Ty}^{*^s_i}
 \qquad
 P\in\operatorname{Ty}^{*^p}
}{
 \{x^{*^s_i}:A\mid P\}\in\operatorname{Tm}^{*^s_i}
},
\tag{Subset-Syn}
\]

#### Choice

\[
\begin{aligned}
\Take^s_i
&:\operatorname{Ty}^{*^s_i}
  \times\operatorname{Ty}^{*^s_i}
  \times\operatorname{Tm}^{*^s_i}
  \longrightarrow\operatorname{Tm}^{*^s_i},\\
\Take^p_i
&:\operatorname{Ty}^{*^s_i}
  \times\operatorname{Ty}^{*^p}
  \times\operatorname{Tm}^{*^p}
  \longrightarrow\operatorname{Tm}^{*^p}
\end{aligned}
\tag{Take-Syn}
\]

### CBPV

#### Type former

\[
\frac{A\in\operatorname{Ty}^{*^v_i}}
     {F A\in\operatorname{Ty}^{*^c_i}},
\qquad
\frac{\underline B\in\operatorname{Ty}^{*^c_i}}
     {U\underline B\in\operatorname{Ty}^{*^v_i}},
\tag{FU-Syn}
\]

- Run step

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

#### Term constructor

- Return / thunk / force

\[
\frac{V\in\operatorname{Tm}^{*^v_i}}
     {\operatorname{return}(V)\in\operatorname{Tm}^{*^c_i}},
\qquad
\frac{M\in\operatorname{Tm}^{*^c_i}}
     {\operatorname{thunk}(M)\in\operatorname{Tm}^{*^v_i}},
\qquad
\frac{V\in\operatorname{Tm}^{*^v_i}}
     {\operatorname{force}(V)\in\operatorname{Tm}^{*^c_i}},
\tag{CBPV-Syn}
\]

- Sequencing

\[
\frac{
 M\in\operatorname{Tm}^{*^c_i}
 \quad
 A\in\operatorname{Ty}^{*^v_i}
 \quad
 N\in\operatorname{Tm}^{*^c_j}
}{
 M\ \operatorname{to}\ x^{*^v_i}:A\ \operatorname{in}\ N
 \in\operatorname{Tm}^{*^c_j}
},
\tag{Seq-Syn}
\]

- Value binding

\[
\frac{
 V\in\operatorname{Tm}^{*^v_i}
 \quad
 A\in\operatorname{Ty}^{*^v_i}
 \quad
 t\in\operatorname{Tm}^{s}
}{
 \operatorname{let}^v x^{*^v_i}:A=V\ \operatorname{in}\ t
 \in\operatorname{Tm}^{s}
}.
\tag{Let-Syn}
\]

#### Function

- \(k=\max(i,j)\)
- Surface notation:

\[
\begin{aligned}
A\Rightarrow\underline B
&\coloneqq
\Pi_{(*^v_i,*^c_j,*^c_k)}
x^{*^v_i}:A.\underline B,\\
\lambda x^{*^v_i}:A.M
&\coloneqq
\lambda_{(*^v_i,*^c_j,*^c_k)}x^{*^v_i}:A.M,\\
M@^cV
&\coloneqq M@_{(*^v_i,*^c_j,*^c_k)}V
\end{aligned}
\]

#### Run

- \(A\in\operatorname{Ty}^{*^v_i}\)
- \(B\in\operatorname{Ty}^{*^v_j}\)
- \(k=\max(i,j)\)
- Checked annotations: \(A,B\)

\[
\begin{aligned}
\operatorname{continue}_{A,B}
&:\operatorname{Tm}^{*^v_i}
  \longrightarrow\operatorname{Tm}^{*^v_k},\\
\operatorname{finish}_{A,B}
&:\operatorname{Tm}^{*^v_j}
  \longrightarrow\operatorname{Tm}^{*^v_k},\\
\operatorname{run}_{A,B}
&:\operatorname{Tm}^{*^v_k}
  \times\operatorname{Tm}^{*^v_i}
  \longrightarrow\operatorname{Tm}^{*^c_j},\\
\operatorname{runCase}_{A,B}
&:\operatorname{Tm}^{*^v_k}
  \times\operatorname{Tm}^{*^v_i}
  \times\operatorname{Tm}^{*^c_k}
  \longrightarrow\operatorname{Tm}^{*^c_j}
\end{aligned}
\tag{Run-Syn}
\]

### Polymorphism notation

- \(k=\max(i+1,j)\)
- Argument: \(P\in\operatorname{Ty}^{*^q_i}\)
- Encoded argument: \(\operatorname{asTm}(P)\in\operatorname{Tm}^{\sq^q_i}\)

\[
\begin{aligned}
\lambda X:*^q_i.M
&\coloneqq
\lambda_{(\sq^q_i,*^c_j,*^c_k)}
X^{\sq^q_i}:*^q_i.M,\\
M[P]
&\coloneqq
M@_{(\sq^q_i,*^c_j,*^c_k)}\operatorname{asTm}(P).
\end{aligned}
\tag{Poly-Surface}
\]

### Reflection / datatype

#### Reflection

\[
\frac{A\in\operatorname{Ty}^{*^q_i}}
     {\operatorname{RfType}(A)\in\operatorname{Ty}^{*^s_i}},
\qquad
\frac{
 A\in\operatorname{Ty}^{*^q_i}
 \quad t\in\operatorname{Tm}^{*^q_i}
}{
 \operatorname{RfTerm}_A(t)\in\operatorname{Tm}^{*^s_i}
}
\tag{Reflection-Syn}
\]

#### Datatype

- Declaration:

\[
I^v(X_1:*^v_{i_1},\ldots,X_n:*^v_{i_n}):*^v_k
\]

- Program:

\[
I^v(\vec A)\in\operatorname{Ty}^{*^v_k},
\qquad
C_h^v[\vec A](\vec V)\in\operatorname{Tm}^{*^v_k}
\]

- Set reflection:

\[
I^s(\operatorname{RfType}(\vec A))\in\operatorname{Ty}^{*^s_k},
\qquad
C_h^s[\operatorname{RfType}(\vec A)](\vec t)
\in\operatorname{Tm}^{*^s_k}
\]

- Default datatype parameter: \(\sq^v_i\)
- Optional computation parameter binder: \(\sq^c_i\)

### Reduction

#### Relation

\[
\begin{aligned}
\longrightarrow^{\mathrm{ty}}_s
&\subseteq
\operatorname{Ty}^s\times\operatorname{Ty}^s,\\
\longrightarrow^{\mathrm{st}}_s
&\subseteq
\operatorname{Tm}^s\times\operatorname{Tm}^s,\\
\longrightarrow^{\mathrm{op}}_i
&\subseteq
\operatorname{Tm}^{*^c_i}\times\operatorname{Tm}^{*^c_i}
\end{aligned}
\]

#### Role bridge

- Cancellation
- \(A\in\operatorname{Ty}^s\)
- \(t\in\operatorname{Tm}^{\kappa}\)
- \(\kappa=\uparrow(s)\)

\[
\operatorname{asTy}(\operatorname{asTm}(A))
\longrightarrow^{\mathrm{ty}}_s A,
\qquad
\operatorname{asTm}(\operatorname{asTy}(t))
\longrightarrow^{\mathrm{st}}_{\kappa}t,
\tag{Role-Cancel}
\]

- Congruence

\[
\frac{t\longrightarrow^{\mathrm{st}}_{\kappa}t'}
     {\operatorname{asTy}(t)
      \longrightarrow^{\mathrm{ty}}_{\downarrow(\kappa)}
      \operatorname{asTy}(t')},
\qquad
\frac{A\longrightarrow^{\mathrm{ty}}_sA'}
     {\operatorname{asTm}(A)
      \longrightarrow^{\mathrm{st}}_{\uparrow(s)}
      \operatorname{asTm}(A')}
\tag{Role-Cong}
\]

#### Static \(\beta\)

\[
\mathcal R_{\mathrm{st}}
\coloneqq
\mathcal R\setminus
\{(*^v_i,*^c_j,*^c_{\max(i,j)})\mid i,j\in\mathbb N\}
\]

- \((s_1,s_2,s_3)\in\mathcal R_{\mathrm{st}}\)

\[
(\lambda_{(s_1,s_2,s_3)}x^{s_1}:A.t)
@_{(s_1,s_2,s_3)}u
\longrightarrow^{\mathrm{st}}_{s_2}
t[x^{s_1}:=u]
\tag{Beta-st}
\]

#### Reflection

\[
\begin{aligned}
&\operatorname{RfType}
\left(
 \Pi_{(\sq^q_i,*^c_j,*^c_k)}
 X^{\sq^q_i}:*^q_i.\underline B
\right)\\
&\quad\longrightarrow^{\mathrm{ty}}_{*^s_k}
\Pi_{(\sq^q_i,*^s_j,*^s_k)}
X^{\sq^q_i}:*^q_i.
\operatorname{RfType}(\underline B),
\qquad k=\max(i+1,j).
\end{aligned}
\tag{Rf-Poly}
\]

#### CBPV operational reduction

- Function \(\beta\)

\[
(\lambda_{(*^v_i,*^c_j,*^c_k)}x^{*^v_i}:A.M)
@_{(*^v_i,*^c_j,*^c_k)}V
\longrightarrow^{\mathrm{op}}_j
M[x^{*^v_i}:=V]
\qquad(k=\max(i,j)),
\tag{Beta-op}
\]

- Force / sequencing

\[
\operatorname{force}(\operatorname{thunk}(M))
\longrightarrow^{\mathrm{op}}_i M,
\qquad
\operatorname{return}(V)
\ \operatorname{to}\ x^{*^v_i}:A\ \operatorname{in}\ N
\longrightarrow^{\mathrm{op}}_j
N[x^{*^v_i}:=V],
\tag{CBPV-op}
\]

- Run unfolding

\[
\operatorname{run}_{A,B}(f,a)
\longrightarrow^{\mathrm{op}}_j
\operatorname{runCase}_{A,B}
(f,a,\operatorname{force}(f)@^c a),
\tag{Run-Unfold}
\]

- Run cases

\[
\begin{aligned}
\operatorname{runCase}_{A,B}
(f,a,\operatorname{return}(\operatorname{continue}_{A,B}(a')))
&\longrightarrow^{\mathrm{op}}_j
\operatorname{run}_{A,B}(f,a'),\\
\operatorname{runCase}_{A,B}
(f,a,\operatorname{return}(\operatorname{finish}_{A,B}(b)))
&\longrightarrow^{\mathrm{op}}_j
\operatorname{return}(b).
\end{aligned}
\tag{Run-op}
\]

#### Reflection boundary

\[
\frac{M\longrightarrow^{\mathrm{op}}_iM'}
     {\operatorname{RfTerm}_{\underline B}(M)
      \longrightarrow^{\mathrm{st}}_{*^s_i}
      \operatorname{RfTerm}_{\underline B}(M')}
\tag{Rf-Cong}
\]

#### Type conversion

\[
\equiv^{\mathrm{ty}}_s
\coloneqq
(\longrightarrow^{\mathrm{ty}}_s
 \cup\longleftarrow^{\mathrm{ty}}_s)^*
\]

### Context / judgement

#### Form

- \(\Gamma::=\varnothing\mid\Gamma,x^s:A:s\)
- \(\operatorname{WF}(\Gamma)\)
- \(\Gamma\vdash A:s\)
- \(\Gamma\vdash t:A:s\)
- \(\Gamma\vDash P\)

#### PTS typing

- \((s_1,s_2,s_3)\in\mathcal R\)
- Sort

\[
\frac{
 \operatorname{WF}(\Gamma)
 \qquad(s_0,s_1)\in\mathcal A
}{
 \Gamma\vdash s_0:s_1
},
\tag{Sort}
\]

- Variable

\[
\frac{\operatorname{WF}(\Gamma,x^s:A:s)}
     {\Gamma,x^s:A:s\vdash x^s:A:s},
\tag{Var}
\]

- \(\Pi\)

\[
\frac{
 \Gamma\vdash A:s_1
 \qquad
 \Gamma,x^{s_1}:A:s_1\vdash B:s_2
}{
 \Gamma\vdash\Pi_{(s_1,s_2,s_3)}x^{s_1}:A.B:s_3
},
\tag{Pi}
\]

- \(\lambda\)

\[
\frac{
 \Gamma\vdash\Pi_{(s_1,s_2,s_3)}x^{s_1}:A.B:s_3
 \qquad
 \Gamma,x^{s_1}:A:s_1\vdash t:B:s_2
}{
 \Gamma\vdash
 \lambda_{(s_1,s_2,s_3)}x^{s_1}:A.t:
 \Pi_{(s_1,s_2,s_3)}x^{s_1}:A.B:s_3
},
\tag{Lam}
\]

- Application

\[
\frac{
 \Gamma\vdash f:\Pi_{(s_1,s_2,s_3)}x^{s_1}:A.B:s_3
 \qquad
 \Gamma\vdash u:A:s_1
}{
 \Gamma\vdash f@_{(s_1,s_2,s_3)}u:B[x^{s_1}:=u]:s_2
}
\tag{App}
\]

#### Role bridge

- Type to term

\[
\frac{
 \Gamma\vdash A:s
 \qquad
 s\in\operatorname{dom}(\uparrow)
}{
 \Gamma\vdash\operatorname{asTm}(A):s:\uparrow(s)
},
\tag{AsTm}
\]

- Term to type

\[
\frac{
 \Gamma\vdash t:\downarrow(\kappa):\kappa
 \qquad
 \kappa\in\operatorname{im}(\uparrow)
}{
 \Gamma\vdash\operatorname{asTy}(t):\downarrow(\kappa)
}.
\tag{AsTy}
\]

#### Conversion

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

#### Reflection

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

### Universe level

#### Non-cumulativity

\[
\Gamma\vdash A:*^q_i
\not\Longrightarrow
\Gamma\vdash A:*^q_{i+1},
\qquad
\Gamma\vdash *^q_i:\sq^q_i.
\]

#### Level expression

\[
\ell::=
0
\mid\alpha
\mid\operatorname{succ}(\ell)
\mid\max(\ell,\ell)
\]

#### Program sort

\[
*^v_\ell:\sq^v_\ell,
\qquad
*^c_\ell:\sq^c_\ell
\]

#### Constraint

- Fixed \(q\in\{v,c\}\)
- Constraints: \(\ell_1\) vs. \(\ell_2\) within \(*^q_\ell\)
