## 体系定義

現行体系では、Set/Prop の PTS と CBPV の Program 部分が別の
syntactic category と judgement で定義されている。ここでは raw term を
一つの構文に統合し、value type と computation type を PTS の sort で
分類する。

統合後も CBPV の phase は保存する。すなわち、value と computation の
違いは結論の sort に現れ、computation の実行は weak call-by-value の
operational reduction によってだけ進む。

この案の主要な judgement は次の三項 judgement である。

\[
\Gamma\vdash e:T:s.
\]

例えば、

\[
\Gamma\vdash V:A:*^v_i
\]

は \(V\) が level \(i\) の value type \(A\) の value であることを表し、

\[
\Gamma\vdash M:\underline B:*^c_i
\]

は \(M\) が level \(i\) の computation type \(\underline B\) を持つ
computation であることを表す。

### sort

Set/Prop 側の sort、axiom、product relation は現行体系のものを使う。
Program 用の sort として、次を追加する。

\[
\mathcal S_t
=
\{*^v_i,*^c_i,\sq^t_i\mid i\in\mathbb N\}.
\]

\[
\mathcal A_t
=
\{(*^v_i,\sq^t_i),(*^c_i,\sq^t_i)\mid i\in\mathbb N\}.
\]

\(*^v_i\) は level \(i\) の value type を分類し、\(*^c_i\) は
level \(i\) の computation type を分類する。\(\sq^t_i\) はこの二つの
proper sort に共通する kind である。共通の kind に属することは、
value type と computation type を conversion で同一視することを意味しない。

Program 用の product relation は、value-to-computation product と
predicative type polymorphism を区別して、次のように置く。

\[
\mathcal R_{\mathrm{fun}}
=
\left\{
(*^v_i,*^c_j,*^c_{\max(i,j)})
\mathrel{\middle|}i,j\in\mathbb N
\right\}.
\]

この relation から、value \(x:A\) を引数に取り、computation type
\(\underline B\) を結果とする product を形成する。

\[
\frac{
 \Gamma\vdash A:*^v_i
 \qquad
 \Gamma,x:A:*^v_i\vdash\underline B:*^c_j
}{
 \Gamma\vdash
 \Pi x:A.\underline B
 :*^c_{\max(i,j)}
}.
\]

product の raw syntax は binder を持つが、現時点の Program type former は
Program value を index に取らない。また、value を domain として kind を codomain に
返す product relation も入れない。このため、sorting derivation に関する帰納法で

\[
\Gamma,x:A:*^v_i\vdash\underline B:*^c_j
\quad\Longrightarrow\quad
x\notin\operatorname{FV}(\underline B)
\tag{Program-Type-Nondependency}
\]

を示す。したがって well-typed な product は非依存であり、CBPV function type の
記法を次で定義する。

\[
A\Rightarrow\underline B
\;\coloneqq\;
\Pi x:A.\underline B
\qquad
(x\notin\operatorname{FV}(\underline B)).
\]

type polymorphism には、別に次の relation を使う。

\[
\mathcal R_{\mathrm{poly}}
=
\left\{
(\sq^t_i,*^c_j,*^c_{\max(i+1,j)})
\mathrel{\middle|}i,j\in\mathbb N
\right\}.
\]

この relation は value type と computation type のどちらにも量化できるが、
形成される polymorphic type 自体は常に computation type とする。例えば、

\[
\frac{
 \Gamma,X:*^v_i:\sq^t_i
 \vdash\underline B:*^c_j
}{
 \Gamma\vdash
 \Pi X:*^v_i.\underline B
 :*^c_{\max(i+1,j)}
}
\]

を得る。domain を \(*^c_i\) にすれば computation type 自体に量化できる。
domain の実際の式が \(*^v_i\) か \(*^c_i\) かを保持するため、両者が同じ
\(\sq^t_i\) に属していても量化対象の phase は区別される。

したがって Program 部分で追加する product relation は

\[
\mathcal R_t
=
\mathcal R_{\mathrm{fun}}
\cup
\mathcal R_{\mathrm{poly}}
\]

である。将来、Program value で index される type former または
value から kind への product relation を追加すると
Program-Type-Nondependency は成り立たなくなる。その拡張は dependent CBPV として
別に扱う。

### raw syntax

sort、Set/Prop term、Program type、value、computation はすべて一つの
raw term \(e\) の constructor とする。

\[
\begin{aligned}
e::={}&s
\mid x
\mid \Pi x:T.T
\mid \lambda^\tau x:T.e
\mid e@^\tau e\\
&\mid F e
\mid Ue
\mid\operatorname{RunStep}(e,e)\\
&\mid\operatorname{return}(e)
\mid\operatorname{thunk}(e)
\mid\operatorname{force}(e)\\
&\mid e\ \operatorname{to}\ x:T\ \operatorname{in}\ e
\mid\operatorname{let}^v x=e\ \operatorname{in}\ e\\
&\mid\operatorname{continue}_{e,e}(e)
\mid\operatorname{finish}_{e,e}(e)\\
&\mid\operatorname{run}_{e,e}(e,e)
\mid\operatorname{runCase}_{e,e}(e,e,e)\\
&\mid\operatorname{RfType}(e)
\mid\operatorname{RfTerm}_e(e)
\mid\cdots.
\end{aligned}
\]

\(\tau\) は core 上の mode tag であり、

\[
\tau::=\mathsf{ty}\mid c
\]

とする。\(\mathsf{ty}\) は PTS と type polymorphism の static な
lambda/application、\(c\) は CBPV computation の lambda/application を表す。
両者は reduction strategy が異なるため core syntax では区別する。
surface syntax では typing からこの tag を elaborate できる。

type abstraction/application の大文字の記法は新しい raw constructor ではなく、
次の surface notation とする。

\[
\Lambda X:*^r_i.e
\;\coloneqq\;
\lambda^{\mathsf{ty}}X:*^r_i.e,
\qquad
e[P]
\;\coloneqq\;
e@^{\mathsf{ty}}P.
\]

期待される product type から binder annotation を回復できる場合に限り、
surface syntax で \(\Lambda X.e\) と省略してよい。また、
\(A\Rightarrow\underline B\) も raw constructor ではなく、上で定義した
非依存 product の surface notation である。

\(V\) と \(M\) は別の raw grammar を表す記号ではなく、それぞれ
value sort と computation sort に属する well-typed raw term を表す
metavariable とする。したがって、phase separation は次の inversion として
得られる形にする。

\[
\Gamma\vdash e:A:*^v_i
\quad\Longrightarrow\quad
e\text{ は value phase に分類される}.
\]

\[
\Gamma\vdash e:\underline B:*^c_i
\quad\Longrightarrow\quad
e\text{ は computation phase に分類される}.
\]

### context と judgement

context entry も三項の形に統合する。

\[
\Gamma::=\emptyset\mid\Gamma,x:T:s.
\]

Program 側では主に次の entry が現れる。

\[
X:*^v_i:\sq^t_i,
\qquad
\underline X:*^c_i:\sq^t_i,
\qquad
x:A:*^v_i.
\]

始めの二つは value/computation type variable であり、最後の一つは
Program value variable である。CBPV の term context には value variable を置き、
computation \(M:\underline B:*^c_i\) は term variable として context に追加しない。

sorting と typing は次の形を持つ。

\[
\Gamma\vdash T:s,
\qquad
\Gamma\vdash e:T:s.
\]

現行の Program formation judgement は次の sorting に対応する。

\[
\begin{aligned}
\Gamma\vdash A\ \mathsf{vtype}_i
&\quad\Longleftrightarrow\quad
\Gamma\vdash A:*^v_i,\\
\Gamma\vdash\underline B\ \mathsf{ctype}_i
&\quad\Longleftrightarrow\quad
\Gamma\vdash\underline B:*^c_i.
\end{aligned}
\]

現行の value/computation typing judgement は次の typing に対応する。

\[
\begin{aligned}
\Gamma\vdash_vV:A
&\quad\Longleftrightarrow\quad
\Gamma\vdash V:A:*^v_i,\\
\Gamma\vdash_cM:\underline B
&\quad\Longleftrightarrow\quad
\Gamma\vdash M:\underline B:*^c_i.
\end{aligned}
\]

\(i\) は \(A\) または \(\underline B\) の principal level である。これにより、
judgement 自体から reflection 先の Set level を回復できる。

### Program type formation

\(F\) と \(U\) は principal level を保存する。

\[
\frac{\Gamma\vdash A:*^v_i}
     {\Gamma\vdash F A:*^c_i}
\tag{F-Form}
\]

\[
\frac{\Gamma\vdash\underline B:*^c_i}
     {\Gamma\vdash U\underline B:*^v_i}
\tag{U-Form}
\]

CBPV の function type は \(\mathcal R_{\mathrm{fun}}\) による product として形成する。

\[
\frac{
 \Gamma\vdash A:*^v_i
 \qquad
 \Gamma,x:A:*^v_i\vdash\underline B:*^c_j
}{
 \Gamma\vdash
 \Pi x:A.\underline B:*^c_{\max(i,j)}
}
\tag{Pi-C-Form}
\]

Program-Type-Nondependency により \(x\notin\operatorname{FV}(\underline B)\) なので、
この product を \(A\Rightarrow\underline B\) と書く。

\[
\frac{
 \Gamma\vdash A:*^v_i
 \qquad
 \Gamma\vdash B:*^v_j
}{
 \Gamma\vdash
 \operatorname{RunStep}(A,B):*^v_{\max(i,j)}
}
\tag{RunStep-Form}
\]

この level 割り当てにより、\(F/U\) の reflection は同じ Set level の中で
reduction でき、computation product は domain と codomain の最大 level を持つ。

### Program typing

主要な CBPV typing rule は、sort と level を結論に含む形で次のように
なる。

\[
\frac{\Gamma\vdash V:A:*^v_i}
     {\Gamma\vdash
       \operatorname{return}(V):F A:*^c_i}
\tag{Return}
\]

\[
\frac{\Gamma\vdash M:\underline B:*^c_i}
     {\Gamma\vdash
       \operatorname{thunk}(M):U\underline B:*^v_i}
\tag{Thunk}
\]

\[
\frac{\Gamma\vdash V:U\underline B:*^v_i}
     {\Gamma\vdash
       \operatorname{force}(V):\underline B:*^c_i}
\tag{Force}
\]

\[
\frac{
 \Gamma\vdash A:*^v_i
 \qquad
 \Gamma,x:A:*^v_i\vdash M:\underline B:*^c_j
}{
 \Gamma\vdash
 \lambda^c x:A.M:
 A\Rightarrow\underline B:*^c_{\max(i,j)}
}
\tag{Fun-I}
\]

\[
\frac{
 \Gamma\vdash M:A\Rightarrow\underline B:*^c_k
 \qquad
 \Gamma\vdash V:A:*^v_i
}{
 \Gamma\vdash M@^cV:\underline B:*^c_j
}
\tag{Fun-E}
\]

ここで \(k=\max(i,j)\) である。product formation は PTS relation で与えるが、
導入・除去と operational reduction は
\(\lambda^c/@^c\) による CBPV の規則として保つ。sequence、value let、run、
runCase にも同じように principal level を付ける。

### polymorphic term

Program type に対する導入と除去は static な type abstraction/application とする。
\(r\in\{v,c\}\)、\(k=\max(i+1,j)\) とする。polymorphic type とその項は
computation phase に属する。

\[
\frac{
 \Gamma,X:*^r_i:\sq^t_i
 \vdash M:\underline B:*^c_j
}{
 \Gamma\vdash
 \Lambda X:*^r_i.M:
 (\Pi X:*^r_i.\underline B):*^c_k
}
\tag{Poly-I}
\]

\[
\frac{
 \Gamma\vdash
 M:(\Pi X:*^r_i.\underline B):*^c_k
 \qquad
 \Gamma\vdash P:*^r_i
}{
 \Gamma\vdash
 M[P]:\underline B[X:=P]:*^c_j
}
\tag{Poly-E}
\]

type abstraction/application は Program effect を実行しない。その beta rule は
static reduction に属する。

\[
(\Lambda X:*^r_i.M)[P]
\longrightarrow_{\mathsf{ty}}
M[X:=P].
\tag{Poly-Beta}
\]

polymorphic computation を value として保持するときは、value-level の
polymorphic product を追加せず、\(U\) を用いる。

\[
\frac{
 \Gamma\vdash
 \Lambda X:*^r_i.M:
 (\Pi X:*^r_i.\underline B):*^c_k
}{
 \Gamma\vdash
 \operatorname{thunk}(\Lambda X:*^r_i.M):
 U(\Pi X:*^r_i.\underline B):*^v_k
}.
\]

### reduction

raw syntax 全体に対する一つの無型 reduction は使わず、少なくとも
次の三つを区別する。

\[
\begin{array}{ll}
\longrightarrow_{\mathsf{ty}}
&\text{PTS と type polymorphism の static reduction},\\
\longrightarrow_c
&\text{CBPV computation の operational reduction},\\
\longrightarrow_s
&\text{Set/Prop と reflection の reduction}.
\end{array}
\]

\(\longrightarrow_c\) の evaluation context は現行体系と同じく、

\[
\begin{aligned}
E::={}&[\,]
\mid E@^cV\\
&\mid E\ \operatorname{to}\ x:A\ \operatorname{in}\ M\\
&\mid\operatorname{runCase}_{A,B}(V,V,E)
\end{aligned}
\]

とする。主要な root rule は次である。

\[
\operatorname{force}(\operatorname{thunk}(M))
\longrightarrow_cM.
\tag{Force-Thunk}
\]

\[
(\lambda^c x:A.M)@^cV
\longrightarrow_cM[x:=V].
\tag{Beta-c}
\]

\[
\operatorname{return}(V)
\ \operatorname{to}\ x:A\ \operatorname{in}\ N
\longrightarrow_cN[x:=V].
\tag{Sequence-Return}
\]

\[
\operatorname{let}^v x=V\ \operatorname{in}\ N
\longrightarrow_cN[x:=V].
\tag{Value-Let-Beta}
\]

run と runCase の reduction も \(\longrightarrow_c\) に属する。value、thunk の内側、
return の内側、lambda body では \(\longrightarrow_c\) を進めない。

### conversion

conversion は raw syntax 上の無型な convertibility ではなく、sort と
level で index された definitional equality を使う。

\[
\Gamma\vdash A\equiv B:*^q_i
\qquad(q\in\{v,c\}).
\]

Program の conversion rule は次の形である。

\[
\frac{
 \Gamma\vdash e:A:*^q_i
 \qquad
 \Gamma\vdash B:*^q_i
 \qquad
 \Gamma\vdash A\equiv B:*^q_i
}{
 \Gamma\vdash e:B:*^q_i
}.
\tag{Conversion}
\]

この規則は同じ proper sort と同じ principal level の型の間だけで使う。
特に、

\[
\Gamma\vdash A:*^v_i,
\qquad
\Gamma\vdash\underline B:*^c_j
\]

から \(A\equiv\underline B\) が生じることはない。

computation の operational reduction

\[
M\longrightarrow_cM'
\]

は Program typing の conversion に直接使わない。この reduction は
subject reduction

\[
\Gamma\vdash M:\underline B:*^c_i
\quad\Longrightarrow\quad
\Gamma\vdash M':\underline B:*^c_i
\]

の対象とする。Program type の conversion に使うのは、type-level の
static reduction から生成した typed definitional equality である。

### reflection

reflection は Program の principal level を Set 側に保存する。

\[
\frac{\Gamma\vdash A:*^v_i}
     {\Gamma\vdash\operatorname{RfType}(A):*^s_i}
\tag{Rf-VType}
\]

\[
\frac{\Gamma\vdash\underline B:*^c_i}
     {\Gamma\vdash\operatorname{RfType}(\underline B):*^s_i}
\tag{Rf-CType}
\]

\[
\frac{\Gamma\vdash V:A:*^v_i}
     {\Gamma\vdash
      \operatorname{RfTerm}_A(V):
      \operatorname{RfType}(A):*^s_i}
\tag{Rf-Value}
\]

\[
\frac{\Gamma\vdash M:\underline B:*^c_i}
     {\Gamma\vdash
      \operatorname{RfTerm}_{\underline B}(M):
      \operatorname{RfType}(\underline B):*^s_i}
\tag{Rf-Compute}
\]

\(F/U\) の level-preserving formation により、次の reduction は同じ Set sort の
中で型を保存する。

\[
\operatorname{RfType}(F A)
\longrightarrow_s
\operatorname{RfType}(A).
\tag{Rf-F}
\]

\[
\operatorname{RfType}(U\underline B)
\longrightarrow_s
\operatorname{RfType}(\underline B).
\tag{Rf-U}
\]

\[
\operatorname{RfType}(A\Rightarrow\underline B)
\longrightarrow_s
\operatorname{RfType}(A)
\to
\operatorname{RfType}(\underline B).
\tag{Rf-Arrow}
\]

\(A:*^v_i\) かつ \(\underline B:*^c_j\) なら、\(\operatorname{Rf-Arrow}\) の両辺は
\(*^s_{\max(i,j)}\) に属する。Program-Type-Nondependency により source product の
binder は codomain に現れないので、Compute binder を Set binder に移す変数変換は
必要ない。term reflection においても return と thunk の境界を消去する。

\[
\operatorname{RfTerm}_{F A}(\operatorname{return}(V))
\longrightarrow_s
\operatorname{RfTerm}_A(V).
\tag{Rf-Return}
\]

\[
\operatorname{RfTerm}_{U\underline B}(\operatorname{thunk}(M))
\longrightarrow_s
\operatorname{RfTerm}_{\underline B}(M).
\tag{Rf-Thunk}
\]

Program evaluation を Set 側から観測する唯一の境界として、次の規則を
保持する。

\[
\frac{M\longrightarrow_cM'}{
 \operatorname{RfTerm}_{\underline B}(M)
 \longrightarrow_s
 \operatorname{RfTerm}_{\underline B}(M')
}.
\tag{Rf-Cong}
\]

したがって、Program の operational reduction が Set/Prop の conversion に
影響する範囲は \(\operatorname{RfTerm}\) の内側に局所化される。

### polymorphism の reflection

polymorphic Program type を構造的に reflection する場合、次の形の
reduction が必要になる。

\[
\operatorname{RfType}(\Pi X:*^r_i.\underline B)
\longrightarrow_s
\Pi X:*^r_i.\operatorname{RfType}(\underline B).
\tag{Rf-Poly}
\]

\(\underline B:*^c_j\) としたとき、左辺の Set level は
\(k=\max(i+1,j)\) である。右辺を同じ level の Set type として
形成するため、次の cross-sort relation を候補とする。

\[
\mathcal R_{\mathrm{Rf}}
=
\left\{
(\sq^t_i,*^s_j,*^s_{\max(i+1,j)})
\mathrel{\middle|}
i,j\in\mathbb N
\right\}.
\]

これは右辺の Set product が Program type の code 全体を domain とすることを
表す。その body は Program type variable \(X\) を
\(\operatorname{RfType}(X)\) の形で使える。model では \(*^v_i\) と \(*^c_i\) を
type code の集合として解釈し、\(\operatorname{RfType}\) をその decoding として
解釈する必要がある。

term reflection にも対応する static rule を置く。

\[
\operatorname{RfTerm}_{\Pi X:*^r_i.\underline B}
  (\Lambda X:*^r_i.M)
\longrightarrow_s
\lambda^{\mathsf{ty}}X:*^r_i.
\operatorname{RfTerm}_{\underline B}(M).
\tag{Rf-Poly-I}
\]

### inductive type と run

Program 側の inductive type に principal level を持たせる。

\[
\Gamma\vdash I^v(\vec A):*^v_k
\]

なら、対応する Set 側の鏡像は

\[
\Gamma\vdash
I^s(\operatorname{RfType}(\vec A)):*^s_k
\]

とする。constructor field と type parameter もそれぞれの principal level で
reflection する。これにより、現行の \(*^s_0\) に固定した鏡像を
universe-polymorphic な宣言に拡張できる。

state type \(A:*^v_i\) と result type \(B:*^v_j\) に対し、

\[
m=\max(i,j)
\]

と置く。このとき、

\[
\operatorname{RunStep}(A,B):*^v_m
\]

であり、

\[
\operatorname{StepFun}(A,B)
=
U\left(A\Rightarrow F(\operatorname{RunStep}(A,B))\right)
:*^v_m
\]

である。continue と finish は次の level を持つ。

\[
\frac{
 \Gamma\vdash a:A:*^v_i
 \qquad
 \Gamma\vdash B:*^v_j
}
     {\Gamma\vdash
      \operatorname{continue}_{A,B}(a):
      \operatorname{RunStep}(A,B):*^v_m}.
\tag{Continue}
\]

\[
\frac{
 \Gamma\vdash A:*^v_i
 \qquad
 \Gamma\vdash b:B:*^v_j
}
     {\Gamma\vdash
      \operatorname{finish}_{A,B}(b):
      \operatorname{RunStep}(A,B):*^v_m}.
\tag{Finish}
\]

accessibility の state は

\[
a:\operatorname{RfType}(A):*^s_i
\]

とし、Acc-Intro の fresh variable も

\[
b:\operatorname{RfType}(A):*^s_i
\]

とする。run と runCase の typing は次のようになる。

\[
\frac{
 \Gamma\vdash f:\operatorname{StepFun}(A,B):*^v_m
 \qquad
 \Gamma\vdash a:A:*^v_i
 \qquad
 \Gamma\vDash\operatorname{Terminates}_{A,B}(f,a)
}{
 \Gamma\vdash
 \operatorname{run}_{A,B}(f,a):F B:*^c_j
}.
\tag{Run}
\]

\[
\frac{
 \begin{array}{c}
 \Gamma\vdash f:\operatorname{StepFun}(A,B):*^v_m
 \qquad
 \Gamma\vdash a:A:*^v_i\\
 \Gamma\vdash
 M:F(\operatorname{RunStep}(A,B)):*^c_m\\
 \Gamma\vDash\operatorname{Terminates}_{A,B}(f,a)
 \qquad
 \Gamma\vDash\operatorname{RunInv}_{A,B}(f,a,M)
 \end{array}
}{
 \Gamma\vdash
 \operatorname{runCase}_{A,B}(f,a,M):F B:*^c_j
}.
\tag{RunCase}
\]

run と runCase の operational rule は level に依存せず、現行の CBPV
reduction をそのまま使える。

## universe level の polymorphism

\(i\in\mathbb N\) を直接書く体系は universe hierarchy を与える。同じ定義を
複数の level に instantiate する universe polymorphism のためには、level を
syntax として扱う。

\[
\ell::=0\mid\alpha\mid\operatorname{succ}(\ell)
\mid\max(\ell,\ell).
\]

sort と規則の \(i,j\) を level expression \(\ell_1,\ell_2\) に一般化する。
宣言の elaboration では level metavariable を生成し、formation と application から
得られる等式・不等式制約を解く。宣言の未解決 level variable を
generalize することで、例えば

\[
\operatorname{id}.{\alpha}
:
\Pi X:*^v_\alpha.
X\Rightarrow F X
\]

のような universe-polymorphic な宣言を得る。

principal level は \(\max\) と \(\operatorname{succ}\) からなる最小の level expression と
する。この principal level を三項 judgement に常に表示し、reflection も
同じ level expression を Set 側に使う。

## non-cumulative universe

Program の universe hierarchy には cumulativity を入れない。型形成と typing は
常に principal level を結論に持ち、

\[
\Gamma\vdash e:A:*^q_i
\quad\Longrightarrow\quad
\Gamma\vdash e:A:*^q_j
\qquad(i<j)
\]

という subsumption は認めない。universe-polymorphic な宣言の再利用は level
variable の instantiation によって行い、型を上位 universe に持ち上げる規則とは
分離する。reflection は judgement に表示された principal level をそのまま Set 側に
保存する。Set/Prop 側に既存の cumulativity がある場合でも、それを Program sort に
自動的に拡張しない。

## 必要な性質

この統合によって、従来 raw grammar の分離から得ていた性質を typing の
theorem として示す必要がある。

- sort separation:
  well-typed な型が value sort と computation sort の両方に属しない。
- principal level uniqueness:
  type の principal level は level constraint の同値を除いて一意である。
- type uniqueness:
  同じ raw term の型は、同じ sort の typed definitional equality を除いて一意である。
- conversion preservation:
  definitional equality は proper sort と principal level を保存する。
- Program subject reduction:
  \(M\longrightarrow_cM'\) は computation type と principal level を保存する。
- reflection preservation:
  Program の typing と reduction は、同じ level の Set typing と reflection
  reduction によって保存される。
- closed Program normalization:
  空 context、または仮定を満たす妥当な closing substitution に
  相対化して、well-typed な閉じた computation は value を return する。

## 変更の段階

実際の体系と実装は次の順序で変更できる。

1. Program type formation に principal level を追加し、
   \(\mathsf{vtype}_i\) と \(\mathsf{ctype}_i\) にする。
2. typing judgement を \(\Gamma\vdash e:T:*^q_i\) の形に統合する。
3. \(F\)、\(U\)、function、\(\operatorname{RunStep}\) に principal level を付ける。
4. reflection、Acc、Program inductive の \(*^s_0\) を principal Set level に
   一般化する。
5. raw AST を一つに統合し、static reduction、operational reduction、
   reflection reduction を typed relation として分離する。
6. \((*^v_i,*^c_j,*^c_{\max(i,j)})\) による computation product と、
   static type abstraction/application を追加する。
7. level metavariable、constraint solving、generalization を追加する。

## 検討事項

- \(\sq^t_i\) 自身をより上の kind に属させるか。その場合は
  \((\sq^t_i,\sq^t_{i+1})\) と higher-kind 用の product relation を追加する。
- \(\mathcal R_{\mathrm{Rf}}\) によって Program type code 上の Set product 全体を認めるか、
  polymorphic reflection 専用の formation rule に限定するか。
- polymorphic computation の static beta を definitional equality としてどの程度
  normalize するか。
- indexed Program type を将来追加する場合の dependent CBPV formation、context
  reindexing、reflection。
- Program inductive の principal level と positivity を Set 側の鏡像に保存する
  declaration rule。
- common kind \(\sq^t_i\) とその type-code/decoding 解釈を含む model。
