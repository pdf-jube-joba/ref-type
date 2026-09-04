# 構文間の写像としての Reflection

`RfType` と `RfTerm` を Set/Prop の raw syntax に含めず、Program 構文から
Set/Prop 構文へのメタレベルの写像として定める。この定式化では、
Reflection の結果に Program 構文が残らない。

このとき、Program term の well-termination は、Program typing が導出済みで
あることを前提として、

\[
\operatorname{RfTerm}_P(p):\operatorname{RfType}(P):\mathsf{Set}
\]

が成り立つこととして定義できる。ここでコロンは写像の値に対する
Set typing であり、`RfTerm` を型付けるための専用規則ではない。

## 体系定義

### 構文定義

Set/Prop と Program の raw syntax は `system.md` のものを用いる。Program datatype
宣言から生成される Set 側の鏡像 \(I^s\) と \(C_i^s\) は Set 構文である。

Reflection 記号は Set term grammar の構成子ではなく、次の構文間写像を
表すメタ記法とする。

\[
\begin{aligned}
\operatorname{RfType}&:\mathsf{ProgramTypeSyntax}
\longrightarrow\mathsf{SetTermSyntax},\\
\operatorname{RfTerm}&:\mathsf{TypedProgramTermSyntax}
\longrightarrow\mathsf{SetTermSyntax}.
\end{aligned}
\]

Program application の raw syntax \(M@^cV\) 自体は domain type \(A\) を保持しない。
従って \(\operatorname{RfTerm}\) は、厳密には Program typing derivation
\(d:\Delta\vdash_Pp:P\) に対する構文的写像 \(\operatorname{RfTerm}(d)\) とする。
\(\operatorname{RfTerm}_P(p)\) はこの写像の略記であり、添字 \(P\) は source
type を表す。Program type の一意性と typing derivation に対する coherence
が得られれば、derivation \(d\) は省略できる。型情報をすべて付けた
elaborated Program syntax を用いる定式化では、その elaborated syntax 上の
写像として同じ定義を与えられる。

#### Type と context の写像

\[
\begin{aligned}
\operatorname{RfType}(X)
&:=X^{\sq^s_0},\\
\operatorname{RfType}(\text{F}A)
&:=\operatorname{RfType}(A),\\
\operatorname{RfType}(\text{U}\underline B)
&:=\operatorname{RfType}(\underline B),\\
\operatorname{RfType}(A\Rightarrow\underline B)
&:=\operatorname{RfType}(A)\to\operatorname{RfType}(\underline B),\\
\operatorname{RfType}(\operatorname{RunStep}(A,B))
&:=\operatorname{RunStep}
(\operatorname{RfType}(A),\operatorname{RfType}(B)),\\
\operatorname{RfType}(I^v(\vec A))
&:=I^s(\operatorname{RfType}(\vec A)).
\end{aligned}
\]

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

ここで source variable から target variable への対応は、各 context に対して
固定した injective な renaming とする。上では sort annotation が異なる同じ
name stem を使った。捕獲が起きる場合は fresh な target name へ
alpha-renaming する。この対応を context、lambda、case branch、substitution で
一貫して使う。

#### Value の写像

\[
\begin{aligned}
\operatorname{RfTerm}_A(x^v)
&:=x^{*^s_0},\\
\operatorname{RfTerm}_{\text{U}\underline B}(\operatorname{thunk}(M))
&:=\operatorname{RfTerm}_{\underline B}(M),\\
\operatorname{RfTerm}_{\operatorname{RunStep}(A,B)}
(\operatorname{continue}_{A,B}(a))
&:=
\operatorname{continue}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}
(\operatorname{RfTerm}_A(a)),\\
\operatorname{RfTerm}_{\operatorname{RunStep}(A,B)}
(\operatorname{finish}_{A,B}(b))
&:=
\operatorname{finish}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}
(\operatorname{RfTerm}_B(b)),\\
\operatorname{RfTerm}_{I^v(\vec A)}
(C_i^v[\vec A](\vec V))
&:=
C_i^s[\operatorname{RfType}(\vec A)]
\left(
\overrightarrow{
\operatorname{RfTerm}_{A_{ij}[\vec X:=\vec A]}(V_j)
}
\right).
\end{aligned}
\]

#### Computation の写像

\(\text{F}\) と \(\text{U}\) は type の写像で消える。それに対応して
\(\operatorname{return}\), \(\operatorname{thunk}\), \(\operatorname{force}\) も写像の結果では
消える。

\[
\begin{aligned}
\operatorname{RfTerm}_{\text{F}A}(\operatorname{return}(V))
&:=\operatorname{RfTerm}_A(V),\\
\operatorname{RfTerm}_{\underline B}(\operatorname{force}(V))
&:=\operatorname{RfTerm}_{\text{U}\underline B}(V),\\
\operatorname{RfTerm}_{A\Rightarrow\underline B}
(\lambda x^v:A.M)
&:=
\lambda x^{*^s_0}:\operatorname{RfType}(A).
\operatorname{RfTerm}_{\underline B}(M),\\
\operatorname{RfTerm}_{\underline B}(M@^cV)
&:=
\operatorname{RfTerm}_{A\Rightarrow\underline B}(M)
@\operatorname{RfTerm}_A(V),\\
\operatorname{RfTerm}_{\underline B}
(M\ \operatorname{to}\ x^v:A\ \operatorname{in}\ N)
&:=
(\lambda x^{*^s_0}:\operatorname{RfType}(A).
\operatorname{RfTerm}_{\underline B}(N))
@\operatorname{RfTerm}_{\text{F}A}(M),\\
\operatorname{RfTerm}_{\underline B}
(\operatorname{let}^v x^v=V\ \operatorname{in}\ N)
&:=
(\lambda x^{*^s_0}:\operatorname{RfType}(A).
\operatorname{RfTerm}_{\underline B}(N))
@\operatorname{RfTerm}_A(V).
\end{aligned}
\]

Program case は鏡像 datatype の Set case へ写す。

\[
\begin{aligned}
&\operatorname{RfTerm}_{\underline B}
\left(
\operatorname{case}^v
(V;\overline{C_i^v(\vec x_i^v)\mapsto M_i})
\right)\\
&\qquad:=
\operatorname{case}^s
\left(
\operatorname{RfTerm}_{I^v(\vec A)}(V);
\overline{
C_i^s(\vec x_i^{*^s_0})
\mapsto\operatorname{RfTerm}_{\underline B}(M_i)
}
\right).
\end{aligned}
\]

Program run と administrative form の \(\operatorname{runCase}\) は Set 側の対応する
構成子へ写す。

\[
\begin{aligned}
&\operatorname{RfTerm}_{\text{F}B}
(\operatorname{run}_{A,B}(f,a))\\
&\qquad:=
\operatorname{run}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}
(\operatorname{RfTerm}_{\text{U}(A\Rightarrow
\text{F}(\operatorname{RunStep}(A,B)))}(f),
\operatorname{RfTerm}_A(a)),\\[4pt]
&\operatorname{RfTerm}_{\text{F}B}
(\operatorname{runCase}_{A,B}(f,a,M))\\
&\qquad:=
\operatorname{runCase}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}
\left(
\operatorname{RfTerm}_{\text{U}(A\Rightarrow
\text{F}(\operatorname{RunStep}(A,B)))}(f),
\operatorname{RfTerm}_A(a),
\operatorname{RfTerm}_{\text{F}(\operatorname{RunStep}(A,B))}(M)
\right).
\end{aligned}
\]

これらの clause は等式によるメタ定義であり、Set reduction の
root rule ではない。例えば \(\operatorname{RfTerm}(\operatorname{return}(V))\)
という Set raw term は存在せず、その表記を展開した結果は
\(\operatorname{RfTerm}_A(V)\) をさらに展開した Set raw term である。

### Reduction 定義

Program reduction \(\Rightarrow_c\) と Set reduction \(\Rightarrow_s\) は `system.md` のものを
用いる。Reflection 固有の reduction relation は生じない。代わりに、
構文間写像が置換と reduction を保つことをメタ定理とする。

#### 置換

\[
\begin{aligned}
&\operatorname{RfTerm}_{P[x^v:=V]}(p[x^v:=V])\\
&\qquad=
\operatorname{RfTerm}_P(p)
[x^{*^s_0}:=\operatorname{RfTerm}_A(V)].
\end{aligned}
\tag{Rf-Substitution}
\]

左辺の type annotation に依存がない現行の Program type では
\(P[x^v:=V]=P\) である。将来 Program type を依存型に拡張した場合も使える
形で記述している。

#### Reduction simulation

\[
p\Rightarrow_c p'
\quad\Longrightarrow\quad
\operatorname{RfTerm}_P(p)
\Rightarrow_s^*
\operatorname{RfTerm}_P(p')
\]

は、\(\operatorname{force}(\operatorname{thunk}(M))\) の step を除いて各 root rule を
直接対応させることで示せる。force-thunk step では写像の両辺が
構文的に同一であるため、\(\Rightarrow_s^*\) は 0 step となる。

例えば Program beta reduction は Rf-Substitution と Set beta reduction により
次のように対応する。

\[
\begin{aligned}
&\operatorname{RfTerm}_{\underline B}
((\lambda x^v:A.M)@^cV)\\
&\quad=
(\lambda x^{*^s_0}:\operatorname{RfType}(A).
\operatorname{RfTerm}_{\underline B}(M))
@\operatorname{RfTerm}_A(V)\\
&\quad\Rightarrow_s
\operatorname{RfTerm}_{\underline B}(M)
[x^{*^s_0}:=\operatorname{RfTerm}_A(V)]\\
&\quad=
\operatorname{RfTerm}_{\underline B}(M[x^v:=V]).
\end{aligned}
\]

Run の一段目も同じ構造を保つ。

\[
\begin{aligned}
&\operatorname{RfTerm}_{\text{F}B}(\operatorname{run}_{A,B}(f,a))\\
&\quad\Rightarrow_s
\operatorname{runCase}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}
\left(
\operatorname{RfTerm}(f),
\operatorname{RfTerm}(a),
\operatorname{RfTerm}(f)@\operatorname{RfTerm}(a)
\right)\\
&\quad=
\operatorname{RfTerm}_{\text{F}B}
\left(
\operatorname{runCase}_{A,B}
(f,a,\operatorname{force}(f)@^c a)
\right).
\end{aligned}
\]

最後の等式では \(\text{U}\), \(\text{F}\), \(\operatorname{force}\) の写像が消える
ことを使っている。

### Judgement 定義

Type reflection の well-formedness は Program type formation から得る。

\[
\begin{aligned}
\Delta\vdash A\ \mathsf{vtype}
&\Longrightarrow
\operatorname{RfCtx}(\Delta)\vdash
\operatorname{RfType}(A):*^s_0,\\
\Delta\vdash\underline B\ \mathsf{ctype}
&\Longrightarrow
\operatorname{RfCtx}(\Delta)\vdash
\operatorname{RfType}(\underline B):*^s_0.
\end{aligned}
\tag{Rf-Type-Formation}
\]

同じ Program typing judgement に対する二つの derivation \(d,d'\) について、
次の coherence を要求する。

\[
\operatorname{RfTerm}(d)
=_{\alpha}
\operatorname{RfTerm}(d').
\tag{Rf-Coherence}
\]

Program type の一意性と各 typing rule の generation から示す。Conversion を
Program typing に追加する場合は、\(=_{\alpha}\) の代わりに target の
definitional equality を使う。

Well-termination judgement は次の略記として定める。

\[
\begin{aligned}
\Delta\Vdash_vV:A
\quad:\Longleftrightarrow\quad
&\Delta\vdash_vV:A\\
&\land
\operatorname{RfCtx}(\Delta)\vdash
\operatorname{RfTerm}_A(V):\operatorname{RfType}(A):*^s_0,\\[4pt]
\Delta\Vdash_cM:\underline B
\quad:\Longleftrightarrow\quad
&\Delta\vdash_cM:\underline B\\
&\land
\operatorname{RfCtx}(\Delta)\vdash
\operatorname{RfTerm}_{\underline B}(M):
\operatorname{RfType}(\underline B):*^s_0.
\end{aligned}
\tag{WT by translation}
\]

Program typing derivation \(d:\Delta\vdash_Pp:P\) に対してのみ well-termination を
問う約束にすれば、これはユーザーの提案どおり次の一行にできる。

\[
\Delta\Vdash p:P
\quad:\Longleftrightarrow\quad
\operatorname{RfCtx}(\Delta)\vdash
\operatorname{RfTerm}_P(p):\operatorname{RfType}(P):*^s_0.
\tag{WT, typed source}
\]

Program typing を前提に繰り込まない場合は、`WT by translation` の連言が
必要である。\(\text{F}\) と \(\text{U}\) を消す写像は source の type error を
消去することがあり、写像の Set typing だけから元の Program typing は
一般に回収できない。

#### Run の条件

Run に必要な条件は、独立の Reflection derivability rule ではなく、
写像の Set typing を反転すると現れる。

\[
\begin{gathered}
\Delta\vdash_v
f:\text{U}(A\Rightarrow\text{F}(\operatorname{RunStep}(A,B))),
\qquad
\Delta\vdash_va:A,\\
\operatorname{RfCtx}(\Delta)\vDash
\operatorname{Acc}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}
\left(
\operatorname{RfTerm}(f),
\operatorname{RfTerm}(a)
\right)
\end{gathered}
\]

が成り立つとき、写像

\[
\operatorname{run}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}
(\operatorname{RfTerm}(f),\operatorname{RfTerm}(a))
\]

が \(\operatorname{RfType}(B)\) の Set term として型付けされる。従って
\(\operatorname{run}_{A,B}(f,a)\) の well-termination も `WT by translation` の一例に
なる。

\(\operatorname{runCase}_{A,B}(f,a,M)\) では、Set 側の typing を反転すると
現在の state の accessibility に加えて次を得る。

\[
\operatorname{RfCtx}(\Delta)\vDash
\operatorname{RfTerm}(f)@\operatorname{RfTerm}(a)
=\operatorname{RfTerm}(M).
\]

この equality と Acc descent が Program の run reduction に対する
well-termination の subject reduction を与える。

## この定式化で簡単になる点

`reflection1.md` の \(\vdash_{\mathrm{Rf}}\) と Set typing の二重化は解消される。
well-termination の derivation は、source Program typing derivation と、完全に展開された
写像に対する Set typing derivation の組である。

さらに、Reflection の object-level syntax が消えるため、次の構成も消える。

- Rf-Cong, Rf-C-App, Rf-U-App の reflection reduction
- glued form と Set representative の間の reification
- Rf-Ctor を先に簡約するか Rf-App を先に簡約するかという
  critical pair
- \(\operatorname{RfTerm}\) の typing rule と、その generation による
  Reflection derivability の回収

Constructor は最初から Set constructor へ写り、lambda は最初から Set lambda へ
写る。そのため、写像内に Program syntax を payload として保持する
必要がない。

## Well-termination と呼ぶためのメタ定理

`WT by translation` 自体は構文と typing による簡潔な定義である。それが
operational な停止を表すことは次の定理に分離する。

### Reflection の subject reduction

\[
\Delta\Vdash_cM:\underline B,
\qquad M\Rightarrow_cM'
\quad\Longrightarrow\quad
\Delta\Vdash_cM':\underline B.
\]

Program subject reduction、Rf-Substitution、reduction simulation、Set subject reduction から
導く。Run-Continue の場合は Set 側の Acc descent を使う。

### 閉じた returner の停止

\[
\emptyset\Vdash_cM:\text{F}A
\quad\Longrightarrow\quad
\exists V.\
M\Rightarrow_c^*\operatorname{return}(V)
\ \land\
\emptyset\Vdash_vV:A.
\]

Set 側の strong normalization と reduction simulation のみを使う場合、
force-thunk step の写像が 0 step になる点に注意が必要である。
Program step の無限列が、Set 側の有限な reduction 列に無条件に写ることは
できない。正の Set step 数と、force-thunk のように写像で消える
administrative redex の大きさを組にした辞書式測度か、Program 側の
logical-relations proof を用いる。

### 結果の対応

\[
M\Rightarrow_c^*\operatorname{return}(V)
\quad\Longrightarrow\quad
\operatorname{RfTerm}_{\text{F}A}(M)
\Rightarrow_s^*\operatorname{RfTerm}_A(V).
\]

鏡像 datatype については、この性質と Set 側の canonicity を合わせて、
Program constructor と Set constructor の結果が一致することを示す。

## Set 項を Program の写像へ戻す境界

構文間写像は Program から Set への一方向である。この向きだけなら、
\(\operatorname{RfTerm}\) は完全にメタレベルに移せる。一方、写像で得た Set
関数は普通の Set lambda であるため、任意の Set 項に適用できる。

例えば Program term

\[
\lambda x^v:A.\operatorname{run}_{A,B}(f,x^v)
\]

の写像は

\[
\lambda x^{*^s_0}:\operatorname{RfType}(A).
\operatorname{run}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}
(\operatorname{RfTerm}(f),x^{*^s_0})
\]

である。これを \(u:\operatorname{RfType}(A)\) という任意の Set term に適用すると、
beta reduction 後の run の初期 state は \(u\) になる。\(u\) に \(\operatorname{Take}\)
などの Set 固有の構成が含まれていることもある。

従って、次の四つを同時に無条件で満たすことはできない。

1. \(\operatorname{RfTerm}\) を Set syntax に入れない。
2. Program function を通常の Set function type と Set lambda へ写す。
3. Set の function elimination を無制限に使う。
4. Reflection から生じた run の \(f\) と \(a\) を常に Program 項の写像に
   限定する。

一方向の停止性定理の対象を、構文間写像が直接生成した
Set term に限定するなら、追加の構文や judgement は必要ない。
Reduction simulation と閉じた returner の停止定理はこの範囲で述べる。
任意の Set context がその写像を利用した後の canonicity は、それらの
定理からは従わない。

Set typing の段階でも第 4 条件を強制するには、通常の Set function
type と application 以外の境界が必要になる。その場合は `reflection1.md`
の abstract boundary を保つ方が直接的であり、この節の単純な
構文間写像にはできない。

## 結論

Program typing を別に確認するという条件付きで、提案の簡素化は成り立つ。
基本定義は次でよい。

\[
\boxed{
\Delta\Vdash p:P
\quad:\Longleftrightarrow\quad
\Delta\vdash_Pp:P
\ \land\
\operatorname{RfCtx}(\Delta)\vdash
\operatorname{RfTerm}_P(p):\operatorname{RfType}(P):*^s_0
}
\]

この定義では \(\operatorname{RfType}\) と \(\operatorname{RfTerm}\) はどちらもメタレベルの
構文間写像であり、右辺に現れる実際の Set term に Reflection 構成子は
残らない。Run の Acc 条件は写像の Set typing に含まれる。

Program-origin の引数だけを run に渡すことを Set typing そのもので強制するなら、
`reflection1.md` のような abstract boundary が必要である。この厳密な
制限を維持する場合、提案の簡素化だけでは足りない。
