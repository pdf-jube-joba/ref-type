## 体系定義

Type sort \(*^t\) の内部に value type と computation type の二つの
syntactic category を置き、\(F\) と \(U\) を明示する。
Set と Prop の PTS 部分は現行体系を保つ。

この案の中心は次の対応である。

\[
\begin{array}{ccl}
A &:& \text{value type},\\
\underline B &:& \text{computation type},\\
F A &:& \text{\(A\) の value を返す computation type},\\
U\underline B &:& \text{\(\underline B\) の computation を suspend した value type}.
\end{array}
\]

value type と computation type は別 sort ではない。どちらも Type sort
\(*^t\) の中にあり、formation judgement によって区別する。

### type

value type と computation type の構文を

\[
\begin{aligned}
A
::={}&X
\mid I^t(\vec A)
\mid U\underline B
\mid\operatorname{RunStep}(A,B),\\
\underline B
::={}&F A
\mid A\Rightarrow\underline B
\end{aligned}
\]

とする。\(I^t\) は Type 側の通常の datatype である。
\(A\Rightarrow\underline B\) は value \(A\) を受け取る computation
function type である。

Type 側の関数を PTS の積から直接作ると \(F/U\) を迂回できるため、
product relation の

\[
(*^t,*^t,*^t)
\]

は外す。Type 側の function は専用の
\(A\Rightarrow\underline B\) で形成する。

主要な type formation は次である。

\[
\frac{\Gamma\vdash A\ \mathsf{vtype}}
     {\Gamma\vdash F A\ \mathsf{ctype}}
\tag{F-Form}
\]

\[
\frac{\Gamma\vdash\underline B\ \mathsf{ctype}}
     {\Gamma\vdash U\underline B\ \mathsf{vtype}}
\tag{U-Form}
\]

\[
\frac{
 \Gamma\vdash A\ \mathsf{vtype}
 \qquad
 \Gamma\vdash\underline B\ \mathsf{ctype}
}{
 \Gamma\vdash A\Rightarrow\underline B\ \mathsf{ctype}
}
\tag{Arrow-Form}
\]

\[
\frac{
 \Gamma\vdash A\ \mathsf{vtype}
 \qquad
 \Gamma\vdash B\ \mathsf{vtype}
}{
 \Gamma\vdash\operatorname{RunStep}(A,B)\ \mathsf{vtype}
}
\tag{RunStep-Form}
\]

ここで
\(\Gamma\vdash A\ \mathsf{vtype}\) と
\(\Gamma\vdash\underline B\ \mathsf{ctype}\) は、いずれも
\(*^t\) に属する type formation judgement である。

### context と judgement

Type 側の term context に置く変数は value variable だけとする。

\[
\Gamma::=\varnothing
\mid\Gamma,x:A
\mid\text{Set/Prop の従来の entry}.
\]

主要な term judgement は

\[
\begin{array}{ll}
\Gamma\vdash_v V:A
& \text{\(V\) は value},\\
\Gamma\vdash_c M:\underline B
& \text{\(M\) は computation},\\
\Gamma\vdash_s t:T:*^s_i
& \text{\(t\) は Set 項},\\
\Gamma\vdash_p P
& \text{\(P\) は proposition},\\
\Gamma\vDash P
& \text{\(P\) は証明可能}
\end{array}
\]

とする。Type 側の variable が Set/Prop の式に現れる場合、その occurrence
は \(\operatorname{RfTerm}\) の payload の中に限られる。

以後、\(\vdash_c\) と \(\longrightarrow_c\) の添字 \(c\) は
旧 sort 名の Compute ではなく、それぞれ computation judgement と
computation reduction を表す。sort 自体の名前と記号は Type と
\(*^t\) で統一する。

### value と computation

value の構文を

\[
\begin{aligned}
V,W::={}&x
\mid C(\vec V)
\mid\operatorname{thunk}(M)\\
&\mid\operatorname{continue}_{A,B}(V)
\mid\operatorname{finish}_{A,B}(V)
\end{aligned}
\]

とする。computation の構文を

\[
\begin{aligned}
M,N::={}&
\operatorname{return}(V)
\mid\operatorname{force}(V)
\mid\lambda x:A.M
\mid M\,V\\
&\mid M\ \operatorname{to}\ x:A\ \operatorname{in}\ N\\
&\mid\operatorname{let}^v x=V\ \operatorname{in}\ N\\
&\mid\operatorname{case}
\left(V;\overline{C_i(\vec x_i)\mapsto M_i}\right)\\
&\mid\operatorname{run}_{A,B}(V,W)\\
&\mid\operatorname{runCase}_{A,B}(V,W,M)
\end{aligned}
\]

とする。

\(\operatorname{thunk}(M)\) は computation を実行せずに value として
保持する。\(\operatorname{force}(V)\) は suspended computation の実行を
開始する。\(\lambda x:A.M\) は computation function type の canonical
form であり、再利用可能な関数 value は
\(\operatorname{thunk}(\lambda x:A.M)\) と書く。

### \(F\) と \(U\) の typing

\[
\frac{\Gamma\vdash_v V:A}
     {\Gamma\vdash_c\operatorname{return}(V):F A}
\tag{Return}
\]

\[
\frac{\Gamma\vdash_c M:\underline B}
     {\Gamma\vdash_v\operatorname{thunk}(M):U\underline B}
\tag{Thunk}
\]

\[
\frac{\Gamma\vdash_v V:U\underline B}
     {\Gamma\vdash_c\operatorname{force}(V):\underline B}
\tag{Force}
\]

\[
\frac{\Gamma,x:A\vdash_cM:\underline B}
     {\Gamma\vdash_c
       \lambda x:A.M:A\Rightarrow\underline B}
\tag{Fun-I}
\]

\[
\frac{
 \Gamma\vdash_cM:A\Rightarrow\underline B
 \qquad
 \Gamma\vdash_vV:A
}{
 \Gamma\vdash_cM\,V:\underline B
}
\tag{Fun-E}
\]

### 二種類の let

CBPV では、value の束縛と computation の sequencing は異なる。
本稿では前者を
\(\operatorname{let}^v\)、後者を
\(\operatorname{to}\) と書く。

\[
\frac{
 \Gamma\vdash_vV:A
 \qquad
 \Gamma,x:A\vdash_cN:\underline B
}{
 \Gamma\vdash_c
 \operatorname{let}^v x=V\ \operatorname{in}\ N:
 \underline B
}
\tag{Value-Let}
\]

\[
\frac{
 \Gamma\vdash_cM:F A
 \qquad
 \Gamma,x:A\vdash_cN:\underline B
}{
 \Gamma\vdash_c
 M\ \operatorname{to}\ x:A\ \operatorname{in}\ N:
 \underline B
}
\tag{Sequence}
\]

\(\operatorname{let}^v\) の右辺はすでに value なので、実行を待たずに
置換できる。一方、\(\operatorname{to}\) は左側の computation が
\(\operatorname{return}(V)\) になるまで右側へ進まない。

文献によっては

\[
\operatorname{let}\ x=V\ \operatorname{in}\ N
\qquad\text{と}\qquad
\operatorname{let}\ x\leftarrow M\ \operatorname{in}\ N
\]

のように、両方を let と書く。後者が \(F\) の bind である。
pair の分解などに使う
\(\operatorname{let}\ (x,y)=V\ \operatorname{in}\ N\) も value elimination
だが、実行を sequence する bind とは別である。

### reduction

computation の evaluation context を

\[
\begin{aligned}
E::={}&[\,]
\mid E\,V
\mid E\ \operatorname{to}\ x:A\ \operatorname{in}\ N\\
&\mid\operatorname{runCase}_{A,B}(f,a,E)
\end{aligned}
\]

とする。root rule は

\[
\operatorname{force}(\operatorname{thunk}(M))
\longrightarrow_c M
\tag{Force-Thunk}
\]

\[
(\lambda x:A.M)\,V
\longrightarrow_c M[x:=V]
\tag{Beta}
\]

\[
\operatorname{return}(V)
\ \operatorname{to}\ x:A\ \operatorname{in}\ N
\longrightarrow_c
N[x:=V]
\tag{Sequence-Return}
\]

\[
\operatorname{let}^v x=V\ \operatorname{in}\ N
\longrightarrow_c
N[x:=V]
\tag{Value-Let-Beta}
\]

\[
\operatorname{case}
\left(
C_i(\vec V);
\overline{C_j(\vec x_j)\mapsto M_j}
\right)
\longrightarrow_c
M_i[\vec x_i:=\vec V]
\tag{Case}
\]

とする。さらに

\[
\frac{M\longrightarrow_cM'}
     {E[M]\longrightarrow_cE[M']}
\tag{Context}
\]

を加える。

\(\operatorname{thunk}\)、\(\operatorname{return}\)、lambda body、
constructor argument、未選択の branch の内部では reduction は進まない。
したがって computation の実行順序は evaluation context から決まる。

### 一般再帰

state type \(A\) と result type \(B\) は value type とする。
step function と state は

\[
f:U\left(A\Rightarrow
F(\operatorname{RunStep}(A,B))\right),
\qquad
a:A
\]

という value である。

run は

\[
\operatorname{run}_{A,B}(f,a):F B
\]

という computation とする。administrative term の
\(\operatorname{runCase}\) も computation である。

\[
\operatorname{run}_{A,B}(f,a)
\longrightarrow_c
\operatorname{runCase}_{A,B}
\left(f,a,(\operatorname{force}(f))\,a\right)
\tag{Run-Enter}
\]

\[
\operatorname{runCase}_{A,B}
\left(
 f,a,
 \operatorname{return}
 \left(\operatorname{continue}_{A,B}(a')\right)
\right)
\longrightarrow_c
\operatorname{run}_{A,B}(f,a')
\tag{Run-Continue}
\]

\[
\operatorname{runCase}_{A,B}
\left(
 f,a,
 \operatorname{return}
 \left(\operatorname{finish}_{A,B}(b)\right)
\right)
\longrightarrow_c
\operatorname{return}(b).
\tag{Run-Finish}
\]

\(\operatorname{runCase}\) の第三引数だけが evaluation context に入るため、
一回分の step computation が \(\operatorname{RunStep}(A,B)\) の value
を返してから次の状態へ移る。

step function の本体は別の computation を
\(\operatorname{to}\) で sequence できる。したがって、すでに停止性を
証明した別の run を呼び出す場合にも、run-free という制約は要らない。

### value と computation を消去する reflection

Set 側の境界には、type category によらない
\(\operatorname{RfType}\) と \(\operatorname{RfTerm}\) を置く。

\[
\frac{\Gamma\vdash A\ \mathsf{vtype}}
     {\Gamma\vdash_s\operatorname{RfType}(A):*^s_0}
\tag{Rf-VType}
\]

\[
\frac{\Gamma\vdash\underline B\ \mathsf{ctype}}
     {\Gamma\vdash_s\operatorname{RfType}(\underline B):*^s_0}
\tag{Rf-CType}
\]

\[
\frac{\Gamma\vdash_vV:A}
     {\Gamma\vdash_s
      \operatorname{RfTerm}_A(V):
      \operatorname{RfType}(A):*^s_0}
\tag{Rf-Value}
\]

\[
\frac{\Gamma\vdash_cM:\underline B}
     {\Gamma\vdash_s
      \operatorname{RfTerm}_{\underline B}(M):
      \operatorname{RfType}(\underline B):*^s_0}
\tag{Rf-Compute}
\]

両方の source category に同じ \(\operatorname{RfTerm}\) を使うため、
Set term の型から value と computation の違いを観測できない。

type reflection は \(F/U\) を消去する。

\[
\operatorname{RfType}(F A)
\longrightarrow
\operatorname{RfType}(A)
\tag{Rf-F}
\]

\[
\operatorname{RfType}(U\underline B)
\longrightarrow
\operatorname{RfType}(\underline B)
\tag{Rf-U}
\]

\[
\operatorname{RfType}(A\Rightarrow\underline B)
\longrightarrow
\operatorname{RfType}(A)
\to
\operatorname{RfType}(\underline B).
\tag{Rf-Arrow}
\]

term reflection も return と thunk の境界を消去する。

\[
\operatorname{RfTerm}_{F A}(\operatorname{return}(V))
\longrightarrow
\operatorname{RfTerm}_A(V)
\tag{Rf-Return}
\]

\[
\operatorname{RfTerm}_{U\underline B}(\operatorname{thunk}(M))
\longrightarrow
\operatorname{RfTerm}_{\underline B}(M)
\tag{Rf-Thunk}
\]

\[
\frac{M\longrightarrow_cM'}
     {
      \operatorname{RfTerm}_{\underline B}(M)
      \longrightarrow
      \operatorname{RfTerm}_{\underline B}(M')
     }
\tag{Rf-Cong}
\]

reflected function の application は二つの形を持つ。

\[
\begin{aligned}
&
\operatorname{RfTerm}_{U(A\Rightarrow\underline B)}(f)
@
\operatorname{RfTerm}_{A}(a)\\
&\qquad\longrightarrow
\operatorname{RfTerm}_{\underline B}
\left((\operatorname{force}(f))\,a\right)
\end{aligned}
\tag{Rf-U-App}
\]

\[
\begin{aligned}
&
\operatorname{RfTerm}_{A\Rightarrow\underline B}(M)
@
\operatorname{RfTerm}_{A}(a)\\
&\qquad\longrightarrow
\operatorname{RfTerm}_{\underline B}(M\,a).
\end{aligned}
\tag{Rf-C-App}
\]

ここで \(f,a\) は value、\(M\) は function computation である。
\(\operatorname{Rf-U-App}\) は open な thunk variable にも適用できる。

\(\operatorname{Rf-Thunk}\) と \(\operatorname{Rf-U-App}\) が同時に
適用できる peak は join する。例えば \(f=\operatorname{thunk}(M)\) なら、
一方は

\[
\operatorname{RfTerm}_{\underline B}
\left(
(\operatorname{force}(\operatorname{thunk}(M)))\,a
\right)
\longrightarrow^*
\operatorname{RfTerm}_{\underline B}(M\,a)
\]

へ進み、他方は先に \(\operatorname{Rf-Thunk}\) を使ってから
\(\operatorname{Rf-C-App}\) により同じ項へ進む。

通常の Type 側 datatype については

\[
\operatorname{RfType}(I^t(\vec A))
\longrightarrow
I^s(\operatorname{RfType}(\vec A))
\]

および value constructor の structural reflection を生成する。
\(\operatorname{RunStep}(A,B)\) は実行制御用の glued carrier として扱う。
その value は \(\operatorname{RfTerm}\) の payload 内で equality に使われる。

Set 側で計算を表す primitive は \(\operatorname{RfTerm}\) 一つである。
run、return、force、thunk、continue、finish はその payload の
Type 側 syntax であり、それぞれに対応する Set constructor は生じない。

### accessibility と run の typing

補助関数を

\[
\begin{aligned}
\operatorname{continueFun}_{A,B}
:={}&
\operatorname{thunk}
\left(
\lambda z:A.
\operatorname{return}
\left(\operatorname{continue}_{A,B}(z)\right)
\right),\\
\operatorname{continueFun}_{A,B}
:{}&
U\left(
A\Rightarrow F(\operatorname{RunStep}(A,B))
\right)
\end{aligned}
\]

とする。

Set 上の一ステップ関係を

\[
\begin{aligned}
\operatorname{Next}_{A,B}(f,b,a)
:={}&
\operatorname{RfTerm}_{U(A\Rightarrow F(\operatorname{RunStep}(A,B)))}(f)
@a\\
&=
\operatorname{RfTerm}_{U(A\Rightarrow F(\operatorname{RunStep}(A,B)))}
(\operatorname{continueFun}_{A,B})
@b
\end{aligned}
\]

とする。\(a,b:\operatorname{RfType}(A)\) は Set 項である。
\(\operatorname{Acc}_{A,B}(f,a)\) は、この \(\operatorname{Next}\) に関する
accessibility とする。

\[
\frac{
 \begin{array}{c}
 \Gamma\vdash_v
 f:U(A\Rightarrow F(\operatorname{RunStep}(A,B)))\\
 \Gamma\vdash_s
 a:\operatorname{RfType}(A):*^s_0
 \end{array}
}{
 \Gamma\vdash_p\operatorname{Acc}_{A,B}(f,a)
}
\tag{Acc-Form}
\]

\[
\frac{
 \Gamma,b:\operatorname{RfType}(A)
 \vDash
 \operatorname{Next}_{A,B}(f,b,a)
 \to
 \operatorname{Acc}_{A,B}(f,b)
}{
 \Gamma\vDash\operatorname{Acc}_{A,B}(f,a)
}
\tag{Acc-Intro}
\]

ここで \(b\) は conclusion の context に現れない fresh な Set 変数
とする。

\[
\frac{
 \Gamma\vDash\operatorname{Acc}_{A,B}(f,a)
 \qquad
 \Gamma\vDash\operatorname{Next}_{A,B}(f,b,a)
}{
 \Gamma\vDash\operatorname{Acc}_{A,B}(f,b)
}
\tag{Acc-Descent}
\]

\[
\operatorname{Terminates}_{A,B}(f,a)
:=
\operatorname{Acc}_{A,B}
\left(f,\operatorname{RfTerm}_A(a)\right).
\]

\(\operatorname{runCase}\) の invariant は

\[
\begin{aligned}
\operatorname{RunInv}_{A,B}(f,a,M)
:={}&
\operatorname{RfTerm}_{F(\operatorname{RunStep}(A,B))}
\left((\operatorname{force}(f))\,a\right)\\
&=
\operatorname{RfTerm}_{F(\operatorname{RunStep}(A,B))}(M)
\end{aligned}
\]

とする。

run と runCase の typing は

\[
\frac{
 \begin{array}{c}
 \Gamma\vdash_v
 f:U(A\Rightarrow F(\operatorname{RunStep}(A,B)))
 \qquad
 \Gamma\vdash_v a:A\\
 \Gamma\vDash\operatorname{Terminates}_{A,B}(f,a)
 \end{array}
}{
 \Gamma\vdash_c\operatorname{run}_{A,B}(f,a):F B
}
\tag{Run}
\]

\[
\frac{
 \begin{array}{c}
 \Gamma\vdash_v
 f:U(A\Rightarrow F(\operatorname{RunStep}(A,B)))
 \qquad
 \Gamma\vdash_v a:A\\
 \Gamma\vdash_cM:F(\operatorname{RunStep}(A,B))\\
 \Gamma\vDash\operatorname{Terminates}_{A,B}(f,a)
 \qquad
 \Gamma\vDash\operatorname{RunInv}_{A,B}(f,a,M)
 \end{array}
}{
 \Gamma\vdash_c
 \operatorname{runCase}_{A,B}(f,a,M):F B
}
\tag{RunCase}
\]

とする。

\(\operatorname{Run-Enter}\) では invariant は reflexivity で得られる。
\(\operatorname{Run-Continue}\) では invariant と
\(\operatorname{Rf-Return}\) から、現在の step が
\(\operatorname{continue}(a')\) を返したことを表す
\(\operatorname{Next}\) の equality を得る。Acc descent により
\(\operatorname{Terminates}_{A,B}(f,a')\) が従うため、reduct の run
も型付けできる。

## run は value にできるか

CBPV の構文上、run を value category に置くこと自体は難しくない。
computation を thunk すればよい。

\[
\frac{
\Gamma\vdash_c\operatorname{run}_{A,B}(f,a):F B
}{
\Gamma\vdash_v
\operatorname{thunk}(\operatorname{run}_{A,B}(f,a)):
U(F B)
}.
\]

略記として

\[
\operatorname{runVal}_{A,B}(f,a)
:=
\operatorname{thunk}(\operatorname{run}_{A,B}(f,a))
\]

を導入してもよい。ただし、これは結果 \(b:B\) ではなく、
実行前の suspended computation \(U(F B)\) である。

primitive な run 自体を \(B\) の value として扱うと、次のどちらかが
必要になる。

1. value の内部で run reduction を進める。
2. \(B\) の value が内部に未実行の computation を隠し持つ。

前者は value/computation の evaluation phase を崩し、後者は
\(U(F B)\) が担う区別を \(B\) に埋め込むことになる。
したがって、run は \(F B\) の computation とし、suspend したい箇所だけ
\(\operatorname{thunk}\) を使う方が CBPV の構造に合う。

## computation reflection の効果

value だけを structural に reflection する場合、

\[
\operatorname{RfTerm}_{U(F B)}
\left(
\operatorname{thunk}(\operatorname{run}(f,a))
\right)
\]

は suspended program の表現に留まり、それだけでは
\(\operatorname{RfType}(B)\) の結果にならない。

今回のように computation も glued reflection の source にすると、
\(\operatorname{Rf-Thunk}\) によって

\[
\begin{aligned}
&
\operatorname{RfTerm}_{U(F B)}
\left(
\operatorname{thunk}(\operatorname{run}(f,a))
\right)\\
&\qquad\longrightarrow
\operatorname{RfTerm}_{F B}(\operatorname{run}(f,a))
\end{aligned}
\]

となり、その payload 内で run を実行できる。直接

\[
\operatorname{RfTerm}_{F B}(\operatorname{run}(f,a))
:
\operatorname{RfType}(B)
\]

と書いてもよい。

この reflection は syntax tree の単純な structural copy ではなく、
total な computation の評価結果を Set の carrier に glue する操作である。
そのため value と computation の両方を許すと gcd の結果の取り出しは
単純になるが、次が proof obligation になる。

- reflected computation の preservation
- computation reduction と reflection reduction の confluence
- termination assumption が妥当な context での normalization
- \(\operatorname{Rf-Thunk}\) と function application の peak の joinability

一般再帰には Acc proof が要求されるので、空 context では
停止する run だけが Set の canonical value まで進むことを目標にできる。
I/O、state、exception、nondeterminism を加える場合は、計算結果を一つの
Set value に消去する代わりに effect の handler または関係的な解釈が必要になる。

## gcd の結果を Set へ持ってくる

\(\mathbb N^t\) を Type 側の value datatype、
\(\mathbb N^s\) を対応する Set datatype とし、

\[
\operatorname{RfType}(\mathbb N^t)
\longrightarrow
\mathbb N^s
\]

とする。Euclid 法の state を

\[
\operatorname{State}
:=
\mathbb N^t\times\mathbb N^t
\]

とし、step function を

\[
\operatorname{gcdStep}
:
U\left(
\operatorname{State}
\Rightarrow
F(\operatorname{RunStep}(\operatorname{State},\mathbb N^t))
\right)
\]

とする。Type 側の gcd computation は

\[
\operatorname{gcdC}(m,n)
:=
\operatorname{run}
\left(
\operatorname{gcdStep},
\operatorname{pair}(m,n)
\right)
:
F\mathbb N^t
\]

である。

その Set 側の結果は

\[
\operatorname{RfTerm}_{F\mathbb N^t}
\left(\operatorname{gcdC}(m,n)\right)
:
\mathbb N^s
\]

と書ける。例えば computation reduction が

\[
\operatorname{gcdC}(\overline{18},\overline{12})
\longrightarrow_c^*
\operatorname{return}(\overline 6)
\]

なら、

\[
\begin{aligned}
&
\operatorname{RfTerm}_{F\mathbb N^t}
\left(
\operatorname{gcdC}(\overline{18},\overline{12})
\right)\\
&\qquad\longrightarrow^*
\operatorname{RfTerm}_{F\mathbb N^t}
\left(\operatorname{return}(\overline 6)\right)\\
&\qquad\longrightarrow
\operatorname{RfTerm}_{\mathbb N^t}(\overline 6)
\longrightarrow^*
\overline 6^{\,s}.
\end{aligned}
\]

gcd 自体を reflected Set function として使う場合は

\[
\begin{aligned}
\operatorname{gcdFun}
:={}&
\operatorname{thunk}
\left(
\lambda p:\operatorname{State}.
\operatorname{run}(\operatorname{gcdStep},p)
\right),\\
\operatorname{gcdFun}
:{}&
U\left(\operatorname{State}\Rightarrow F\mathbb N^t\right).
\end{aligned}
\]

このとき

\[
\operatorname{RfTerm}_{U(\operatorname{State}\Rightarrow F\mathbb N^t)}
(\operatorname{gcdFun})
:
\operatorname{RfType}(\operatorname{State})
\to\mathbb N^s
\]

である。reflected state に適用すれば
\(\operatorname{Rf-U-App}\) により gcd computation の reflection
へ進む。

\[
\begin{aligned}
&
\operatorname{RfTerm}_{U(\operatorname{State}\Rightarrow F\mathbb N^t)}
(\operatorname{gcdFun})
@
\operatorname{RfTerm}_{\operatorname{State}}
(\operatorname{pair}(m,n))\\
&\qquad\longrightarrow^*
\operatorname{RfTerm}_{F\mathbb N^t}
\left(\operatorname{gcdC}(m,n)\right).
\end{aligned}
\]

したがって、run を \(B\) の value に変えることは gcd の reflection に
必要ない。run は \(F B\) の computation のまま、\(F\) を消去する
computation reflection を境界に置けばよい。

## 再帰型との組み合わせ

CBPV の value/computation distinction と再帰型は組み合わせられる。
ただし、CBPV を採用するだけで任意の再帰型が安全になるわけではない。

通常の有限な inductive datatype は value type に置く。例えば

\[
\operatorname{List}(A)
\simeq
\mu X.\,1+A\times X
\]

では、nil と cons は value constructor、case や structural recursor は
computation になる。この形は CBPV とよく合う。

再帰型を raw syntax に直接加える場合は、equi-recursive type より
iso-recursive type

\[
\mu X.A,
\qquad
\operatorname{fold}:A[X:=\mu X.A]\to\mu X.A,
\qquad
\operatorname{unfold}:\mu X.A\to A[X:=\mu X.A]
\]

の方が conversion と reduction の境界を明示しやすい。
現在の datatype 宣言の方針を保つなら、strictly-positive な named
inductive datatype として生成するのがさらに扱いやすい。

強正規化を保つには、再帰変数の出現を strictly positive に制限する必要が
ある。polarity は \(F\) と \(U\) を通過して保存され、
\(A\Rightarrow\underline B\) の domain で反転し、codomain で保存される。

例えば

\[
D
:=
\mu X.\,
U(X\Rightarrow F A)
\]

は \(X\) が function domain に現れる negative recursive type である。
この型を許すと fix を primitive に持たなくても自己適用を作れる。

\[
\begin{aligned}
\delta
&:=
\lambda x:D.\,
\left(\operatorname{force}(\operatorname{unfold}(x))\right)x
:
D\Rightarrow F A,\\
d
&:=
\operatorname{fold}(\operatorname{thunk}(\delta))
:
D.
\end{aligned}
\]

すると

\[
\begin{aligned}
\left(\operatorname{force}(\operatorname{unfold}(d))\right)d
&\longrightarrow_c^*
\delta\,d\\
&\longrightarrow_c
\left(\operatorname{force}(\operatorname{unfold}(d))\right)d
\end{aligned}
\]

となる。したがって、fix がないことから停止性を得るには、
再帰型を有限で strictly-positive な inductive datatype に制限するか、
guarded recursion や sized type のような別の条件が必要である。

Set 側への datatype reflection は、Type 側の named datatype
\(I^t\) と Set 側の named datatype \(I^s\) を対応させ、
constructor を一層ずつ reflection する既存の方法を使える。
\(F/U\) は datatype の constructor ではなく phase の境界なので、
先に定義した \(\operatorname{Rf-F}\) と \(\operatorname{Rf-U}\) で消去する。

## run を含む停止性

次の fragment を考える。

- Type 側は simply typed CBPV である。
- datatype は有限で strictly-positive である。
- structural recursor は構造的に小さい引数へだけ再帰する。
- fix、negative recursive type、一般の effect はない。
- 一般再帰を導入する primitive は run と runCase だけである。

この fragment の run/runCase を除く部分には、通常の logical relation
または reducibility による強正規化を期待できる。

run に要求する

\[
\operatorname{Terminates}_{A,B}(f,a)
=
\operatorname{Acc}_{A,B}
\left(f,\operatorname{RfTerm}_A(a)\right)
\]

が実際の一ステップ遷移と一致していれば、run も accessibility induction
で停止する。証明の形は次のようになる。

1. \((\operatorname{force}(f))a\) を評価する。
2. closed な \(F(\operatorname{RunStep}(A,B))\) の canonicity により、
   結果は
   \(\operatorname{return}(\operatorname{continue}(a'))\) または
   \(\operatorname{return}(\operatorname{finish}(b))\) になる。
3. finish の場合は \(\operatorname{return}(b)\) で終了する。
4. continue の場合は \(\operatorname{RunInv}\) と reflection reduction
   から \(\operatorname{Next}_{A,B}(f,a',a)\) を得る。
5. Acc descent で \(a'\) の accessibility を得て、元の Acc proof の
   strict subtree に対する帰納法を使う。

step function の内部に別の run がある場合、その run 自身の typing
derivation にも termination premise がある。base fragment の
reducibility と accessibility induction を組み合わせれば、
一回分の step computation が停止することと、外側の状態遷移列が有限で
あることを同時に示せる見込みがある。

したがって、次の形の定理が目標になる。

\[
\begin{aligned}
&\varnothing\vdash_c M:F A\\
&\qquad\Longrightarrow
\exists V.\,
\varnothing\vdash_vV:A
\land
M\longrightarrow_c^*\operatorname{return}(V).
\end{aligned}
\]

これは現時点では定義から自動的に得られる定理ではない。
少なくとも次の補題が必要になる。

- run を除く fragment の strong normalization
- closed computation の canonicity
- \(\operatorname{RunInv}\) の reduction による保存
- runtime の continue step と \(\operatorname{Next}\) を結ぶ bridge lemma
- Acc-Descent の soundness
- nested run を含む reducibility
- reflection と run reduction の confluence

また、open context に偽の Acc assumption を置けば、停止しない run を
型付けできる可能性がある。停止定理は空 context、またはすべての
assumption が意味論的に妥当な closing substitution に相対化する必要が
ある。Prop と Acc の model soundness まで含めれば、質問の fragment は
停止すると考えてよい。

## reflection と評価順序

\(M:F A\) を Set 側へ持ってくる場合、

\[
\operatorname{RfTerm}_{F A}(M)
:
\operatorname{RfType}(A)
\]

と書ける。\(\operatorname{Rf-Cong}\) が模倣するのは
\(\longrightarrow_c\) の一段だけであり、その
\(\longrightarrow_c\) は先に定義した evaluation context で制御される。
したがって payload 内の evaluation は CBPV で指定した順序のまま進む。

\[
\begin{aligned}
M
&\longrightarrow_c M_1
\longrightarrow_c\cdots
\longrightarrow_c\operatorname{return}(V),\\
\operatorname{RfTerm}_{F A}(M)
&\longrightarrow
\operatorname{RfTerm}_{F A}(M_1)
\longrightarrow\cdots\\
&\longrightarrow
\operatorname{RfTerm}_{F A}(\operatorname{return}(V))
\longrightarrow
\operatorname{RfTerm}_A(V).
\end{aligned}
\]

最後の一段には \(\operatorname{Rf-Return}\) が必要である。
\(\operatorname{Rf-Cong}\) だけでは
\(\operatorname{return}(V)\) と reflected value の境界を消去できない。
通常の datatype の \(V\) なら、その後に constructor reflection が
Set constructor を露出する。

\(\operatorname{Rf-Thunk}\) は少し異なる役割を持つ。
Type 側だけで
\(\operatorname{thunk}(M)\) を扱う間は \(M\) を評価しないが、

\[
\operatorname{RfTerm}_{U\underline B}(\operatorname{thunk}(M))
\longrightarrow
\operatorname{RfTerm}_{\underline B}(M)
\]

によって reflection 境界を越えた時点で suspension を消去する。
その後の \(M\) は \(\operatorname{Rf-Cong}\) により CBPV の順序で評価される。
これは Set 側で \(U\underline B\) を suspended code として観測せず、
computation の結果と同じ carrier として扱うという設計判断である。

\(\operatorname{Rf-U-App}\) と \(\operatorname{Rf-C-App}\) も、
function application を新しい reflected computation payload に戻すだけで、
payload 内の評価順序は変更しない。

一つの payload の中では CBPV の評価順序が保たれる。一方、Set 項に
独立な \(\operatorname{RfTerm}\) が複数あれば、Set reduction の
compatible closure によってそれらの簡約順は interleave しうる。
この fragment は pure で決定的なので、confluence が示せれば最終値は
その interleaving に依存しない。

したがって、\(F A\) の computation について
「CBPV の順序で \(\operatorname{return}(V)\) まで評価され、それから
\(V\) が Set 側へ現れる」という理解で合っている。
ただし thunk は reflection 自体が明示的に force する設計であり、
term reflection の規則には
\(\operatorname{Rf-Return}\)、二つの reflected application、
\(\operatorname{Rf-Cong}\) も必要である。

## CBPV1 からの変更点

| 項目 | CBPV1 | CBPV2 |
| --- | --- | --- |
| computation type | judgement に暗黙化 | \(F A\) として明示 |
| suspended computation | function value に暗黙化 | \(U\underline B\) として明示 |
| function value | \(A\Rightarrow B\) | \(U(A\Rightarrow F B)\) |
| function execution | \(f@^ca\) | \((\operatorname{force}(f))\,a\) |
| value binding | substitution に含める | \(\operatorname{let}^v\) |
| computation sequencing | \(\operatorname{bind}\) | \(M\operatorname{to}x\operatorname{in}N\) |
| run | \(B\) を返す computation judgement | computation type \(F B\) |
| reflection | phase を一つの型へ glue | \(F/U\) も消去して同じ Set carrier へ glue |

この構成では、CBPV の value/computation distinction は Type 側で
\(F/U\)、thunk/force、二種類の let によって明示される。
Set 境界では \(\operatorname{RfType}\) と
\(\operatorname{RfTerm}\) が \(F/U\) を消去するため、Set 側にはその
phase distinction が残らない。
