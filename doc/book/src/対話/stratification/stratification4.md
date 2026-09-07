## 体系定義

[system.md](../../system.md) の Set/Prop と Program を、領域・level ごとの
term/type/kind 構文へ移す。Program には型抽象・型適用を加える。
以下を移行先の体系 \(\mathcal S_{\mathrm{str}}\) とする。

### 1. Sort と構文の分類

#### Sort と axiom

\[
\begin{aligned}
\mathcal B_{sp}&=\{*^s_i\mid i\in\mathbb N\}\cup\{*^p\},\\
\mathcal B_{pr}&=\{*^v_i,*^c_i\mid i\in\mathbb N\},\\
\mathcal B&=\mathcal B_{sp}\cup\mathcal B_{pr},\\
\mathcal S_{sp}&=\mathcal B_{sp}\cup\kappa(\mathcal B_{sp}),\\
\kappa(*^s_i)&=\square^s_i,&
\kappa(*^p)&=\square^p,&
\kappa(*^q_i)&=\square^q_i\quad(q\in\{v,c\}),\\
\mathcal S&=\mathcal B\cup\kappa(\mathcal B),&
\mathcal A&=\{(b,\kappa(b))\mid b\in\mathcal B\}.
\end{aligned}
\]

#### 三つの構文 family

\(b\in\mathcal B\) ごとに、互いに異なる三つの構文を相互帰納的に生成する。

| 構文 | 記号 | typing での役割 |
| --- | --- | --- |
| term | \(t\in\mathsf{Tm}_b\) | \(H\vdash t:A\)、\(H\vdash A:b\) |
| type constructor | \(A\in\mathsf{Ty}_b\) | \(H\vdash A:K\)、\(H\vdash K:\kappa(b)\) |
| kind | \(K\in\mathsf{Kd}_b\) | \(H\vdash K:\kappa(b)\) |

ここで type は型演算子も含む。実際に term の型として使えるのは
\(H\vdash A:b\) を持つ type constructor である。
\(b\) 自身は \(\mathsf{Kd}_b\) の定数であり、
\(\kappa(b)\) は kind formation の右辺に置く sort 記号である。

\[
b\in\mathsf{Kd}_b,
\qquad x_b\in\mathsf{Tm}_b,
\qquad X_b\in\mathsf{Ty}_b.
\]

Set/Prop の変数と Program の変数は別の名前空間を持つ。
Program の \(\mathsf{Tm}_{*^v_i}\) を value、
\(\mathsf{Tm}_{*^c_i}\) を computation と呼び、\(V,M\) で表す。
\(\mathsf{Ty}_{*^v_i}\)、\(\mathsf{Ty}_{*^c_i}\) はそれぞれ value/computation
type constructor、\(\mathsf{Kd}_{*^v_i}\)、\(\mathsf{Kd}_{*^c_i}\) はその kind である。

#### Judgement 用の family の略記

規則をまとめるため、次の略記を使う。

\[
\begin{array}{c|cc}
\sigma&\mathsf E_\sigma&\mathsf C_\sigma\\\hline
b&\mathsf{Tm}_b&\mathsf{Ty}_b\\
\kappa(b)&\mathsf{Ty}_b&\mathsf{Kd}_b
\end{array}
\]

\(\mathsf E,\mathsf C\) は上の三構文を参照するメタレベルの略記である。
例えば、型引数 \(A\in\mathsf{Ty}_b\) は
\(\mathsf E_{\kappa(b)}\) の引数として直接使える。
型演算子の引数位置と、term の型位置は同じ \(\mathsf{Ty}_b\) を参照する。

### 2. Product signature

#### Set の product rule

Set の異なる level は、次の \(\max\) 規則で組み合わせる。

\[
\begin{aligned}
\mathcal R_s=\bigcup_{i,j\in\mathbb N}\{&
(*^s_i,*^s_j,*^s_{\max(i,j)}),\\
&(*^s_i,\square^s_j,\square^s_{\max(i,j)}),\\
&(\square^s_i,\square^s_j,\square^s_{\max(i,j)}),\\
&(\square^s_i,*^s_j,*^s_{\max(i+1,j)})\}.
\end{aligned}
\]

#### Prop と領域間の product rule

Prop と Set/Prop 間の規則は次とする。

\[
\begin{aligned}
\mathcal R_{sp}={}&\mathcal R_s\\
&\cup\{(*^p,*^p,*^p),(\square^p,*^p,*^p),
               (\square^p,\square^p,\square^p)\}\\
&\cup\bigcup_i\{(\sigma,\tau,\tau)\mid
  \sigma\in\{*^s_i,\square^s_i\},\
  \tau\in\{*^p,\square^p\}\}.
\end{aligned}
\]

#### Program の product rule

Program は value から computation への関数、型についての多相性、
型演算子を持つ。\(q,r\in\{v,c\}\) として、

\[
\begin{aligned}
\mathcal R_{pr}=\bigcup_{i,j}\{&
(*^v_i,*^c_j,*^c_{\max(i,j)})\}\\
\cup\bigcup_{q,i,j}\{&
(\square^q_i,*^c_j,*^c_{\max(i+1,j)})\}\\
\cup\bigcup_{q,r,i,j}\{&
(\square^q_i,\square^r_j,\square^r_{\max(i,j)})\}.
\end{aligned}
\]

最後の行によって、例えば value type を computation type に写す型演算子を
抽象・適用できる。Program type/kind の自由変数は Program type variable
だけからなる。Program の value 引数に関する関数型は非依存である。

#### Level

level は non-cumulative な自然数の構文添字であり、各規則は表示された level で適用する。
level の繰上げは上の product rule に従う。level polymorphic な宣言は、
この規則群を level パラメータでメタレベルに一般化した schema として扱う。

### 3. 基本構文の生成

#### Product・abstraction・application

\(r=(\sigma_1,\sigma_2,\sigma_3)\in\mathcal R_{sp}\cup\mathcal R_{pr}\)
ごとに、次で構文を生成する。\(z^{\sigma_1}\) は
\(\mathsf E_{\sigma_1}\) の変数である。

\[
\frac{A\in\mathsf C_{\sigma_1}\quad B\in\mathsf C_{\sigma_2}}
 {\Pi_r z^{\sigma_1}:A.B\in\mathsf C_{\sigma_3}},
\qquad
\frac{A\in\mathsf C_{\sigma_1}\quad e\in\mathsf E_{\sigma_2}}
 {\lambda_r z^{\sigma_1}:A.e\in\mathsf E_{\sigma_3}},
\]

\[
\frac{f\in\mathsf E_{\sigma_3}\quad a\in\mathsf E_{\sigma_1}}
 {f@_r a\in\mathsf E_{\sigma_2}}.
\]

binder の scope は body である。Program の
\((*^v_i,*^c_j,*^c_k)\) に対する \(\Pi\) は
\(z\notin\mathrm{FV}(B)\) を満たすものとする。
term 引数と型引数のどちらにも、同じ \(\Pi_r,\lambda_r,@_r\) を使う。

#### Rule label

以下で使う product rule の名前を定める。

\[
\begin{aligned}
s^{i,j}&:=(*^s_i,*^s_j,*^s_{\max(i,j)}),\\
r^{i,j}_{vc}&:=(*^v_i,*^c_j,*^c_{\max(i,j)}),\\
r^{q;i,j}_{tc}&:=(\square^q_i,*^c_j,*^c_{\max(i+1,j)}).
\end{aligned}
\]

非依存 product の略記は、その label を含めて
\(A\to_r B:=\Pi_r z:A.B\)（\(z\notin\mathrm{FV}(B)\)）とする。

\(r\) の三添字は constructor が持つ情報である。例えば多相関数の level は
\(k=\max(i+1,j)\) だが、その型適用の結果は level \(j\) に属する。
application の結果の level を、関数の level と同一にはしない。

#### Alpha 同値と代入

項は alpha 同値で同一視する。renaming と capture-avoiding substitution は
三構文を同時に辿り、\(x_b\) には \(\mathsf{Tm}_b\)、
\(X_b\) には \(\mathsf{Ty}_b\) の構文を代入する。
Program type substitution は term 内の型注釈と型引数にも作用する。

### 4. Set/Prop 固有の構文

#### Constructor

次の表では \(A,B,X,T\in\mathsf{Ty}_{*^s_i}\)、
\(a,b,u,f\in\mathsf{Tm}_{*^s_i}\)、\(P\in\mathsf{Ty}_{*^p}\) とする。
表の引数指定は構文上の条件であり、具体的な型の一致は judgement が検査する。

| constructor | 出力構文 |
| --- | --- |
| \(\Power A\) | \(\mathsf{Ty}_{*^s_i}\) |
| \(\Ty(A,u)\) | \(\mathsf{Ty}_{*^s_i}\) |
| \(\{x_{*^s_i}:A\mid P\}\) | \(\mathsf{Tm}_{*^s_i}\) |
| \(\Pred(A,u,a)\) | \(\mathsf{Ty}_{*^p}\) |
| \(a=b\)、\(\exists A\) | \(\mathsf{Ty}_{*^p}\) |
| \(\Proof P\) | \(\mathsf{Tm}_{*^p}\) |
| \(\Take^s_i(X,T,f)\) | \(\mathsf{Tm}_{*^s_i}\) |
| \(\Take^p_i(X,P,g)\)、\(g\in\mathsf{Tm}_{*^p}\) | \(\mathsf{Tm}_{*^p}\) |
| \(\operatorname{RunStep}(A,B)\) | \(\mathsf{Ty}_{*^s_i}\) |
| \(\operatorname{continue}_{A,B}(a)\)、\(\operatorname{finish}_{A,B}(b)\) | \(\mathsf{Tm}_{*^s_i}\) |
| \(\operatorname{Acc}_{A,B}(f,a)\) | \(\mathsf{Ty}_{*^p}\) |
| \(\operatorname{run}_{A,B}(f,a)\)、\(\operatorname{runCase}_{A,B}(f,a,u)\) | \(\mathsf{Tm}_{*^s_i}\) |

\(\Ty\) は system.md の type lift constructor である。
特に subset \(\{x:A\mid P\}\) は \(\Power A\) の term であり、
その要素の型は \(\Ty(A,\{x:A\mid P\})\) で表す。

#### RunStep recursor

RunStep recursor は結果の分類 \(\sigma\in\mathcal S_{sp}\) を持つ。
\(P\in\mathsf C_\sigma\)、\(r\in\mathsf{Tm}_{*^s_i}\) とし、
\((*^s_i,\sigma,\tau)\in\mathcal R_{sp}\) のとき、

\[
\operatorname{prec}^{\sigma}_{\operatorname{RunStep}(A,B)}
 (x.P,c,d,r)\in\mathsf E_\sigma,
\qquad c,d\in\mathsf E_\tau.
\]

\(x\) の scope は \(P\) である。motive が type なら結果は term、
motive が kind なら結果は type constructor になる。

### 5. Program 固有の構文

#### Type constructor

\(A\in\mathsf{Ty}_{*^v_i}\)、\(B\in\mathsf{Ty}_{*^v_i}\)、
\(\underline C\in\mathsf{Ty}_{*^c_i}\) に対して、

\[
F A\in\mathsf{Ty}_{*^c_i},\qquad
U\underline C\in\mathsf{Ty}_{*^v_i},\qquad
\operatorname{RunStep}(A,B)\in\mathsf{Ty}_{*^v_i}.
\]

#### Term constructor

term constructor は次とする。\(V,W\in\mathsf{Tm}_{*^v_i}\)、
\(M\in\mathsf{Tm}_{*^c_i}\)、\(N\in\mathsf{Tm}_{*^c_j}\)。

| constructor | 出力構文 |
| --- | --- |
| \(\operatorname{return}(V)\) | \(\mathsf{Tm}_{*^c_i}\) |
| \(\operatorname{thunk}(M)\) | \(\mathsf{Tm}_{*^v_i}\) |
| \(\operatorname{force}(V)\) | \(\mathsf{Tm}_{*^c_i}\) |
| \(M\ \operatorname{to}\ x_{*^v_i}:A\ \operatorname{in}\ N\) | \(\mathsf{Tm}_{*^c_j}\) |
| \(\operatorname{let}^v x_{*^v_i}:A=V\ \operatorname{in}\ N\) | \(\mathsf{Tm}_{*^c_j}\) |
| \(\operatorname{continue}_{A,B}(V)\)、\(\operatorname{finish}_{A,B}(V)\) | \(\mathsf{Tm}_{*^v_i}\) |
| \(\operatorname{run}_{A,B}(V,W)\) | \(\mathsf{Tm}_{*^c_i}\) |
| \(\operatorname{runCase}_{A,B}(V,W,M)\) | \(\mathsf{Tm}_{*^c_i}\) |

sequence と let の binder の scope は \(N\) である。
value lambda/application、多相 lambda/application、型演算子は §3 の構文を使う。

### 6. Reflection と Box の構文

#### Reflection の構文写像

reflection はメタレベルの構文写像とする。
Program の各名前を Set の名前へ単射で写し、binder と変数 occurrence に同じ写像を使う。
sort、rule label、構文の写像を次で定める。

\[
\begin{aligned}
\overline{*^q_i}&=*^s_i,&
\overline{\square^q_i}&=\square^s_i,&
\overline{(\sigma_1,\sigma_2,\sigma_3)}
 &=(\bar\sigma_1,\bar\sigma_2,\bar\sigma_3),\\
\operatorname{RfKind}&:\mathsf{Kd}_{*^q_i}\to\mathsf{Kd}_{*^s_i},\\
\operatorname{RfType}&:\mathsf{Ty}_{*^q_i}\to\mathsf{Ty}_{*^s_i},\\
\operatorname{RfTerm}&:\mathsf{Tm}_{*^q_i}\to\mathsf{Tm}_{*^s_i}.
\end{aligned}
\]

\(q=v,c\) のどちらも同じ level の Set 側へ写る。
基本構文の \(\Pi_r,\lambda_r,@_r\) は、引数を再帰的に写し、rule label を
\(r\mapsto\bar r\) と置き換える。特に、

\[
\begin{aligned}
\operatorname{RfKind}(*^q_i)&=*^s_i,\\
\operatorname{RfType}(F A)&=\operatorname{RfType}(A),\\
\operatorname{RfType}(U\underline B)&=\operatorname{RfType}(\underline B),\\
\operatorname{RfType}(\Pi_r z:A.B)
 &=\Pi_{\bar r}\bar z:\operatorname{Rf}(A).\operatorname{Rf}(B),\\
\operatorname{RfTerm}(\lambda_r z:A.M)
 &=\lambda_{\bar r}\bar z:\operatorname{Rf}(A).\operatorname{RfTerm}(M),\\
\operatorname{RfTerm}(M@_r a)
 &=\operatorname{RfTerm}(M)@_{\bar r}\operatorname{Rf}(a).
\end{aligned}
\]

\(\operatorname{Rf}\) は引数の family に応じた
\(\operatorname{RfKind},\operatorname{RfType},\operatorname{RfTerm}\) を表す。
type/kind の \(\Pi_r,\lambda_r,@_r\) にも同じ再帰的な写像を適用する。

#### Program 固有 constructor の reflection

\(\operatorname{return},\operatorname{thunk},\operatorname{force}\) は各引数の
reflection へ写す。§5 の level \(i,j\) を使うと、sequence と value let はそれぞれ

\[
\begin{aligned}
\operatorname{RfTerm}(M\ \operatorname{to}\ x:A\ \operatorname{in}\ N)
 &=(\lambda_{s^{i,j}}\bar x:\operatorname{RfType}(A).\operatorname{RfTerm}(N))
       @_{s^{i,j}}\operatorname{RfTerm}(M),\\
\operatorname{RfTerm}(\operatorname{let}^v x:A=V\ \operatorname{in}\ N)
 &=(\lambda_{s^{i,j}}\bar x:\operatorname{RfType}(A).\operatorname{RfTerm}(N))
       @_{s^{i,j}}\operatorname{RfTerm}(V)
\end{aligned}
\]

へ写す。RunStep、continue、finish、run、runCase は、引数と型注釈を再帰的に
写した同名の Set constructor へ写す。

#### Box と boxed application

Box には閉じた Program 型・項を格納する。\(P\in\mathsf{Ty}_{*^q_i}\) として、

\[
\operatorname{Box}(P)\in\mathsf{Ty}_{*^s_i},\qquad
\operatorname{box}_P(p),\operatorname{Force}_P(t)\in\mathsf{Tm}_{*^s_i},
\]

ただし \(p\in\mathsf{Tm}_{*^q_i}\)、\(t\in\mathsf{Tm}_{*^s_i}\)。
閉性と具体的な型は Box の typing で検査する。
boxed application の構文は型注釈を持たせる。

\[
\begin{aligned}
\operatorname{bapp}_{A,\underline B}(f,a)&\in\mathsf{Tm}_{*^s_j},
 &A&\in\mathsf{Ty}_{*^v_i},\quad
 \underline B\in\mathsf{Ty}_{*^c_j},\\
\operatorname{btapp}_{X:K,\underline B}(f,P)&\in\mathsf{Tm}_{*^s_j},
 &K&\in\mathsf{Kd}_{*^q_i},\quad
 \underline B\in\mathsf{Ty}_{*^c_j}.
\end{aligned}
\]

bapp の引数は \(f\in\mathsf{Tm}_{*^s_{\max(i,j)}}\)、
\(a\in\mathsf{Tm}_{*^s_i}\)。btapp の引数は
\(f\in\mathsf{Tm}_{*^s_{\max(i+1,j)}}\)、
\(P\in\mathsf{Ty}_{*^q_i}\) であり、\(X\) は注釈 \(\underline B\) を束縛する。

### 7. Reduction 定義

#### 関係族と compatible closure

\(b\in\mathcal B\) ごとに、三構文上の一段簡約を相互帰納的に定義する。

\[
\begin{aligned}
\Rightarrow_{\mathsf{Tm}_b}
 &\subseteq\mathsf{Tm}_b\times\mathsf{Tm}_b,\\
\Rightarrow_{\mathsf{Ty}_b}
 &\subseteq\mathsf{Ty}_b\times\mathsf{Ty}_b,\\
\Rightarrow_{\mathsf{Kd}_b}
 &\subseteq\mathsf{Kd}_b\times\mathsf{Kd}_b.
\end{aligned}
\]

以下の root と閉包規則、および §12 の datatype 規則を満たす最小の関係族とする。
\(\Rightarrow_{\mathsf E_\sigma}\) は §1 の略記に従い、
\(\sigma=b\) なら \(\Rightarrow_{\mathsf{Tm}_b}\)、
\(\sigma=\kappa(b)\) なら \(\Rightarrow_{\mathsf{Ty}_b}\) を表す。

Set/Prop の三構文では、各 constructor の Set/Prop 引数の位置について
compatible closure を取る。Program の type/kind では、各 type/kind 引数の
位置について compatible closure を取る。具体的には、これらの位置に穴を持つ
一穴構文 context \(C:\mathsf F\rightsquigarrow\mathsf G\) に対して

\[
\frac{e\Rightarrow_{\mathsf F}e'}
 {C[e]\Rightarrow_{\mathsf G}C[e']}.
\]

context は binder の注釈と body の位置も含み、穴の family と出力の family を
固定する。これにより、Set/Prop の型・kind 内に含まれる term の簡約も伝播する。
Program term の閉包は後述の evaluation context で定める。

#### 基本 beta

\(r=(\sigma_1,\sigma_2,\sigma_3)\) に対する基本 root は

\[
(\lambda_r z:A.e)@_r a\Rightarrow_{\mathsf E_{\sigma_2}}e[z:=a].
\]

Set/Prop では \(r\in\mathcal R_{sp}\)、Program 型演算子では
\(r=(\square^q_i,\square^{q'}_j,\square^{q'}_k)\) の instance を使う。

#### Set/Prop 固有の root

次の label を使う。

\[
p_i:=(*^s_i,\square^p,\square^p),\qquad
h_{i,\sigma}:=(*^s_i,\sigma,\tau)\in\mathcal R_{sp}.
\]

\(h_{i,\sigma}\) の \(\tau\) は §2 の signature で一意に定まる。

\[
\begin{aligned}
\Pred(A,\{x:B\mid P\},t)
 &\Rightarrow_{\mathsf{Ty}_{*^p}}(\lambda_{p_i}x:B.P)@_{p_i}t,\\
\operatorname{prec}^{\sigma}_{\operatorname{RunStep}(A,B)}(x.P,c,d,\operatorname{continue}_{A,B}(a))
 &\Rightarrow_{\mathsf E_\sigma}c@_{h_{i,\sigma}}a,\\
\operatorname{prec}^{\sigma}_{\operatorname{RunStep}(A,B)}(x.P,c,d,\operatorname{finish}_{A,B}(b))
 &\Rightarrow_{\mathsf E_\sigma}d@_{h_{i,\sigma}}b,\\
\operatorname{run}_{A,B}(f,a)
 &\Rightarrow_{\mathsf{Tm}_{*^s_i}}\operatorname{runCase}_{A,B}(f,a,f@_{s^{i,i}}a),\\
\operatorname{runCase}_{A,B}(f,a,\operatorname{continue}_{A,B}(a'))
 &\Rightarrow_{\mathsf{Tm}_{*^s_i}}\operatorname{run}_{A,B}(f,a'),\\
\operatorname{runCase}_{A,B}(f,a,\operatorname{finish}_{A,B}(b))
 &\Rightarrow_{\mathsf{Tm}_{*^s_i}}b.
\end{aligned}
\]

prec の branch application は、branch の product label
\(h_{i,\sigma}\) を持ち、結果は \(\mathsf E_\sigma\) に属する。

#### Program computation の evaluation context

\(E_h^j\) は、穴が \(\mathsf{Tm}_{*^c_h}\)、出力が
\(\mathsf{Tm}_{*^c_j}\) に属する一穴構文 context とする。次で生成する。

\[
\frac{}{[\,]\in E_h^h},
\qquad
\frac{E\in E_h^{\max(i,j)}\quad V\in\mathsf{Tm}_{*^v_i}}
 {E@_{r^{i,j}_{vc}}V\in E_h^j},
\]

\[
\frac{E\in E_h^{\max(i+1,j)}\quad P\in\mathsf{Ty}_{*^q_i}}
 {E@_{r^{q;i,j}_{tc}}P\in E_h^j},
\]

\[
\frac{E\in E_h^i\quad A\in\mathsf{Ty}_{*^v_i}
 \quad N\in\mathsf{Tm}_{*^c_j}}
 {E\ \operatorname{to}\ x_{*^v_i}:A\ \operatorname{in}\ N\in E_h^j},
\]

\[
\frac{E\in E_h^i\quad A,B\in\mathsf{Ty}_{*^v_i}
 \quad V,W\in\mathsf{Tm}_{*^v_i}}
 {\operatorname{runCase}_{A,B}(V,W,E)\in E_h^i}.
\]

computation の簡約をこの context で閉じる。

\[
\frac{M\Rightarrow_{\mathsf{Tm}_{*^c_h}}M'\quad E\in E_h^j}
 {E[M]\Rightarrow_{\mathsf{Tm}_{*^c_j}}E[M']}.
\]

#### Program computation の root

root は次とする。各 level は §3・§5 の出力構文に従う。

\[
\begin{aligned}
\operatorname{force}(\operatorname{thunk}(M))&\Rightarrow_{\mathsf{Tm}_{*^c_i}}M,\\
(\lambda_{r^{i,j}_{vc}}x:A.M)@_{r^{i,j}_{vc}}V&\Rightarrow_{\mathsf{Tm}_{*^c_j}}M[x:=V],\\
(\lambda_{r^{q;i,j}_{tc}}X:K.M)@_{r^{q;i,j}_{tc}}P&\Rightarrow_{\mathsf{Tm}_{*^c_j}}M[X:=P],\\
\operatorname{return}(V)\ \operatorname{to}\ x:A\ \operatorname{in}\ N
 &\Rightarrow_{\mathsf{Tm}_{*^c_j}}N[x:=V],\\
\operatorname{let}^v x:A=V\ \operatorname{in}\ N
 &\Rightarrow_{\mathsf{Tm}_{*^c_j}}N[x:=V],\\
\operatorname{run}_{A,B}(f,a)
 &\Rightarrow_{\mathsf{Tm}_{*^c_i}}\operatorname{runCase}_{A,B}(f,a,\operatorname{force}(f)@_{r^{i,i}_{vc}}a),\\
\operatorname{runCase}_{A,B}(f,a,\operatorname{return}(\operatorname{continue}_{A,B}(a')))
 &\Rightarrow_{\mathsf{Tm}_{*^c_i}}\operatorname{run}_{A,B}(f,a'),\\
\operatorname{runCase}_{A,B}(f,a,\operatorname{return}(\operatorname{finish}_{A,B}(b)))
 &\Rightarrow_{\mathsf{Tm}_{*^c_i}}\operatorname{return}(b).
\end{aligned}
\]

型適用の引数 \(P\) は型構文として代入する。実行の評価位置は \(E_h^j\) が指定し、
型演算子の簡約は型検査時の \(\Rightarrow_{\mathsf{Ty}_{*^q_i}}\) と
\(\Rightarrow_{\mathsf{Kd}_{*^q_i}}\) が扱う。
Program value の \(\Rightarrow_{\mathsf{Tm}_{*^v_i}}\) は空関係となる。

#### Box の root

Box の root は次とする。\(r\) は閉じて型付けされた Program の
\(\mathsf{Tm}_{*^q_i}\) の項であり、
\(\Rightarrow_{\mathsf{Tm}_{*^q_i}}\)-normal form である。

\[
\begin{aligned}
M\Rightarrow_{\mathsf{Tm}_{*^c_i}}M'&\Longrightarrow
 \operatorname{box}_{\underline B}(M)
 \Rightarrow_{\mathsf{Tm}_{*^s_i}}\operatorname{box}_{\underline B}(M'),\\
\operatorname{Force}_P(\operatorname{box}_P(r))
 &\Rightarrow_{\mathsf{Tm}_{*^s_i}}\operatorname{RfTerm}(r),\\
\operatorname{bapp}_{A,\underline B}
 (\operatorname{box}_{A\to_{r^{i,j}_{vc}}\underline B}(M),\operatorname{box}_A(V))
 &\Rightarrow_{\mathsf{Tm}_{*^s_j}}\operatorname{box}_{\underline B}(M@_{r^{i,j}_{vc}}V),\\
\operatorname{btapp}_{X:K,\underline B}
 (\operatorname{box}_{\Pi_{r^{q;i,j}_{tc}}X:K.\underline B}(M),P)
 &\Rightarrow_{\mathsf{Tm}_{*^s_j}}\operatorname{box}_{\underline B[X:=P]}(M@_{r^{q;i,j}_{tc}}P).
\end{aligned}
\]

Set の compatible context は Program payload を一つの構文引数として扱い、
payload の実行は box step が与える。

### 8. Context と judgement 定義

#### Context と基本 judgement

Set/Prop context と Program context を次で生成する。

\[
\begin{aligned}
\Gamma&::=\varnothing\mid\Gamma,x_b:A\mid\Gamma,X_b:K
       &&(b\in\mathcal B_{sp}),\\
\Delta&::=\varnothing\mid\Delta,X_{*^q_i}:K
                       \mid\Delta,x_{*^v_i}:A
       &&(q\in\{v,c\}).
\end{aligned}
\]

Program type/kind は \(\Delta\) の型変数部分 \(\Theta\) の下で検査する。
\(H\) は規則が属する領域の context を表す。基本 judgement は
\(\operatorname{WF}(H)\)、\(H\vdash e:A\)、\(\Gamma\vDash P\) とする。
\(H\vdash K:\kappa(b)\) も同じ二項形式の formation instance である。

\[
\frac{}{\operatorname{WF}(\varnothing)},\qquad
\frac{\operatorname{WF}(H)\quad H\vdash A:\sigma}
 {\operatorname{WF}(H,z^\sigma:A)},\qquad
\frac{\operatorname{WF}(H)}{H\vdash b:\kappa(b)}.
\]

context extension では上の context grammar、freshness、構文 family を満たすものを使う。
変数規則は \(H,z:A\vdash z:A\)。各 judgement は well-formed context への
weakening を持つ。以下の規則の前提は、その context の well-formedness も含む。

#### Product・abstraction・application の typing

\(r=(\sigma_1,\sigma_2,\sigma_3)\) に対する基本規則は

\[
\frac{H\vdash A:\sigma_1\quad H,z:A\vdash B:\sigma_2}
 {H\vdash\Pi_r z:A.B:\sigma_3},
\]

\[
\frac{H\vdash A:\sigma_1\quad H,z:A\vdash B:\sigma_2
       \quad H,z:A\vdash e:B}
 {H\vdash\lambda_r z:A.e:\Pi_r z:A.B},
\]

\[
\frac{H\vdash A:\sigma_1\quad H,z:A\vdash B:\sigma_2
       \quad H\vdash f:\Pi_r z:A.B\quad H\vdash a:A}
 {H\vdash f@_r a:B[z:=a]}.
\]

構文上 \(e\in\mathsf E_\sigma\)、\(A\in\mathsf C_\sigma\) であることを
各 instance の条件とする。右辺の型が \(b\) の場合、
\(H\vdash A:b\) は type constructor の typing そのものである。
これによって sorting と type-as-term の接続が同じ judgement に入る。

#### Conversion

比較する構文 family を一つ固定する。

\[
\mathsf F\in
\{\mathsf{Ty}_b,\mathsf{Kd}_b\mid b\in\mathcal B\}.
\]

ここで同じ family とは、type constructor / kind の区別、領域、level が
すべて一致することをいう。§7 で定めた簡約から、conversion を次で定義する。

\[
\equiv_{\mathsf{Ty}_b}
 :=(\Rightarrow_{\mathsf{Ty}_b}\cup\Leftarrow_{\mathsf{Ty}_b})^*,
\qquad
\equiv_{\mathsf{Kd}_b}
 :=(\Rightarrow_{\mathsf{Kd}_b}\cup\Leftarrow_{\mathsf{Kd}_b})^*.
\]

\(\Leftarrow_{\mathsf F}\) は \(\Rightarrow_{\mathsf F}\) の逆関係、
\((-)^*\) は反射的・推移的閉包を表す。
conversion \(\equiv_{\mathsf F}\) は、一段簡約 \(\Rightarrow_{\mathsf F}\) を含む
\(\mathsf F\) 上の最小の反射的・対称的・推移的関係とする。明示的には、
\(A,B\in\mathsf F\) に対して

\[
\begin{aligned}
A\equiv_{\mathsf F}B
\quad:\Longleftrightarrow\quad
&\exists n\in\mathbb N,\ \exists A_0,\ldots,A_n\in\mathsf F,\\
&A_0=A,\quad A_n=B,\\
&\forall j<n,\quad
 A_j\Rightarrow_{\mathsf F}A_{j+1}
 \ \lor\ A_{j+1}\Rightarrow_{\mathsf F}A_j.
\end{aligned}
\]

§3 のとおり構文は alpha 同値で同一視する。各段の構文には rule label と
分類情報を保持し、簡約の各 instance は §7 の label の条件を満たす。
途中の \(A_j\) に要求するのは \(\mathsf F\) への所属であり、
端点の formation は次の conversion 規則の前提で検査する。

conversion 規則は \(\sigma\in\mathcal S\)、
\(e\in\mathsf E_\sigma\)、\(A,B\in\mathsf C_\sigma\) に対して

\[
\frac{H\vdash e:A\quad H\vdash A:\sigma\quad H\vdash B:\sigma
       \quad A\equiv_{\mathsf C_\sigma}B}
 {H\vdash e:B}.
\]

\(\sigma=b\) では term の型を \(\mathsf{Ty}_b\) 内で比較し、
\(\sigma=\kappa(b)\) では type constructor の kind を
\(\mathsf{Kd}_b\) 内で比較する。family が明らかな場合は
\(A\equiv B\) と略記する。

### 9. Set/Prop の固有 judgement

#### 規則 schema の移行

system.md の power set/subset、equality、choice、RunStep の形成・constructor、
Acc/run の各規則を、
次の変換で規則 schema として移す。

| 旧規則の記法 | 新規則の記法と構文条件 |
| --- | --- |
| \(\Gamma\vdash A:\sigma\) | \(\Gamma\vdash A:\sigma\)、\(A\in\mathsf C_\sigma\) |
| \(\Gamma\vdash t:A:\sigma\) | \(\Gamma\vdash t:A\)、\(t\in\mathsf E_\sigma\)、\(A\in\mathsf C_\sigma\) |
| \(\Gamma,x:A:\sigma\) | \(\Gamma,x:A\)、\(x\in\mathsf E_\sigma\) |
| \(\Gamma\vDash P\) | \(\Gamma\vDash P\)、\(P\in\mathsf{Ty}_{*^p}\) |

formation・provability の全前提を引き継ぐ。

#### Power set と subset

例えば、

\[
\frac{\Gamma\vdash A:*^s_i}{\Gamma\vdash\Power A:*^s_i},
\qquad
\frac{\Gamma\vdash A:*^s_i\quad\Gamma,x:A\vdash P:*^p}
 {\Gamma\vdash\{x:A\mid P\}:\Power A},
\]

\[
\frac{\Gamma\vdash A:*^s_i\quad\Gamma\vdash S:\Power A}
 {\Gamma\vdash\Ty(A,S):*^s_i},
\]

\[
\frac{\Gamma\vdash A:*^s_i\quad\Gamma\vdash S:\Power A
       \quad\Gamma\vdash t:A\quad\Gamma\vDash\Pred(A,S,t)}
 {\Gamma\vdash t:\Ty(A,S)}.
\]

#### Provability と proof term

provable と proof term は

\[
\frac{\Gamma\vdash t:P\quad\Gamma\vdash P:*^p}{\Gamma\vDash P},
\qquad
\frac{\Gamma\vDash P}{\Gamma\vdash\Proof P:P}.
\]

#### Acc・run・runCase

Set run は \(\Gamma\vDash\operatorname{Acc}_{A,B}(f,a)\) を前提とする。
runCase はさらに transition \(r\) の型付けと
\(\Gamma\vDash f@_{s^{i,i}}a=r\) を前提とする。

#### RunStep recursor の typing

prec は \(D=\operatorname{RunStep}(A,B)\)、
\(h_{i,\sigma}=(*^s_i,\sigma,\tau)\) と置き、

\[
\begin{gathered}
\Gamma\vdash A:*^s_i,\quad\Gamma\vdash B:*^s_i,\quad\Gamma\vdash r:D,\\
\Gamma,x:D\vdash P:\sigma,\qquad
h_{i,\sigma}\in\mathcal R_{sp},\\
\Gamma\vdash c:\Pi_{h_{i,\sigma}}a:A.P[x:=\operatorname{continue}_{A,B}(a)],\\
\Gamma\vdash d:\Pi_{h_{i,\sigma}}b:B.P[x:=\operatorname{finish}_{A,B}(b)]
\end{gathered}
\]

および二つの branch 型の \(\tau\) での formation から、

\[
\Gamma\vdash\operatorname{prec}^{\sigma}_D(x.P,c,d,r):P[x:=r]
\]

を得る。結果の分類 \(\sigma\) と branch の分類 \(\tau\) を区別する。

### 10. Program の固有 judgement と多相性

#### Type formation

\(F,U,\operatorname{RunStep}\) の formation は

\[
\frac{\Theta\vdash A:*^v_i}{\Theta\vdash F A:*^c_i},\qquad
\frac{\Theta\vdash\underline B:*^c_i}{\Theta\vdash U\underline B:*^v_i},\qquad
\frac{\Theta\vdash A:*^v_i\quad\Theta\vdash B:*^v_i}
 {\Theta\vdash\operatorname{RunStep}(A,B):*^v_i}.
\]

#### Term typing と run

system.md の return/thunk/force、sequence、value let、continue/finish、run/runCase の
規則は §5 の構文 family に沿って二項 judgement へ移す。
具体的には、\(\Delta\vdash_vV:A\)、\(\Delta\vdash_cM:\underline B\) を
それぞれ \(\Delta\vdash V:A\)、\(\Delta\vdash M:\underline B\) とし、
type formation は \(\Theta\vdash A:*^v_i\)、
\(\Theta\vdash\underline B:*^c_j\) とする。
各 term typing は表示された型の formation を要求する。
Program run の step function は

\[
f:U(A\to_{r^{i,i}_{vc}}F(\operatorname{RunStep}(A,B)))
\]

という value 型を持つ。Program run はこの型と初期値の型で導入する。

#### 型引数に関する product・abstraction・application

多相性を明示すると、\(K\in\mathsf{Kd}_{*^q_i}\)、
\(\underline B\in\mathsf{Ty}_{*^c_j}\)、\(k=\max(i+1,j)\) に対して、

\[
\frac{\Theta\vdash K:\square^q_i
       \quad\Theta,X:K\vdash\underline B:*^c_j}
 {\Theta\vdash\Pi_{r^{q;i,j}_{tc}}X:K.\underline B:*^c_k},
\]

\[
\frac{\Theta\vdash\Pi_{r^{q;i,j}_{tc}}X:K.\underline B:*^c_k
       \quad\Delta,X:K\vdash M:\underline B}
 {\Delta\vdash\lambda_{r^{q;i,j}_{tc}}X:K.M:\Pi_{r^{q;i,j}_{tc}}X:K.\underline B},
\]

\[
\frac{\Theta\vdash K:\square^q_i
       \quad\Theta,X:K\vdash\underline B:*^c_j
       \quad\Delta\vdash M:\Pi_{r^{q;i,j}_{tc}}X:K.\underline B
       \quad\Theta\vdash P:K}
 {\Delta\vdash M@_{r^{q;i,j}_{tc}}P:\underline B[X:=P]}.
\]

\(X\) は fresh とする。\(K=*^v_i\) は value type についての量化、
\(K=*^c_i\) は computation type についての量化である。
一般の \(K\) では型演算子について量化できる。
多相 computation を value として渡す型は
\(U(\Pi_{r^{q;i,j}_{tc}}X:K.\underline B)\) で表す。

### 11. Well-termination と Box の judgement

#### Reflection context と well-termination

reflection context は

\[
\begin{aligned}
\operatorname{RfCtx}(\varnothing)&=\varnothing,\\
\operatorname{RfCtx}(\Delta,X:K)
 &=\operatorname{RfCtx}(\Delta),\bar X:\operatorname{RfKind}(K),\\
\operatorname{RfCtx}(\Delta,x:A)
 &=\operatorname{RfCtx}(\Delta),\bar x:\operatorname{RfType}(A).
\end{aligned}
\]

\(P:*^q_i\) に対して、well-termination は二つの有限導出の組とする。

\[
\Delta\Vdash p:P
\quad:\Longleftrightarrow\quad
\Delta\vdash p:P
\ \land\
\operatorname{RfCtx}(\Delta)\vdash
\operatorname{RfTerm}(p):\operatorname{RfType}(P).
\]

右側の反映された型は \(*^s_i\) に属する。
第二の導出は Set run の Acc 条件も検査する。

#### Box の formation・導入・Force

\(\operatorname{WF}(\Gamma)\) の下で Box の規則は次とする。

\[
\frac{\varnothing\vdash P:*^q_i}
 {\Gamma\vdash\operatorname{Box}(P):*^s_i},\qquad
\frac{\varnothing\vdash P:*^q_i\quad\varnothing\Vdash p:P}
 {\Gamma\vdash\operatorname{box}_P(p):\operatorname{Box}(P)},
\]

\[
\frac{\varnothing\vdash P:*^q_i\quad\Gamma\vdash b:\operatorname{Box}(P)}
 {\Gamma\vdash\operatorname{Force}_P(b):\operatorname{RfType}(P)}.
\]

#### Boxed application

閉じた \(A:*^v_i\)、\(\underline B:*^c_j\) の formation と
\(\Gamma\vdash f:\operatorname{Box}(A\to_{r^{i,j}_{vc}}\underline B)\)、
\(\Gamma\vdash a:\operatorname{Box}(A)\) から、

\[
\Gamma\vdash\operatorname{bapp}_{A,\underline B}(f,a):\operatorname{Box}(\underline B)
\]

を得る。また、\(\varnothing\vdash K:\square^q_i\)、
\(X:K\vdash\underline B:*^c_j\)、\(\varnothing\vdash P:K\)、
\(\Gamma\vdash f:\operatorname{Box}(\Pi_{r^{q;i,j}_{tc}}X:K.\underline B)\) から、

\[
\Gamma\vdash\operatorname{btapp}_{X:K,\underline B}(f,P):
\operatorname{Box}(\underline B[X:=P])
\]

を得る。Box の level は Program 型の level に一致する。

### 12. Datatype 宣言の移行

#### 宣言と field の条件

宣言環境 \(\mathcal D\) の datatype に、parameter kind と結果 level を付ける。

\[
I^v(X_1:K_1,\ldots,X_n:K_n):*^v_k,
\qquad
C_h^v(x_1:A_{h1},\ldots,x_{m_h}:A_{hm_h}):I^v(\vec X).
\]

parameter は順序付き telescope とし、各 field は parameter context の下で
\(A_{hj}:*^v_{d_{hj}}\)、\(d_{hj}\leq k\) を満たす。
parameter kind の level も \(k\) 以下とする。宣言の自己参照は strictly positive
であり、型演算子を展開した reflected field についても同じ検査を要求する。
constructor の括弧は field telescope を表す。各 field 型は value 変数に依存せず、
constructor application はこの telescope の全引数を受け取る。

#### Program constructor と case

宣言から \(I^v(\vec P)\in\mathsf{Ty}_{*^v_k}\)、
\(C_h^v[\vec P](\vec V)\in\mathsf{Tm}_{*^v_k}\) を生成する。
Program case は結果型 \(\underline B:*^c_j\) を注釈に持つ
\(\mathsf{Tm}_{*^c_j}\) の constructor とする。constructor ごとの branch は、
対応する field の value 変数を束縛する。
formation、constructor、case の premise は system.md の規則を telescope と level に
合わせて移し、case の各 branch は同じ \(\underline B\) を持つ。

\[
\operatorname{case}^v_{\underline B}
 (C_h^v[\vec P](\vec V);\overline{C_l^v(\vec x_l)\mapsto M_l})
\Rightarrow_{\mathsf{Tm}_{*^c_j}}M_h[\vec x_h:=\vec V].
\]

#### Set の鏡像と case

Set の鏡像は parameter kind、field 型、名前を reflection した宣言とする。
\(I^s\) と \(C_h^s\) はそれぞれ \(\mathsf{Ty}_{*^s_k}\)、
\(\mathsf{Tm}_{*^s_k}\) の constructor を生成する。
case の reflection 用に、結果型注釈 \(B:*^s_j\) を持つ非依存 Set case を設ける。
scrutinee を \(I^s(\vec P)\)、全 branch を field context の下で \(B\) と型付けし、
constructor に対して対応する branch への代入を簡約規則とする。

\[
\operatorname{RfTerm}(\operatorname{case}^v_{\underline B}(V;\vec M))
=\operatorname{case}^s_{\operatorname{RfType}(\underline B)}
 (\operatorname{RfTerm}(V);\operatorname{RfTerm}(\vec M)).
\]

Set case の compatible context には scrutinee の位置を加える。
Program case の scrutinee は value であり、§7 の computation evaluation context は
そのまま使う。
constructor と datatype application の reflection は、名前を鏡像名へ写し、
parameter と field を再帰的に写す。

## 構文分離の例

### Set の型演算子と多相 term

この例の label を

\[
t_i:=(\square^s_i,\square^s_i,\square^s_i),\qquad
u_i:=(\square^s_i,*^s_i,*^s_{i+1})
\]

と置く。

\[
\begin{aligned}
\lambda_{t_i}X:*^s_i.X
 &: \Pi_{t_i}X:*^s_i.*^s_i
 &&\text{type constructor と kind},\\
\lambda_{u_i}X:*^s_i.\lambda_{s^{i,i}}x:X.x
 &: \Pi_{u_i}X:*^s_i.(X\to_{s^{i,i}}X)
 &&\text{term と type},\\
\Pi_{u_i}X:*^s_i.(X\to_{s^{i,i}}X) &: *^s_{i+1}.
\end{aligned}
\]

最初の lambda は \(\mathsf{Ty}_{*^s_i}\)、二番目の lambda は
\(\mathsf{Tm}_{*^s_{i+1}}\) に属する。
\(*^s_i\) は \(\mathsf{Kd}_{*^s_i}\) なので、
\(\Power:\mathsf{Ty}_{*^s_i}\to\mathsf{Ty}_{*^s_i}\) の引数位置には入らない。

### Program の型演算子と多相 identity

#### 定義と適用

型演算子の label を \(t^{vc}_i:=(\square^v_i,\square^c_i,\square^c_i)\) と置く。

\[
\begin{aligned}
\lambda_{t^{vc}_i}X:*^v_i.FX
 &: \Pi_{t^{vc}_i}X:*^v_i.*^c_i,\\
\mathrm{Id}_i
 &:=\Pi_{r^{v;i,i}_{tc}}X:*^v_i.\,(X\to_{r^{i,i}_{vc}}FX),\\
\mathrm{id}_i
 &:=\lambda_{r^{v;i,i}_{tc}}X:*^v_i.
       \lambda_{r^{i,i}_{vc}}x:X.\operatorname{return}(x),\\
\varnothing\vdash\mathrm{Id}_i&:*^c_{i+1},\\
\varnothing\vdash\mathrm{id}_i&:\mathrm{Id}_i.
\end{aligned}
\]

\(A:*^v_i\)、\(V:A\) に対して
\(\mathrm{id}_i@_{r^{v;i,i}_{tc}}A:A\to_{r^{i,i}_{vc}}FA\)、
\((\mathrm{id}_i@_{r^{v;i,i}_{tc}}A)@_{r^{i,i}_{vc}}V:FA\) であり、
結果は \(\operatorname{return}(V)\) へ簡約する。
\(\operatorname{thunk}(\mathrm{id}_i)\) は \(U\mathrm{Id}_i\) の value である。

#### Reflection と Box

reflection は \(\overline{r^{v;i,i}_{tc}}=u_i\)、
\(\overline{r^{i,i}_{vc}}=s^{i,i}\) より、

\[
\begin{aligned}
\operatorname{RfType}(\mathrm{Id}_i)
 &=\Pi_{u_i}X:*^s_i.(X\to_{s^{i,i}}X),\\
\operatorname{RfTerm}(\mathrm{id}_i)
 &=\lambda_{u_i}X:*^s_i.\lambda_{s^{i,i}}x:X.x.
\end{aligned}
\]

ここでは反映後の bound variable の名前を alpha 同値で \(X,x\) とした。
したがって \(\varnothing\Vdash\mathrm{id}_i:\mathrm{Id}_i\) の両方の導出を構成でき、
\(\operatorname{box}_{\mathrm{Id}_i}(\mathrm{id}_i)\) は
level \(i+1\) の Box に入る。

#### Computation type の量化

\[
\lambda_{r^{c;i,i}_{tc}}Y:*^c_i.
 \lambda_{r^{i,i}_{vc}}u:UY.\operatorname{force}(u)
:
\Pi_{r^{c;i,i}_{tc}}Y:*^c_i.\,(UY\to_{r^{i,i}_{vc}}Y).
\]

## 現行体系との対応と証明義務

### 構文の移行と規則の拡張

変更を次のように対応付ける。

| 変更 | 現行体系との関係 |
| --- | --- |
| term/type/kind、rule label、変数の分類 | 分類情報を消去することで元の式へ戻す |
| 二項 judgement | 元の最後の sort は構文 family と formation premise が担う |
| 異なる level の Set product | system.md の同一 level の規則を拡張し、sort.rs の \(\max\) 規則に合わせる |
| prec の branch level | 拡張した product rule に合わせて \(\sigma\) と \(\tau\) を分ける |
| Program の型演算子・多相性 | 新しい型・項・簡約を追加する |
| level 付き Box、btapp | 多相 Program の型形成と反映先に合わせる |
| datatype の level と Set case | 宣言・reflection に必要な schema を具体化する |

#### 比較先と消去写像

移行の比較先 \(\mathcal U\) を、system.md に §2 の product signature、
Program の型演算子・多相性、level 付き Box を反映した分類前の参照体系とする。
各固有規則は §9–§12 と同じ前提を持つ。\(|-|\) は三構文の分類情報と
rule label を消去する写像とし、Box の payload では Program の
value/computation と型 binder の区別を保つ。\(\mathcal U\) の conversion は、
Set 側では raw compatible reduction、Program type/kind 側では型 lambda の
raw beta の、それぞれの同値閉包とする。

構文分離の保存性は、この比較先 \(\mathcal U\) との間の証明課題である。
新しい多相 Program を旧 Program へ逆変換できることとは区別する。
既存 Program の型と項は level 0 に写せる。

#### 保存性と構文的な証明課題

必要な構文的性質は次である。

1. 三構文を同時に扱う renaming/substitution の family 保存。
2. 新しい導出の消去が \(\mathcal U\) の導出になること。
3. 比較先の導出へ分類情報を付けて新しい導出を構成できること。
4. 注釈付けと代入・簡約の対応、および kind/type formation の generation。
5. conversion の消去による保存と subject reduction。同じ family の端点について、
   逆に参照体系の conversion を持ち上げられるかは追加の証明課題とする。
   その際は、中間項を同じ family に分類できるか、異なる rule label が
   消去後に一致する場合をどう扱うかを検査する。

subset による複数の型付けは維持される。ここで必要なのは、通常の PTS の型一意性を
引用することではなく、各 typing に必要な formation と分類を回収することである。
構文的に family を保つ簡約と、具体的な型を保つ subject reduction は別々に示す。

### Reflection と Box 消去

#### Formation の保存

\(\bar r\in\mathcal R_{sp}\) はすべての Program product rule について成立する。
型・kind の formation の保存は、この対応と \(F/U\) の消去を使って証明する。

\[
\begin{aligned}
\Theta\vdash K:\square^q_i
 &\Longrightarrow\operatorname{RfCtx}(\Theta)\vdash
      \operatorname{RfKind}(K):\square^s_i,\\
\Theta\vdash P:K
 &\Longrightarrow\operatorname{RfCtx}(\Theta)\vdash
      \operatorname{RfType}(P):\operatorname{RfKind}(K).
\end{aligned}
\]

#### 代入と簡約の対応

型引数についても、

\[
\operatorname{Rf}(e[X:=P])
=_\alpha\operatorname{Rf}(e)[\bar X:=\operatorname{RfType}(P)]
\]

を kind/type/term の同時構造帰納法で示す。
value substitution の対応と合わせて、

\[
p\Rightarrow_{\mathsf{Tm}_{*^c_i}}p'
\Longrightarrow
\operatorname{RfTerm}(p)\Rightarrow_{\mathsf{Tm}_{*^s_i}}^{*}\operatorname{RfTerm}(p')
\]

を得るための追加 case が型 beta である。
Program term の Set typing は well-termination の第二の導出が保証する。

#### Box 消去写像

Box 消去は

\[
\begin{aligned}
\lfloor\operatorname{Box}(P)\rfloor&=\operatorname{RfType}(P),\\
\lfloor\operatorname{box}_P(p)\rfloor&=\operatorname{RfTerm}(p),\\
\lfloor\operatorname{Force}_P(t)\rfloor&=\lfloor t\rfloor,\\
\lfloor\operatorname{bapp}_{A,\underline B}(f,a)\rfloor
 &=\lfloor f\rfloor @_{\overline{r^{i,j}_{vc}}}\lfloor a\rfloor,\\
\lfloor\operatorname{btapp}_{X:K,\underline B}(f,P)\rfloor
 &=\lfloor f\rfloor @_{\overline{r^{q;i,j}_{tc}}}\operatorname{RfType}(P)
\end{aligned}
\]

へ拡張する。\(A:*^v_i\)、\(K:\square^q_i\)、\(\underline B:*^c_j\) とし、
各 application には表示した reflected product rule を記録する。
btapp の導出保存は、閉じた \(P:K\) の reflection と Set の型引数への dep elim による。
Box 消去全体は、well-termination を展開した有限導出の同時帰納法で示す。

多相 identity の例により、datatype がなくても閉じた Program 型が存在する。
proof.md §3.2 の「閉じた Program 型が存在しない」という補助的な議論は、
上の一般の formation・代入・application の証明へ置き換える。

### 集合モデル

#### Sort と valuation の解釈

proof.md の trace encoding と raw 解釈を消去後の式に適用する。
Set/Prop の sort の解釈は

\[
\llbracket *^s_i\rrbracket=U_i,\qquad
\llbracket\square^s_i\rrbracket=U_{i+1},\qquad
\llbracket *^p\rrbracket=\mathbb B,\qquad
\llbracket\square^p\rrbracket=U_\omega
\]

とする。異なる level の product は、domain と fiber を
\(U_{\max(i,j)}\)、\(U_{\max(i,j)+1}\)、または
\(U_{\max(i+1,j)}\) へ入れて universe の閉性を使う。
context の valuation は \(\rho(z)\in\llbracket A\rrbracket_\rho\) で定義する。

#### 健全性の主張と証明課題

二項 judgement の健全性の主張は

\[
H\vdash e:A\Longrightarrow
\llbracket e\rrbracket_\rho\in\llbracket A\rrbracket_\rho
\]

であり、ここでは Box を消去した Set/Prop の導出を対象とする。
sort 注釈に応じた raw 解釈の分岐を加える必要はない。

現行 proof.md の TC は未証明である。この移行でも、拡張した参照体系について
conversion の意味保存を示す義務が残る。datatype については、宣言の positivity、
universe 内の帰納的集合、case の意味保存も必要になる。
ここで定めた移行規則と例は、これらの無矛盾性証明の完了を意味しない。

## Rust の構文への対応

### Family と node

三構文の handle を、それぞれ領域と level を持つ node に対応させる。
Set/Prop には `SetTerm`・`SetType`・`SetKind`、Program には
`Value`・`Computation`・`ValueType`・`ComputationType`・`ValueKind`・`ComputationKind`
を用意する。Set/Prop の区別も node の分類情報として保持する。

### Product・abstraction・application

`Prod` の domain は term binder なら type handle、type binder なら kind handle を持つ。
lambda/application も binder・引数の分類で constructor を分け、rule label に入力・body・
結果の level を記録する。型演算子の適用結果を term の型に使うときは、同じ type handle
を参照し、kind が基底 sort であることを検査する。

型引数の product・abstraction・application も、対応する family の
`Prod`・`Lambda`・`Application` として表し、binder と引数の family、rule label を持たせる。

### 代入と kernel の検査

型代入は Program type/kind と、Program term の型注釈を同時に辿る。
runtime value substitution は value 変数の occurrence を置き換える。

既存の `ExpJudgement { term, ty }` に相当する検査結果は二項のまま保ち、
handle の分類と formation の検査結果から次の段の情報を得る。
分類情報の正しさを検査する kernel の入口を設け、外部から受け取った level や
rule label は signature と照合する。
