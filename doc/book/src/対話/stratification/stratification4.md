## 体系定義

[system.md](../../system.md) の Set/Prop と Program を、領域・level ごとの
term/type/kind 構文へ移す。Program には型抽象・型適用を加える。
以下を移行先の体系 \(\mathcal S_{\mathrm{str}}\) とする。

### 1. Sort と構文の分類

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

level は non-cumulative な自然数の構文添字であり、各規則は表示された level で適用する。
level の繰上げは上の product rule に従う。level polymorphic な宣言は、
この規則群を level パラメータでメタレベルに一般化した schema として扱う。

### 3. 基本構文の生成

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
\(z\notin\mathrm{FV}(B)\) を満たすものとし、\(A\Rightarrow B\) と書く。
Program の \((\square^q_i,*^c_j,*^c_k)\) に対する
\(\Pi,\lambda,@\) は、\(\forall X:K.B,\Lambda X:K.M,M[P]\) と書く。
型演算子の lambda/application は \(\lambda^{\mathrm{ty}},@^{\mathrm{ty}}\) とも書く。

\(r\) の三添字は constructor が持つ情報である。例えば多相関数の level は
\(k=\max(i+1,j)\) だが、その型適用の結果は level \(j\) に属する。
application の結果の level を、関数の level と同一にはしない。

項は alpha 同値で同一視する。renaming と capture-avoiding substitution は
三構文を同時に辿り、\(x_b\) には \(\mathsf{Tm}_b\)、
\(X_b\) には \(\mathsf{Ty}_b\) の構文を代入する。
Program type substitution は term 内の型注釈と型引数にも作用する。

### 4. Set/Prop 固有の構文

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

\(A\in\mathsf{Ty}_{*^v_i}\)、\(B\in\mathsf{Ty}_{*^v_i}\)、
\(\underline C\in\mathsf{Ty}_{*^c_i}\) に対して、

\[
F A\in\mathsf{Ty}_{*^c_i},\qquad
U\underline C\in\mathsf{Ty}_{*^v_i},\qquad
\operatorname{RunStep}(A,B)\in\mathsf{Ty}_{*^v_i}.
\]

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
基本構文の \(\Pi,\lambda,@\) は、引数を再帰的に写し、rule label を
\(r\mapsto\bar r\) と置き換える。特に、

\[
\begin{aligned}
\operatorname{RfKind}(*^q_i)&=*^s_i,\\
\operatorname{RfType}(F A)&=\operatorname{RfType}(A),\\
\operatorname{RfType}(U\underline B)&=\operatorname{RfType}(\underline B),\\
\operatorname{RfType}(A\Rightarrow\underline B)
 &=\operatorname{RfType}(A)\to\operatorname{RfType}(\underline B),\\
\operatorname{RfType}(\forall X:K.\underline B)
 &=\Pi\bar X:\operatorname{RfKind}(K).\operatorname{RfType}(\underline B),\\
\operatorname{RfTerm}(\Lambda X:K.M)
 &=\lambda\bar X:\operatorname{RfKind}(K).\operatorname{RfTerm}(M),\\
\operatorname{RfTerm}(M[P])
 &=\operatorname{RfTerm}(M)@\operatorname{RfType}(P).
\end{aligned}
\]

\(\operatorname{return},\operatorname{thunk},\operatorname{force}\) は各引数の
reflection へ写す。sequence と value let はそれぞれ

\[
\begin{aligned}
\operatorname{RfTerm}(M\ \operatorname{to}\ x:A\ \operatorname{in}\ N)
 &=(\lambda\bar x:\operatorname{RfType}(A).\operatorname{RfTerm}(N))
       @\operatorname{RfTerm}(M),\\
\operatorname{RfTerm}(\operatorname{let}^v x:A=V\ \operatorname{in}\ N)
 &=(\lambda\bar x:\operatorname{RfType}(A).\operatorname{RfTerm}(N))
       @\operatorname{RfTerm}(V)
\end{aligned}
\]

へ写す。RunStep、continue、finish、run、runCase は、引数と型注釈を再帰的に
写した同名の Set constructor へ写す。

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

Set/Prop の \(\Rightarrow_{sp}\) は三構文の argument category を保つ
compatible closure、Program 型演算子の \(\Rightarrow_{\mathrm{ty}}\) は
Program type/kind 上の compatible closure とする。基本 root は

\[
(\lambda_r z:A.e)@_r a\Rightarrow e[z:=a].
\]

Set/Prop では \(r\in\mathcal R_{sp}\)、Program 型演算子では
\(r=(\square^q_i,\square^r_j,\square^r_k)\) の instance を使う。
型・kind 内に含まれる各構文の簡約も、その slot を通して閉じる。

Set 固有の root は次とする。

\[
\begin{aligned}
\Pred(A,\{x:B\mid P\},t)
 &\Rightarrow_{sp}(\lambda^{\mathrm{ty}}x:B.P)@^{\mathrm{ty}}t,\\
\operatorname{prec}^{\sigma}(x.P,c,d,\operatorname{continue}_{A,B}(a))
 &\Rightarrow_{sp}c@a,\\
\operatorname{prec}^{\sigma}(x.P,c,d,\operatorname{finish}_{A,B}(b))
 &\Rightarrow_{sp}d@b,\\
\operatorname{run}_{A,B}(f,a)
 &\Rightarrow_{sp}\operatorname{runCase}_{A,B}(f,a,f@a),\\
\operatorname{runCase}_{A,B}(f,a,\operatorname{continue}_{A,B}(a'))
 &\Rightarrow_{sp}\operatorname{run}_{A,B}(f,a'),\\
\operatorname{runCase}_{A,B}(f,a,\operatorname{finish}_{A,B}(b))
 &\Rightarrow_{sp}b.
\end{aligned}
\]

prec の略記は左辺の recursor 添字を \(\operatorname{RunStep}(A,B)\) とする。
application の label は、その branch の product rule から決める。

Program 実行の \(\Rightarrow_c\) は次の evaluation context で閉じる。

\[
E::=[\,]\mid E@^cV\mid E[P]
 \mid E\ \operatorname{to}\ x:A\ \operatorname{in}\ N
 \mid\operatorname{runCase}_{A,B}(V,W,E).
\]

各 context は入力と出力の computation level を持つ。root は

\[
\begin{aligned}
\operatorname{force}(\operatorname{thunk}(M))&\Rightarrow_c M,\\
(\lambda x:A.M)@^cV&\Rightarrow_c M[x:=V],\\
(\Lambda X:K.M)[P]&\Rightarrow_c M[X:=P],\\
\operatorname{return}(V)\ \operatorname{to}\ x:A\ \operatorname{in}\ N
 &\Rightarrow_c N[x:=V],\\
\operatorname{let}^v x:A=V\ \operatorname{in}\ N
 &\Rightarrow_c N[x:=V],\\
\operatorname{run}_{A,B}(f,a)
 &\Rightarrow_c\operatorname{runCase}_{A,B}(f,a,\operatorname{force}(f)@^c a),\\
\operatorname{runCase}_{A,B}(f,a,\operatorname{return}(\operatorname{continue}_{A,B}(a')))
 &\Rightarrow_c\operatorname{run}_{A,B}(f,a'),\\
\operatorname{runCase}_{A,B}(f,a,\operatorname{return}(\operatorname{finish}_{A,B}(b)))
 &\Rightarrow_c\operatorname{return}(b).
\end{aligned}
\]

型適用の引数 \(P\) は型構文として代入する。実行の評価位置は \(E\) が指定し、
型演算子の簡約は型検査時の \(\Rightarrow_{\mathrm{ty}}\) が扱う。

Box の root は次とする。\(r\) は閉じて型付けされた Program の
\(\Rightarrow_c\)-normal form である。

\[
\begin{aligned}
M\Rightarrow_cM'&\Longrightarrow
 \operatorname{box}_{\underline B}(M)
 \Rightarrow_{sp}\operatorname{box}_{\underline B}(M'),\\
\operatorname{Force}_P(\operatorname{box}_P(r))
 &\Rightarrow_{sp}\operatorname{RfTerm}(r),\\
\operatorname{bapp}_{A,\underline B}
 (\operatorname{box}_{A\Rightarrow\underline B}(M),\operatorname{box}_A(V))
 &\Rightarrow_{sp}\operatorname{box}_{\underline B}(M@^cV),\\
\operatorname{btapp}_{X:K,\underline B}
 (\operatorname{box}_{\forall X:K.\underline B}(M),P)
 &\Rightarrow_{sp}\operatorname{box}_{\underline B[X:=P]}(M[P]).
\end{aligned}
\]

Set の compatible context は Program payload を一つの構文引数として扱い、
payload の実行は box step が与える。

### 8. Context と judgement 定義

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

conversion は、型演算子にも適用する。

\[
\frac{H\vdash e:A\quad H\vdash A:\sigma\quad H\vdash B:\sigma
       \quad A\equiv B}
 {H\vdash e:B}.
\]

#### Conversion の比較対象

\(|-|\) を、三構文の分類情報と rule label を消去する写像とする。
Box の payload では Program の value/computation と型 binder の区別を保つ。
比較先 \(\mathcal U\) は、system.md に §2 の product signature、Program の型演算子・
多相性、level 付き Box を反映した、分類前の参照体系である。
各固有規則は §9–§12 と同じ前提を持つ。

\[
A\equiv B\quad:\Longleftrightarrow\quad |A|\equiv_{\mathcal U}|B|.
\]

Set 側の \(\equiv_{\mathcal U}\) は system.md と同じ raw compatible reduction の
同値閉包、Program の type/kind 側では型 lambda の raw beta の同値閉包とする。
新しい分類情報はこの比較に影響しない。この定義では、Set の conversion の途中の
raw 項も比較対象に含まれる。三構文内の簡約の同値閉包との一致は、移行の補題となる。

### 9. Set/Prop の固有 judgement

system.md の power set/subset、equality、choice、RunStep の形成・constructor、
Acc/run の各規則を、
次の変換で規則 schema として移す。

| 旧規則の記法 | 新規則の記法と構文条件 |
| --- | --- |
| \(\Gamma\vdash A:\sigma\) | \(\Gamma\vdash A:\sigma\)、\(A\in\mathsf C_\sigma\) |
| \(\Gamma\vdash t:A:\sigma\) | \(\Gamma\vdash t:A\)、\(t\in\mathsf E_\sigma\)、\(A\in\mathsf C_\sigma\) |
| \(\Gamma,x:A:\sigma\) | \(\Gamma,x:A\)、\(x\in\mathsf E_\sigma\) |
| \(\Gamma\vDash P\) | \(\Gamma\vDash P\)、\(P\in\mathsf{Ty}_{*^p}\) |

formation・provability の全前提を引き継ぐ。例えば、

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

provable と proof term は

\[
\frac{\Gamma\vdash t:P\quad\Gamma\vdash P:*^p}{\Gamma\vDash P},
\qquad
\frac{\Gamma\vDash P}{\Gamma\vdash\Proof P:P}.
\]

Set run は \(\Gamma\vDash\operatorname{Acc}_{A,B}(f,a)\) を前提とする。
runCase はさらに transition \(r\) の型付けと
\(\Gamma\vDash f@a=r\) を前提とする。

prec は \(D=\operatorname{RunStep}(A,B)\) と置き、

\[
\begin{gathered}
\Gamma\vdash A:*^s_i,\quad\Gamma\vdash B:*^s_i,\quad\Gamma\vdash r:D,\\
\Gamma,x:D\vdash P:\sigma,\qquad
(*^s_i,\sigma,\tau)\in\mathcal R_{sp},\\
\Gamma\vdash c:\Pi a:A.P[x:=\operatorname{continue}_{A,B}(a)],\\
\Gamma\vdash d:\Pi b:B.P[x:=\operatorname{finish}_{A,B}(b)]
\end{gathered}
\]

および二つの branch 型の \(\tau\) での formation から、

\[
\Gamma\vdash\operatorname{prec}^{\sigma}_D(x.P,c,d,r):P[x:=r]
\]

を得る。結果の分類 \(\sigma\) と branch の分類 \(\tau\) を区別する。

### 10. Program の固有 judgement と多相性

\(F,U,\operatorname{RunStep}\) の formation は

\[
\frac{\Theta\vdash A:*^v_i}{\Theta\vdash F A:*^c_i},\qquad
\frac{\Theta\vdash\underline B:*^c_i}{\Theta\vdash U\underline B:*^v_i},\qquad
\frac{\Theta\vdash A:*^v_i\quad\Theta\vdash B:*^v_i}
 {\Theta\vdash\operatorname{RunStep}(A,B):*^v_i}.
\]

system.md の return/thunk/force、sequence、value let、continue/finish、run/runCase の
規則は §5 の構文 family に沿って二項 judgement へ移す。
具体的には、\(\Delta\vdash_vV:A\)、\(\Delta\vdash_cM:\underline B\) を
それぞれ \(\Delta\vdash V:A\)、\(\Delta\vdash M:\underline B\) とし、
type formation は \(\Theta\vdash A:*^v_i\)、
\(\Theta\vdash\underline B:*^c_j\) とする。
各 term typing は表示された型の formation を要求する。
Program run の step function は

\[
f:U(A\Rightarrow F(\operatorname{RunStep}(A,B)))
\]

という value 型を持つ。Program run はこの型と初期値の型で導入する。

多相性を明示すると、\(K\in\mathsf{Kd}_{*^q_i}\)、
\(\underline B\in\mathsf{Ty}_{*^c_j}\)、\(k=\max(i+1,j)\) に対して、

\[
\frac{\Theta\vdash K:\square^q_i
       \quad\Theta,X:K\vdash\underline B:*^c_j}
 {\Theta\vdash\forall X:K.\underline B:*^c_k},
\]

\[
\frac{\Theta\vdash\forall X:K.\underline B:*^c_k
       \quad\Delta,X:K\vdash M:\underline B}
 {\Delta\vdash\Lambda X:K.M:\forall X:K.\underline B},
\]

\[
\frac{\Theta\vdash K:\square^q_i
       \quad\Theta,X:K\vdash\underline B:*^c_j
       \quad\Delta\vdash M:\forall X:K.\underline B
       \quad\Theta\vdash P:K}
 {\Delta\vdash M[P]:\underline B[X:=P]}.
\]

\(X\) は fresh とする。\(K=*^v_i\) は value type についての量化、
\(K=*^c_i\) は computation type についての量化である。
一般の \(K\) では型演算子について量化できる。
多相 computation を value として渡す型は
\(U(\forall X:K.\underline B)\) で表す。

### 11. Well-termination と Box の judgement

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

閉じた \(A:*^v_i\)、\(\underline B:*^c_j\) の formation と
\(\Gamma\vdash f:\operatorname{Box}(A\Rightarrow\underline B)\)、
\(\Gamma\vdash a:\operatorname{Box}(A)\) から、

\[
\Gamma\vdash\operatorname{bapp}_{A,\underline B}(f,a):\operatorname{Box}(\underline B)
\]

を得る。また、\(\varnothing\vdash K:\square^q_i\)、
\(X:K\vdash\underline B:*^c_j\)、\(\varnothing\vdash P:K\)、
\(\Gamma\vdash f:\operatorname{Box}(\forall X:K.\underline B)\) から、

\[
\Gamma\vdash\operatorname{btapp}_{X:K,\underline B}(f,P):
\operatorname{Box}(\underline B[X:=P])
\]

を得る。Box の level は Program 型の level に一致する。

### 12. Datatype 宣言の移行

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
\Rightarrow_c M_h[\vec x_h:=\vec V].
\]

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

両 case の compatible/evaluation context には scrutinee の位置を加える。
constructor と datatype application の reflection は、名前を鏡像名へ写し、
parameter と field を再帰的に写す。

## 構文分離の例

### Set の型演算子と多相 term

\[
\begin{aligned}
\lambda^{\mathrm{ty}}X:*^s_i.X
 &: \Pi X:*^s_i.*^s_i
 &&\text{type constructor と kind},\\
\lambda X:*^s_i.\lambda x:X.x
 &: \Pi X:*^s_i.X\to X
 &&\text{term と type},\\
\Pi X:*^s_i.X\to X &: *^s_{i+1}.
\end{aligned}
\]

最初の lambda は \(\mathsf{Ty}_{*^s_i}\)、二番目の lambda は
\(\mathsf{Tm}_{*^s_{i+1}}\) に属する。
\(*^s_i\) は \(\mathsf{Kd}_{*^s_i}\) なので、
\(\Power:\mathsf{Ty}_{*^s_i}\to\mathsf{Ty}_{*^s_i}\) の引数位置には入らない。

### Program の型演算子と多相 identity

\[
\begin{aligned}
\lambda^{\mathrm{ty}}X:*^v_i.FX
 &: \Pi X:*^v_i.*^c_i,\\
\mathrm{Id}_i
 &:=\forall X:*^v_i.\,X\Rightarrow FX,\\
\mathrm{id}_i
 &:=\Lambda X:*^v_i.\lambda x:X.\operatorname{return}(x),\\
\varnothing\vdash\mathrm{Id}_i&:*^c_{i+1},\\
\varnothing\vdash\mathrm{id}_i&:\mathrm{Id}_i.
\end{aligned}
\]

\(A:*^v_i\)、\(V:A\) に対して
\(\mathrm{id}_i[A]:A\Rightarrow FA\)、
\(\mathrm{id}_i[A]@^cV:FA\) であり、結果は \(\operatorname{return}(V)\) へ簡約する。
\(\operatorname{thunk}(\mathrm{id}_i)\) は \(U\mathrm{Id}_i\) の value である。

reflection は

\[
\operatorname{RfType}(\mathrm{Id}_i)
=\Pi X:*^s_i.X\to X,
\qquad
\operatorname{RfTerm}(\mathrm{id}_i)
=\lambda X:*^s_i.\lambda x:X.x.
\]

したがって \(\varnothing\Vdash\mathrm{id}_i:\mathrm{Id}_i\) の両方の導出を構成でき、
\(\operatorname{box}_{\mathrm{Id}_i}(\mathrm{id}_i)\) は
level \(i+1\) の Box に入る。

computation type の量化の例は

\[
\Lambda Y:*^c_i.\lambda u:UY.\operatorname{force}(u)
:
\forall Y:*^c_i.\,UY\Rightarrow Y.
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

構文分離の保存性は、比較先 \(\mathcal U\) との間で示す。
新しい多相 Program を旧 Program へ逆変換できることとは区別する。
既存 Program の型と項は level 0 に写せる。

必要な構文的性質は次である。

1. 三構文を同時に扱う renaming/substitution の family 保存。
2. 新しい導出の消去が \(\mathcal U\) の導出になること。
3. 比較先の導出へ分類情報を付けて新しい導出を構成できること。
4. 注釈付けと代入・簡約の対応、および kind/type formation の generation。
5. conversion の一致と subject reduction。特に sort の異なる label を持つ項が
   消去後に同じ項となる場合の扱い。

subset による複数の型付けは維持される。ここで必要なのは、通常の PTS の型一意性を
引用することではなく、各 typing に必要な formation と分類を回収することである。
構文的に family を保つ簡約と、具体的な型を保つ subject reduction は別々に示す。

### Reflection と Box 消去

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

型引数についても、

\[
\operatorname{Rf}(e[X:=P])
=_\alpha\operatorname{Rf}(e)[\bar X:=\operatorname{RfType}(P)]
\]

を kind/type/term の同時構造帰納法で示す。
value substitution の対応と合わせて、

\[
p\Rightarrow_c p'
\Longrightarrow
\operatorname{RfTerm}(p)\Rightarrow_{sp}^{*}\operatorname{RfTerm}(p')
\]

を得るための追加 case が型 beta である。
Program term の Set typing は well-termination の第二の導出が保証する。

Box 消去は

\[
\begin{aligned}
\lfloor\operatorname{Box}(P)\rfloor&=\operatorname{RfType}(P),\\
\lfloor\operatorname{box}_P(p)\rfloor&=\operatorname{RfTerm}(p),\\
\lfloor\operatorname{Force}_P(t)\rfloor&=\lfloor t\rfloor,\\
\lfloor\operatorname{bapp}(f,a)\rfloor&=\lfloor f\rfloor @\lfloor a\rfloor,\\
\lfloor\operatorname{btapp}(f,P)\rfloor
 &=\lfloor f\rfloor @\operatorname{RfType}(P)
\end{aligned}
\]

へ拡張する。各 application の label は型注釈の reflected product rule で決める。
btapp の導出保存は、閉じた \(P:K\) の reflection と Set の型引数への dep elim による。
Box 消去全体は、well-termination を展開した有限導出の同時帰納法で示す。

多相 identity の例により、datatype がなくても閉じた Program 型が存在する。
proof.md §3.2 の「閉じた Program 型が存在しない」という補助的な議論は、
上の一般の formation・代入・application の証明へ置き換える。

### 集合モデル

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

三構文の handle を、それぞれ領域と level を持つ node に対応させる。
Set/Prop には `SetTerm`・`SetType`・`SetKind`、Program には
`Value`・`Computation`・`ValueType`・`ComputationType`・`ValueKind`・`ComputationKind`
を用意する。Set/Prop の区別も node の分類情報として保持する。

`Prod` の domain は term binder なら type handle、type binder なら kind handle を持つ。
lambda/application も binder・引数の分類で constructor を分け、rule label に入力・body・
結果の level を記録する。型演算子の適用結果を term の型に使うときは、同じ type handle
を参照し、kind が基底 sort であることを検査する。

Program の多相性には `Forall`、`TypeLambda`、`TypeApplication` を追加する。
型演算子の lambda/application はこれらとは別の type node とする。
型代入は Program type/kind と、Program term の型注釈を同時に辿る。
runtime value substitution は value 変数の occurrence を置き換える。

既存の `ExpJudgement { term, ty }` に相当する検査結果は二項のまま保ち、
handle の分類と formation の検査結果から次の段の情報を得る。
分類情報の正しさを検査する kernel の入口を設け、外部から受け取った level や
rule label は signature と照合する。
