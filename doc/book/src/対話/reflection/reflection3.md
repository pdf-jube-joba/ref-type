# Reflection と Boxed Program

## 体系定義

### 構文定義

Program type を \(P\)、型付けされた Program term を \(p\) と書く。
まず、Reflection で用いる二つの記号を区別する。

\[
\begin{aligned}
\operatorname{RfType}
&:\mathsf{ProgramTypeSyntax}
\longrightarrow\mathsf{SetTypeSyntax},\\
\operatorname{RfTerm}
&:\mathsf{TypedProgramTermSyntax}
\longrightarrow\mathsf{SetTermSyntax}.
\end{aligned}
\]

どちらも Set/Prop の raw constructor ではなく、構文を構文へ移す
メタレベルの写像である。ここで \(\mathsf{SetTypeSyntax}\) は、
PTS で型として使われる Set term の構文を表す。

- \(\operatorname{RfType}(P)\) は、Program type \(P\) の内容を
  Set 側で表す型である。特に value type と computation type の区別を消す。
- \(\operatorname{RfTerm}_P(p)\) は、Program term \(p:P\) の計算構造を
  Set 側へ移して得られる term である。

見方としては、\(\operatorname{RfType}\) が型のコンパイル、
\(\operatorname{RfTerm}\) が型付き term のコンパイルであり、
後者の出力に対する Set の型検査が停止性検査になる。

代表的な定義式は次のようになる。

\[
\begin{aligned}
\operatorname{RfType}(X)
&:=X^{\sq^s_0},\\
\operatorname{RfType}(\text{F}A)
&:=\operatorname{RfType}(A),\\
\operatorname{RfType}(\text{U}\underline B)
&:=\operatorname{RfType}(\underline B),\\
\operatorname{RfType}(A\Rightarrow\underline B)
&:=\operatorname{RfType}(A)
\to\operatorname{RfType}(\underline B),\\
\operatorname{RfType}(\operatorname{RunStep}(A,B))
&:=\operatorname{RunStep}
(\operatorname{RfType}(A),\operatorname{RfType}(B)).
\end{aligned}
\]

\[
\begin{aligned}
\operatorname{RfTerm}_{\text{F}A}(\operatorname{return}(V))
&:=\operatorname{RfTerm}_A(V),\\
\operatorname{RfTerm}_{\text{U}\underline B}(\operatorname{thunk}(M))
&:=\operatorname{RfTerm}_{\underline B}(M),\\
\operatorname{RfTerm}_{\underline B}(\operatorname{force}(V))
&:=\operatorname{RfTerm}_{\text{U}\underline B}(V),\\
\operatorname{RfTerm}_{A\Rightarrow\underline B}
(\lambda x^v:A.M)
&:=\lambda x^{*^s_0}:\operatorname{RfType}(A).
\operatorname{RfTerm}_{\underline B}(M),\\
\operatorname{RfTerm}_{\underline B}(M@^cV)
&:=\operatorname{RfTerm}_{A\Rightarrow\underline B}(M)
@\operatorname{RfTerm}_A(V).
\end{aligned}
\]

従って \(\text{F}\)、\(\text{U}\)、
\(\operatorname{return}\)、\(\operatorname{thunk}\)、
\(\operatorname{force}\) は、Set 側へ移した結果では消える。
Program の \(\operatorname{run}\) は Set の \(\operatorname{run}\) へ移るため、
その像が Set typing を持つかどうかは Acc 条件によって決まる。

\(\operatorname{RfTerm}\) は raw term だけでなく、Program typing derivation を
入力に取る。例えば application の domain type は typing derivation から得る。
derivation の選び方によらず同じ Set term が得られることを要求し、
その結果を \(\operatorname{RfTerm}_P(p)\) と略記する。

Boxed Program のために、次を Set/Prop の raw syntax へ加える。

\[
t::=\cdots
\mid\operatorname{Box}(P)
\mid\operatorname{box}_P(p)
\mid\operatorname{Force}_P(t)
\mid t@^{\operatorname{Box}}t.
\]

\(\operatorname{Box}(P)\) は、Reflection による停止性検査を通った
closed Program \(p:P\) の syntax を保持する型である。
\(\operatorname{box}_P(p)\) はその syntax を保持し、
\(\operatorname{Force}_P(t)\) は保持された Program を
reflected Set term として計算する。
\(f@^{\operatorname{Box}}a\) は boxed function と boxed argument を
Program application として合成する。

Box の payload が computation \(M\) の場合、その reduction には Set reduction ではなく
Program reduction \(\Rightarrow_c\) を使う。従って box の内側では
Program の evaluation strategy を保ったまま計算できる。

### reduction 定義

Program computation の一段の reduction を、box の一段の reduction とする。

\[
\frac{M\Rightarrow_c M'}{
\operatorname{box}_{\underline B}(M)
\Rightarrow_s
\operatorname{box}_{\underline B}(M')}.
\tag{Box-Step}
\]

\(r\) を型 \(P\) の closed な Program term で、
\(r\Rightarrow_c r'\) となる \(r'\) が存在しないものとする。
Force は payload が normal form になったところで Reflection の像へ移す。

\[
\operatorname{Force}_P(\operatorname{box}_P(r))
\Rightarrow_s
\operatorname{RfTerm}_P(r).
\tag{Force-Box}
\]

右辺に書かれた \(\operatorname{RfTerm}_P(r)\) は新しい raw constructor ではない。
この rule は、メタレベル写像を展開して得られる Set raw term を右辺とする
rule schema である。

Boxed application は二つの payload から Program application を組み立てる。

\[
\operatorname{box}_{A\Rightarrow\underline B}(M)
@^{\operatorname{Box}}
\operatorname{box}_A(V)
\Rightarrow_s
\operatorname{box}_{\underline B}(M@^cV).
\tag{Box-App}
\]

\(\Rightarrow_s\) の compatible closure により、\(\operatorname{Force}\) の引数と
boxed application の両辺でも Set reduction を行う。
従って \(\operatorname{Force}_{\underline B}
(\operatorname{box}_{\underline B}(M))\) は、Box-Step を使って
\(M\) を Program normal form まで計算した後に Force-Box を使う。

### judgement 定義

\(\vdash\) は、Box の rule も含む Set typing とする。
\(\emptyset\vdash P\ \mathsf{ptype}\) は、closed な Program value type または
computation type の formation を表す。
\(\emptyset\vdash_Pp:P\) は、対応する closed Program term の typing を表す。

Program の well-termination を次で定める。

\[
\emptyset\Vdash p:P
\quad:\Longleftrightarrow\quad
\emptyset\vdash_Pp:P
\ \land\
\emptyset\vdash
\operatorname{RfTerm}_P(p):
\operatorname{RfType}(P):*^s_0.
\]

\(\operatorname{RfTerm}_P(p)\) は構文上は常に計算できるが、
Set typing を持つとは限らない。後半の premise が停止性検査に当たる。

Box の typing rule は次の四つである。

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| box type | \(\Gamma\vdash\operatorname{Box}(P):*^s_0\) | \(\operatorname{WF}(\Gamma)\)<br>\(\emptyset\vdash P\ \mathsf{ptype}\) | |
| box intro | \(\Gamma\vdash\operatorname{box}_P(p):\operatorname{Box}(P):*^s_0\) | \(\operatorname{WF}(\Gamma)\)<br>\(\emptyset\Vdash p:P\) | |
| force box | \(\Gamma\vdash\operatorname{Force}_P(b):\operatorname{RfType}(P):*^s_0\) | \(\Gamma\vdash b:\operatorname{Box}(P):*^s_0\) | |
| boxed application | \(\Gamma\vdash f@^{\operatorname{Box}}a:\operatorname{Box}(\underline B):*^s_0\) | \(\Gamma\vdash f:\operatorname{Box}(A\Rightarrow\underline B):*^s_0\)<br>\(\Gamma\vdash a:\operatorname{Box}(A):*^s_0\) | |

box intro を展開すると、必要な premise は次の二つである。

\[
\frac{
\operatorname{WF}(\Gamma)
\qquad
\emptyset\vdash_Pp:P
\qquad
\emptyset\vdash
\operatorname{RfTerm}_P(p):
\operatorname{RfType}(P):*^s_0
}{
\Gamma\vdash
\operatorname{box}_P(p):
\operatorname{Box}(P):*^s_0
}.
\tag{Box-Intro}
\]

従って \(b:\operatorname{Box}(P)\) という typing judgement は、
中の Program が Reflection typing を持つことを保証する。
Set 側では box を data structure に格納したり関数へ渡したりした後でも、
変数 \(b\) に \(\operatorname{Force}_P\) を適用できる。

Box-App の右辺も box intro の条件を満たす。
実際、二つの box literal の typing から次の Set typing が得られる。

\[
\begin{aligned}
\emptyset\vdash&
\operatorname{RfTerm}_{A\Rightarrow\underline B}(M):
\operatorname{RfType}(A)\to\operatorname{RfType}(\underline B):*^s_0,\\
\emptyset\vdash&
\operatorname{RfTerm}_A(V):
\operatorname{RfType}(A):*^s_0.
\end{aligned}
\]

\(\operatorname{RfTerm}\) の application に対する定義式により、
その Set application は
\(\operatorname{RfTerm}_{\underline B}(M@^cV)\) である。
従って \(M@^cV\) も well-termination を満たし、
\(\operatorname{box}_{\underline B}(M@^cV)\) を形成できる。

## Reflection の読み方

例えば \(\emptyset\vdash_vV:A\) に対して、次の Program を考える。

\[
p
:=
\operatorname{force}
(\operatorname{thunk}(\operatorname{return}(V)))
:\text{F}A.
\]

型と term の Reflection はそれぞれ次になる。

\[
\begin{aligned}
\operatorname{RfType}(\text{F}A)
&=\operatorname{RfType}(A),\\
\operatorname{RfTerm}_{\text{F}A}(p)
&=\operatorname{RfTerm}_A(V).
\end{aligned}
\]

ここで行っているのは Program term \(p\) の評価ではなく、
\(p\) の構文をたどって Set term
\(\operatorname{RfTerm}_A(V)\) を作ることである。
この Set term が \(\operatorname{RfType}(A)\) で型付けできれば、
\(p\) を box にできる。

\[
\operatorname{box}_{\text{F}A}(p):
\operatorname{Box}(\text{F}A).
\]

Box の内側では、まず Program reduction が使われる。

\[
\operatorname{box}_{\text{F}A}(p)
\Rightarrow_s
\operatorname{box}_{\text{F}A}(\operatorname{return}(V)).
\]

Force の下でも同じ reduction が進み、Program normal form に到達した後で
Set term へ変わる。

\[
\begin{aligned}
&\operatorname{Force}_{\text{F}A}
(\operatorname{box}_{\text{F}A}(p))\\
&\quad\Rightarrow_s
\operatorname{Force}_{\text{F}A}
(\operatorname{box}_{\text{F}A}(\operatorname{return}(V)))\\
&\quad\Rightarrow_s
\operatorname{RfTerm}_A(V).
\end{aligned}
\]

従って二つの型は異なるものを表す。

\[
\operatorname{Box}(P)
\not\equiv_s
\operatorname{RfType}(P).
\]

前者の要素は Program-origin を持つ syntax であり、
後者の要素は Reflection により得た Set 側の結果である。

## Boxed application

Boxed function と boxed argument の合成では、Set function application へ
変換せずに Program application を作る。

\[
\begin{aligned}
&\operatorname{box}_{A\Rightarrow\underline B}(\lambda x^v:A.M)
@^{\operatorname{Box}}
\operatorname{box}_A(V)\\
&\quad\Rightarrow_s
\operatorname{box}_{\underline B}
((\lambda x^v:A.M)@^cV)\\
&\quad\Rightarrow_s
\operatorname{box}_{\underline B}(M[x^v:=V]).
\end{aligned}
\]

この後も Box-Step は Program reduction を使う。
従って boxed function と boxed argument を合成してから Force すれば、
application の計算は Program 側で行われ、最終結果だけが
\(\operatorname{RfTerm}\) によって Set 側へ移る。
実装上も Box-Step を Program evaluator に委譲できるため、
Program を最初から Set term へ展開して計算する必要がない。

二つの計算経路は次のように区別できる。

\[
\begin{aligned}
\operatorname{Force}_{A\Rightarrow\underline B}(f)
@\operatorname{Force}_A(a)
&:\operatorname{RfType}(\underline B),\\
\operatorname{Force}_{\underline B}
(f@^{\operatorname{Box}}a)
&:\operatorname{RfType}(\underline B).
\end{aligned}
\]

上は function と argument を先に Reflection の像へ移すため Set reduction を使う。
下は boxed application を先に作るため Program reduction を使う。

## 循環が生じない理由

この体系が用いる依存関係は次の向きだけである。

\[
\left.
\begin{array}{c}
\emptyset\vdash_Pp:P\\
\emptyset\vdash
\operatorname{RfTerm}_P(p):
\operatorname{RfType}(P):*^s_0
\end{array}
\right\}
\Longrightarrow
\operatorname{box}_P(p):\operatorname{Box}(P)
\Longrightarrow
\operatorname{Force}_P(\operatorname{box}_P(p)):
\operatorname{RfType}(P).
\]

Program typing だけから
\(\operatorname{RfTerm}_P(p):\operatorname{RfType}(P)\) を導く rule は置かない。
\(\operatorname{RfTerm}\) は typing rule ではなく、先に展開されるメタレベル写像である。

well-termination の定義に現れる \(\vdash\) は Box を含む Set typing だが、
ここから循環的な derivation は生じない。
\(\operatorname{RfType}\) と \(\operatorname{RfTerm}\) の定義について、
構造に関する帰納法により次を得る。

\[
\begin{aligned}
\operatorname{BoxFree}(\operatorname{RfType}(P)),\\
\operatorname{BoxFree}(\operatorname{RfTerm}_P(p)).
\end{aligned}
\]

ここで \(\operatorname{BoxFree}\) は
\(\operatorname{Box}\)、\(\operatorname{box}\)、\(\operatorname{Force}\)、
boxed application を部分項に持たないことを表す。
さらに Box-free conservativity として、\(\Gamma\)、\(t\)、\(T\) が
Box-free であり、\(\Gamma\vdash t:T:s\) が導出できるなら、
同じ judgement を導く derivation から Box の rule をすべて除去できることを示す。
この性質は新しい root rule の形、Program reduction の決定性、
\(\operatorname{RfTerm}\) の reduction simulation から示す。

特に
\(\operatorname{RfTerm}_P(p):\operatorname{RfType}(P)\) の typing は、
表記上は拡張後の \(\vdash\) を使っていても Box の rule に依存しない。
その derivation を得るために、検査中の
\(\operatorname{box}_P(p)\) や \(\operatorname{Force}_P\) を使うことはできない。

追加した三つの reduction はいずれも型を保存する。

- Box-Step では Program の subject reduction と
  \(\operatorname{RfTerm}\) の reduction simulation を使う。
- Force-Box では Box-Intro の premise から
  \(\operatorname{RfTerm}_P(r):\operatorname{RfType}(P)\) を得る。
- Box-App では boxed application の typing で示した
  \(\operatorname{RfTerm}_{\underline B}(M@^cV)\) の typing を使う。

well-termination から Program の operational な停止を導く定理により、
Box-Step の列も有限になる。この停止性定理では、まず
Box-free conservativity により Reflection の typing derivation から
Box の rule を除き、既存の Set の strong normalization を適用する。

## 結論

Reflection は Program の型付き構文を Set 構文へ移すメタレベル写像として使う。
Box は、その写像の結果が Set typing を持つ Program syntax を
Set 内で first-class に保持する。
Box の内部と boxed application は Program reduction を使い、
\(\operatorname{Force}\) は計算後の Program normal form を Reflection の像へ移す。
