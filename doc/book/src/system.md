# 体系について
とりあえず、現在考えている core calculus をここにまとめる。
ただし、まだ定義できていない部分は載ってない。

体系は Set/Prop を記述する PTS 部分と、CBPV に基づく Program 部分からなる。
Program の型と項は PTS の sort では分類せず、専用の syntactic category と judgement で分類する。
帰納型関連はまとめて章立てする。

## Sort
pure type system のような形で \(S, A, R\) の組を次のように定義する。
以降は特別に書かない限り \(i \in \mathbb{N}\) とする。

- \(\mathcal{S} = \{*^s_{i}, \sq^s_{i} \mid i \in \mathbb{N}\} \cup \{*^p, \sq^p\}\)
    - \(*^s_{i}, \sq^s_{i}\) は set 用の sort
    - \(*^p, \sq^p\) は proposition 用の sort
- \(\mathcal{A} = \{(*^s_{i}, \sq^s_{i})\} \cup \{(*^p, \sq^p)\}\)
- \(\mathcal{R} =\) union of
    - \(\{(*^s_i, *^s_j, *^s_{\max(i,j)}), (*^s_i, \sq^s_j, \sq^s_{\max(i,j)}), (\sq^s_i, \sq^s_j, \sq^s_{\max(i,j)})\}\) ... universe level の異なる dependent product は最小の共通 level に置く
    - \(\{(\sq^s_i, *^s_j, *^s_{\max(i+1,j)})\}\) ... universe 自身を走る場合だけ domain 側の level を一つ上げる
    - \(\{(*^p, *^p, *^p), (\sq^p, *^p, *^p), (\sq^p, \sq^p, \sq^p)\}\) ... \(*^p\) は impredicative だけど依存型のような \((*^p, \sq^p, \sq^p)\) はない。
    - \(\{(*^s_i, *^p, *^p), (*^s_i, \sq^p, \sq^p)\}\) ... \(*^s\) についての命題を用意するため。

普通の変数を \(x\)、Program の type variable を \(X\) とする。
\(s\) や \(s_i\) は \(\mathcal{S}\) の元とする。

> [!note]
> - PTS の変数には sort をつけて \(x^s\) にする
> - Program の value variable は \(x^v\) と書く
> - PTS の typing には sort をつける

## Term, Context, Judgement

（2つあるものは、別の書き方として用意している。）

### Term

#### Set/Prop

- term: \(t = \)
    - 普通の Lambda 項
        | category | definition |
        | --- | --- |
        | sort | \(s\) |
        | variable | \(x^s\) |
        | lambda abstraction | \(\lambda x^s: t. t\) |
        | dependent product type | \(\Pi x^s: t. t\) or \((x^s: t) \to t\) |
        | application | \(t @ t\) or \(t t\) |
    - 証明項
        | category | definition |
        | --- | --- |
        | "proof later" mark | \(\Proof t\) |
    - 集合に関する項
        | category | definition |
        | --- | --- |
        | refinement type | \(\{x^s: t \mid t\}\) |
        | power set | \(\Power t\) |
        | type lift | \(\Ty (t, t)\) |
        | predicate | \(\Pred_t t (t)\) or \(\Pred(t, t, t)\) |
    - equiality の記述
        | category | definition |
        | --- | --- |
        | equality type | \(t = t\) |
        | existence | \(\exists t\) |
        | take operator | \(\Take(t,t,t)\) |
    - Program との接続
        | category | definition |
        | --- | --- |
        | type reflection | \(\operatorname{RfType}(P)\) |
        | term reflection | \(\operatorname{RfTerm}_P(p)\) |
        | accessibility | \(\operatorname{Acc}_{A,A}(V,t)\) |

#### Program

- value type: \(A = \)
    | category | definition |
    | --- | --- |
    | type variable | \(X\) |
    | thunk type | \(\text{U}\underline B\) |
    | run step type | \(\operatorname{RunStep}(A,A)\) |
- computation type: \(\underline B = \)
    | category | definition |
    | --- | --- |
    | returner type | \(\text{F} A\) |
    | function type | \(A\Rightarrow\underline B\) |
- value: \(V = \)
    | category | definition |
    | --- | --- |
    | variable | \(x^v\) |
    | thunk | \(\operatorname{thunk}(M)\) |
    | continue | \(\operatorname{continue}_{A,A}(V)\) |
    | finish | \(\operatorname{finish}_{A,A}(V)\) |
- computation: \(M = \)
    | category | definition |
    | --- | --- |
    | return | \(\operatorname{return}(V)\) |
    | force | \(\operatorname{force}(V)\) |
    | lambda abstraction | \(\lambda x^v:A.M\) |
    | application | \(M @^c V\) |
    | sequence | \(M\ \operatorname{to}\ x^v:A\ \operatorname{in}\ M\) |
    | value let | \(\operatorname{let}^v x^v=V\ \operatorname{in}\ M\) |
    | run | \(\operatorname{run}_{A,A}(V,V)\) |
    | run case | \(\operatorname{runCase}_{A,A}(V,V,M)\) |
- program type: \(P = \)
    | category | definition |
    | --- | --- |
    | value type | \(A\) |
    | computation type | \(\underline B\) |
- program: \(p = \)
    | category | definition |
    | --- | --- |
    | value | \(V\) |
    | computation | \(M\) |

### Context と judgement

- context: \(\Gamma=\)
    | category | definition |
    | --- | --- |
    | empty context | \(\emptyset\) |
    | PTS concat | \(\Gamma, x^s:t:s\) |
    | Program type concat | \(\Gamma,X:\mathsf{vtype}\) |
    | Program value concat | \(\Gamma,x^v:A:\mathsf{value}\) |

- judgement:
    | category | definition |
    | --- | --- |
    | well formed context | \(\operatorname{WF}(\Gamma)\) |
    | PTS sorting | \(\Gamma\vdash t:s\) |
    | PTS typing | \(\Gamma\vdash t:T:s\) |
    | provable | \(\Gamma\vDash P\) |
    | value type formation | \(\Gamma\vdash A\ \mathsf{vtype}\) |
    | computation type formation | \(\Gamma\vdash\underline B\ \mathsf{ctype}\) |
    | value typing | \(\Gamma\vdash_vV:A\) |
    | computation typing | \(\Gamma\vdash_cM:\underline B\) |

### 略記

\[
\begin{aligned}
\operatorname{StepFun}(A,B)
&:=
\text{U}\left(A\Rightarrow
\text{F}(\operatorname{RunStep}(A,B))\right),\\
\operatorname{continueFun}_{A,B}
&:=
\operatorname{thunk}
\left(
\lambda z^v:A.
\operatorname{return}
\left(\operatorname{continue}_{A,B}(z^v)\right)
\right),\\
\operatorname{Next}_{A,B}(f,b,a)
&:=
\operatorname{RfTerm}_{\operatorname{StepFun}(A,B)}(f)@a\\
&\phantom{:={}}
=
\operatorname{RfTerm}_{\operatorname{StepFun}(A,B)}
(\operatorname{continueFun}_{A,B})@b,\\
\operatorname{Terminates}_{A,B}(f,a)
&:=
\operatorname{Acc}_{A,B}
\left(f,\operatorname{RfTerm}_A(a)\right),\\
\operatorname{RunInv}_{A,B}(f,a,M)
&:=
\operatorname{RfTerm}_{\text{F}(\operatorname{RunStep}(A,B))}
\left(\operatorname{force}(f) @^c a\right)\\
&\phantom{:={}}
=
\operatorname{RfTerm}_{\text{F}(\operatorname{RunStep}(A,B))}(M).
\end{aligned}
\]

## reduction

### Set/Prop

\(\Rightarrow_s\) は通常の Lambda 項の reduction と次の root rule の compatible closure とする。

\[
\Pred (A, \{x^s: B \mid P\}, t)
\Rightarrow_s
(\lambda x^s: B. P) @ t.
\]

### Program

Program reduction \(\Rightarrow_c\) は、次の evaluation context による
weak call-by-value reduction とする。

\[
\begin{aligned}
E::={}&
[\,]
\mid E @^c V\\
&\mid E\ \operatorname{to}\ x^v:A\ \operatorname{in}\ M\\
&\mid\operatorname{runCase}_{A,A}(V,V,E).
\end{aligned}
\]

\[
\begin{aligned}
\operatorname{force}(\operatorname{thunk}(M))
&\Rightarrow_c M,\\
(\lambda x^v:A.M) @^c V
&\Rightarrow_c M[x^v:=V],\\
\operatorname{return}(V)\ \operatorname{to}\ x^v:A\ \operatorname{in}\ N
&\Rightarrow_c N[x^v:=V],\\
\operatorname{let}^v x^v=V\ \operatorname{in}\ N
&\Rightarrow_c N[x^v:=V],\\
\operatorname{run}_{A,B}(f,a)
&\Rightarrow_c
\operatorname{runCase}_{A,B}\left(f,a,\operatorname{force}(f) @^c a\right),\\
\operatorname{runCase}_{A,B}
\left(f,a,\operatorname{return}(\operatorname{continue}_{A,B}(a'))\right)
&\Rightarrow_c \operatorname{run}_{A,B}(f,a'),\\
\operatorname{runCase}_{A,B}
\left(f,a,\operatorname{return}(\operatorname{finish}_{A,B}(b))\right)
&\Rightarrow_c \operatorname{return}(b),\\
M\Rightarrow_cM'
&\longrightarrow E[M]\Rightarrow_cE[M'].
\end{aligned}
\]

### reflection

reflection reduction は PTS/Set reduction \(\Rightarrow_s\) の root rule とする。

\[
\begin{aligned}
\operatorname{RfType}(\text{F} A)
&\Rightarrow_s \operatorname{RfType}(A),\\
\operatorname{RfType}(\text{U}\underline B)
&\Rightarrow_s \operatorname{RfType}(\underline B),\\
\operatorname{RfType}(A\Rightarrow\underline B)
&\Rightarrow_s
\operatorname{RfType}(A)\to\operatorname{RfType}(\underline B),\\
\operatorname{RfTerm}_{\text{F} A}(\operatorname{return}(V))
&\Rightarrow_s \operatorname{RfTerm}_{A}(V),\\
\operatorname{RfTerm}_{\text{U}\underline B}(\operatorname{thunk}(M))
&\Rightarrow_s \operatorname{RfTerm}_{\underline B}(M),\\
M\Rightarrow_cM'
&\Longrightarrow
\operatorname{RfTerm}_{\underline B}(M)
\Rightarrow_s\operatorname{RfTerm}_{\underline B}(M'),\\
\operatorname{RfTerm}_{\text{U}(A\Rightarrow\underline B)}(f)
@
\operatorname{RfTerm}_{A}(a)\\
&\qquad\Rightarrow_s
\operatorname{RfTerm}_{\underline B}
\left(\operatorname{force}(f) @^c a\right),\\
\operatorname{RfTerm}_{A\Rightarrow\underline B}(M)
@
\operatorname{RfTerm}_{A}(a)\\
&\qquad\Rightarrow_s
\operatorname{RfTerm}_{\underline B}(M @^c a).
\end{aligned}
\]

### definitional equality

\[
\equiv_s\;:=\;(\Rightarrow_s\cup\Leftarrow_s)^*.
\]

## derivation

### Set/Prop

\(\Gamma::e\) は \(\Gamma,e\) の別表記とする。

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| empty | \(\operatorname{WF}(\emptyset)\) | | |
| axiom | \(\emptyset \vdash s_1: s_2\) | | \(s_1,s_2\in\mathcal{S}\)<br>\((s_1, s_2) \in \mathcal{A}\) |
| start | \(\operatorname{WF}(\Gamma::(x^s: t: s))\) | \(\operatorname{WF}(\Gamma)\)<br>\(\Gamma \vdash t: s\) | \(s\in\mathcal{S}\)<br>\(x^s\notin\Gamma\) |
| weak sort | \(\Gamma::(x^s: t: s) \vdash t_1: s'\) | \(\Gamma \vdash t_1: s'\)<br>\(\operatorname{WF}(\Gamma::(x^s: t: s))\) | \(s,s'\in\mathcal{S}\)<br>\(x^s\notin\Gamma\) |
| weak type | \(\Gamma::(x^s: t: s) \vdash t_1: t_2: s'\) | \(\Gamma \vdash t_1: t_2: s'\)<br>\(\operatorname{WF}(\Gamma::(x^s: t: s))\) | \(s,s'\in\mathcal{S}\)<br>\(x^s\notin\Gamma\) |
| weak sort over Program | \(\Gamma::e \vdash t:s\) | \(\Gamma\vdash t:s\)<br>\(\operatorname{WF}(\Gamma::e)\) | \(e\) は fresh な Program entry |
| weak type over Program | \(\Gamma::e \vdash t:T:s\) | \(\Gamma\vdash t:T:s\)<br>\(\operatorname{WF}(\Gamma::e)\) | \(e\) は fresh な Program entry |
| variable | \(\Gamma::(x^s: t: s) \vdash x^s: t: s\) | \(\operatorname{WF}(\Gamma::(x^s: t: s))\) | \(s\in\mathcal{S}\) |
| conversion | \(\Gamma \vdash t: T_2: s\) | \(\Gamma \vdash t: T_1: s\)<br>\(\Gamma \vdash T_2: s\) | \(s\in\mathcal{S}\)<br>\(T_1 \equiv_s T_2\) |
| dep form | \(\Gamma \vdash (\Pi x^{s_1}:t. T): s_3\) | \(\Gamma \vdash t: s_1\)<br>\(\Gamma::(x^{s_1}: t: s_1) \vdash T: s_2\) | \(s_1,s_2,s_3\in\mathcal{S}\)<br>\((s_1, s_2, s_3) \in \mathcal{R}\)<br>\(x^{s_1}\notin\Gamma\) |
| dep intro | \(\Gamma \vdash (\lambda x^{s_1}:t.m): (\Pi x^{s_1}:t.M) : s_3\) | \(\Gamma \vdash (\Pi x^{s_1}:t. M): s_3\)<br>\(\Gamma::(x^{s_1}:t: s_1) \vdash m: M: s_2\) | \(s_1,s_2,s_3\in\mathcal{S}\)<br>\(x^{s_1}\notin\Gamma\) |
| dep elim | \(\Gamma \vdash (f @ a): T[x := a]: s_2\) | \(\Gamma \vdash f: (\Pi x^{s_1}: t. T): s_3\)<br>\(\Gamma \vdash a: t: s_1\) | \(s_1,s_2,s_3\in\mathcal{S}\) |
| type elem | \(\Gamma \vdash A: s: t\) | \(\Gamma \vdash A: s\)<br>\(\Gamma \vdash s: t\) | \(s,t\in\mathcal{S}\) |
| type sort | \(\Gamma \vdash A: s\) | \(\Gamma \vdash A: s: t\) | \(s,t\in\mathcal{S}\) |

#### provable

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| provable | \(\Gamma\vDash P\) | \(\Gamma\vdash t:P:*^p\) | |
| proof term | \(\Gamma\vdash\Proof P:P:*^p\) | \(\Gamma\vDash P\) | |

#### power set, subset

ここで出てくる \(*^s\) は全部 \(i\) を同じにする。

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| power set form | \(\Gamma\vdash\Power A:*^s\) | \(\Gamma\vdash A:*^s\) | |
| power set intro | \(\Gamma\vdash\Ty(A,B):*^s\) | \(\Gamma\vdash B:\Power A:*^s\) | |
| predicate | \(\Gamma\vdash\Pred(A,B,t):*^p\) | \(\Gamma\vdash B:\Power A:*^s\)<br>\(\Gamma\vdash t:A:*^s\) | |
| subset form | \(\Gamma\vdash\{x^{*^s}:A\mid P\}:\Power A:*^s\) | \(\Gamma\vdash A:*^s\)<br>\(\Gamma,x^{*^s}:A:*^s\vdash P:*^p\) | |
| subset intro | \(\Gamma\vdash t:\Ty(A,B):*^s\) | \(\Gamma\vdash B:\Power A:*^s\)<br>\(\Gamma\vdash t:A:*^s\)<br>\(\Gamma\vDash\Pred(A,B,t)\) | |
| subset weak | \(\Gamma\vdash t:A:*^s\) | \(\Gamma\vdash t:\Ty(A,B):*^s\) | |
| subset prop | \(\Gamma\vDash\Pred(A,B,t)\) | \(\Gamma\vdash t:\Ty(A,B):*^s\) | |

#### equality

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| id form | \(\Gamma\vdash a=b:*^p\) | \(\Gamma\vdash a:A:*^s\)<br>\(\Gamma\vdash b:A:*^s\) | |
| id intro | \(\Gamma\vDash a=a\) | \(\Gamma\vdash a:A:*^s\) | |
| id elim | \(\Gamma\vDash(\lambda x:A.P)@b\) | \(\Gamma\vdash a:A:*^s\)<br>\(\Gamma\vdash b:A:*^s\)<br>\(\Gamma\vDash a=b\)<br>\(\Gamma,x:A:*^s\vdash P:*^p\)<br>\(\Gamma\vDash(\lambda x:A.P)@a\) | |

#### choice

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| exists form | \(\Gamma\vdash\exists T:*^p\) | \(\Gamma\vdash T:*^s\) | |
| exists intro | \(\Gamma\vDash\exists T\) | \(\Gamma\vdash e:T:*^s\) | |
| take elim set | \(\Gamma\vdash\Take(X,T,f):T:*^s\) | \(\Gamma\vdash X:*^s\)<br>\(\Gamma\vdash T:*^s\)<br>\(\Gamma\vdash f:X\to T:*^s\)<br>\(\Gamma\vDash\exists X\)<br>\(\Gamma\vDash(x_1:X)\to(x_2:X)\to f@x_1=f@x_2\) | |
| take elim prop | \(\Gamma\vdash\Take(X,T,f):T:*^p\) | \(\Gamma\vdash X:*^s\)<br>\(\Gamma\vdash T:*^p\)<br>\(\Gamma\vdash f:X\to T:*^p\)<br>\(\Gamma\vDash\exists X\) | |
| take equal | \(\Gamma\vDash\Take(X,T,f)=f@t\) | \(\Gamma\vdash\Take(X,T,f):T:*^s\)<br>\(\Gamma\vdash t:X:*^s\) | |

### Other

#### Program context と type formation

\(\Gamma\vdash_PJ\) は value type formation、computation type formation、
value typing、computation typing のいずれか一つを表す。

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| value type start | \(\operatorname{WF}(\Gamma,X:\mathsf{vtype})\) | \(\operatorname{WF}(\Gamma)\) | \(X\notin\Gamma\) |
| value type variable | \(\Gamma,X:\mathsf{vtype}\vdash X\ \mathsf{vtype}\) | \(\operatorname{WF}(\Gamma,X:\mathsf{vtype})\) | |
| value start | \(\operatorname{WF}(\Gamma,x^v:A:\mathsf{value})\) | \(\operatorname{WF}(\Gamma)\)<br>\(\Gamma\vdash A\ \mathsf{vtype}\) | \(x^v\notin\Gamma\) |
| Program weak | \(\Gamma,e\vdash_PJ\) | \(\Gamma\vdash_PJ\)<br>\(\operatorname{WF}(\Gamma,e)\) | \(e\) は PTS entry、Program type entry、Program value entry のいずれか<br>\(J\) の自由変数を capture しない |
| \(\text{F}\) form | \(\Gamma\vdash \text{F} A\ \mathsf{ctype}\) | \(\Gamma\vdash A\ \mathsf{vtype}\) | |
| \(\text{U}\) form | \(\Gamma\vdash \text{U}\underline B\ \mathsf{vtype}\) | \(\Gamma\vdash\underline B\ \mathsf{ctype}\) | |
| function form | \(\Gamma\vdash A\Rightarrow\underline B\ \mathsf{ctype}\) | \(\Gamma\vdash A\ \mathsf{vtype}\)<br>\(\Gamma\vdash\underline B\ \mathsf{ctype}\) | |
| run step form | \(\Gamma\vdash\operatorname{RunStep}(A,B)\ \mathsf{vtype}\) | \(\Gamma\vdash A\ \mathsf{vtype}\)<br>\(\Gamma\vdash B\ \mathsf{vtype}\) | |

#### Program typing

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| value variable | \(\Gamma,x^v:A:\mathsf{value}\vdash_vx^v:A\) | \(\operatorname{WF}(\Gamma,x^v:A:\mathsf{value})\) | |
| return | \(\Gamma\vdash_c\operatorname{return}(V):\text{F} A\) | \(\Gamma\vdash_vV:A\) | |
| thunk | \(\Gamma\vdash_v\operatorname{thunk}(M):\text{U}\underline B\) | \(\Gamma\vdash_cM:\underline B\) | |
| force | \(\Gamma\vdash_c\operatorname{force}(V):\underline B\) | \(\Gamma\vdash_vV:\text{U}\underline B\) | |
| function intro | \(\Gamma\vdash_c\lambda x^v:A.M:A\Rightarrow\underline B\) | \(\Gamma,x^v:A:\mathsf{value}\vdash_cM:\underline B\) | \(x^v\notin\Gamma\) |
| function elim | \(\Gamma\vdash_cM @^c V:\underline B\) | \(\Gamma\vdash_cM:A\Rightarrow\underline B\)<br>\(\Gamma\vdash_vV:A\) | |
| sequence | \(\Gamma\vdash_c M\ \operatorname{to}\ x^v:A\ \operatorname{in}\ N:\underline B\) | \(\Gamma\vdash_cM:\text{F} A\)<br>\(\Gamma,x^v:A:\mathsf{value}\vdash_cN:\underline B\) | \(x^v\notin\Gamma\) |
| value let | \(\Gamma\vdash_c\operatorname{let}^v x^v=V\ \operatorname{in}\ N:\underline B\) | \(\Gamma\vdash_vV:A\)<br>\(\Gamma,x^v:A:\mathsf{value}\vdash_cN:\underline B\) | \(x^v\notin\Gamma\) |
| continue intro | \(\Gamma\vdash_v\operatorname{continue}_{A,B}(a):\operatorname{RunStep}(A,B)\) | \(\Gamma\vdash_v a:A\)<br>\(\Gamma\vdash B\ \mathsf{vtype}\) | |
| finish intro | \(\Gamma\vdash_v\operatorname{finish}_{A,B}(b):\operatorname{RunStep}(A,B)\) | \(\Gamma\vdash A\ \mathsf{vtype}\)<br>\(\Gamma\vdash_v b:B\) | |

#### Reflection typing

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| reflection value type | \(\Gamma\vdash\operatorname{RfType}(A):*^s_0\) | \(\Gamma\vdash A\ \mathsf{vtype}\) | |
| reflection computation type | \(\Gamma\vdash\operatorname{RfType}(\underline B):*^s_0\) | \(\Gamma\vdash\underline B\ \mathsf{ctype}\) | |
| reflection value | \(\Gamma\vdash\operatorname{RfTerm}_A(V):\operatorname{RfType}(A):*^s_0\) | \(\Gamma\vdash_vV:A\) | |
| reflection computation | \(\Gamma\vdash\operatorname{RfTerm}_{\underline B}(M):\operatorname{RfType}(\underline B):*^s_0\) | \(\Gamma\vdash_cM:\underline B\) | |

#### Acc と run

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| acc form | \(\Gamma\vdash\operatorname{Acc}_{A,B}(f,a):*^p\) | \(\Gamma\vdash_v f:\operatorname{StepFun}(A,B)\)<br>\(\Gamma\vdash a:\operatorname{RfType}(A):*^s_0\) | |
| acc intro | \(\Gamma\vDash\operatorname{Acc}_{A,B}(f,a)\) | \(\Gamma\vdash_v f:\operatorname{StepFun}(A,B)\)<br>\(\Gamma\vdash a:\operatorname{RfType}(A):*^s_0\)<br>\(\Gamma,b^{*^s_0}:\operatorname{RfType}(A):*^s_0\vDash\operatorname{Next}_{A,B}(f,b^{*^s_0},a)\to\operatorname{Acc}_{A,B}(f,b^{*^s_0})\) | \(b^{*^s_0}\notin\Gamma\) |
| acc descent | \(\Gamma\vDash\operatorname{Acc}_{A,B}(f,b)\) | \(\Gamma\vDash\operatorname{Acc}_{A,B}(f,a)\)<br>\(\Gamma\vDash\operatorname{Next}_{A,B}(f,b,a)\) | |
| run | \(\Gamma\vdash_c\operatorname{run}_{A,B}(f,a):\text{F} B\) | \(\Gamma\vdash_v f:\operatorname{StepFun}(A,B)\)<br>\(\Gamma\vdash_v a:A\)<br>\(\Gamma\vDash\operatorname{Terminates}_{A,B}(f,a)\) | |
| run case | \(\Gamma\vdash_c\operatorname{runCase}_{A,B}(f,a,M):\text{F} B\) | \(\Gamma\vdash_v f:\operatorname{StepFun}(A,B)\)<br>\(\Gamma\vdash_v a:A\)<br>\(\Gamma\vdash_cM:\text{F}(\operatorname{RunStep}(A,B))\)<br>\(\Gamma\vDash\operatorname{Terminates}_{A,B}(f,a)\)<br>\(\Gamma\vDash\operatorname{RunInv}_{A,B}(f,a,M)\) | |

## 帰納型と CBPV

### 構文

| category | definition |
| --- | --- |
| value type | \(I^v(\vec A)\) |
| value | \(C_i^v[\vec A](\vec V)\) |
| computation | \(\operatorname{case}^v\left(V;\overline{C_i^v(\vec x^v)\mapsto M}\right)\) |
| Set/Prop term | \(I^s(\vec t)\) |
| Set/Prop term | \(C_i^s[\vec t](\vec t)\) |

### 宣言

\[
\operatorname{inductive}
I^v(X_1,\ldots,X_n)
\ \operatorname{where}\
C_i^v:
A_{i1}\to\cdots\to A_{ik_i}\to I^v(\vec X).
\]

再帰 occurrence \(I^v(\vec X)\) は strictly positive でなければならない。
特に、再帰 occurrence を
\(\text{U}(A\Rightarrow\underline B)\) の function domain に置く宣言は拒否する。
declaration name と constructor name は declaration environment 内で
一意とする。

各 Program datatype 宣言と同時に、Set 側へ名前付きの鏡像
\(I^s\) と constructor \(C_i^s\) を生成する。
これらの type parameter は \(\operatorname{RfType}(\vec A)\) の形に限る。

### Program reduction

\[
\operatorname{case}^v
\left(C_i^v[\vec A](\vec V);\overline{C_j^v(\vec x_j^v)\mapsto M_j}\right)
\Rightarrow_c
M_i[\vec x_i^v:=\vec V].
\]

### Program constructor と case

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| inductive type form | \(\Gamma\vdash I^v(\vec A)\ \mathsf{vtype}\) | \(\Gamma\vdash A_\ell\ \mathsf{vtype}\) for all \(\ell\) | \(I^v\) は well-formed な declaration |
| constructor intro | \(\Gamma\vdash_v C_i^v[\vec A](\vec V):I^v(\vec A)\) | \(\Gamma\vdash_vV_j:A_{ij}[\vec X:=\vec A]\) for all \(j\) | |
| case | \(\Gamma\vdash_c\operatorname{case}^v\left(V;\overline{C_i^v(\vec x_i^v)\mapsto M_i}\right):\underline B\) | \(\Gamma\vdash_vV:I^v(\vec A)\)<br>\(\Gamma,\vec x_i^v:\vec A_i[\vec X:=\vec A]:\mathsf{value}\vdash_cM_i:\underline B\) for all \(i\) | 各 constructor の branch がちょうど一つ<br>branch binder は fresh |

### Set の鏡像と reflection

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| reflected inductive type form | \(\Gamma\vdash I^s(\operatorname{RfType}(\vec A)):*^s_0\) | \(\Gamma\vdash A_\ell\ \mathsf{vtype}\) for all \(\ell\) | \(I^v\) は well-formed な declaration |
| reflected constructor intro | \(\Gamma\vdash C_i^s[\operatorname{RfType}(\vec A)](\vec t):I^s(\operatorname{RfType}(\vec A)):*^s_0\) | \(\Gamma\vdash A_\ell\ \mathsf{vtype}\) for all \(\ell\)<br>\(\Gamma\vdash t_j:\operatorname{RfType}(A_{ij}[\vec X:=\vec A]):*^s_0\) for all \(j\) | |

\[
\operatorname{RfType}(I^v(\vec A))
\Rightarrow_s
I^s(\operatorname{RfType}(\vec A)).
\tag{Rf-Ind}
\]

\[
\begin{aligned}
&
\operatorname{RfTerm}_{I^v(\vec A)}
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

Set case と induction は declaration から生成される通常の規則を持つ。

### case と run への elaboration

Type 側の構造再帰を surface syntax として提供する場合も、core では
case と run へ elaboration する。再帰呼び出し後に処理を続ける定義や
複数の recursive field を処理する定義では、Program state に
未処理の field、途中結果、defunctionalize した continuation stack を
含める。

elaboration が生成する step function は case で state の外側を一層だけ
観察し、continue で次状態を返す。Set/Prop 側では reflected datatype の
induction や tree height を用いて、その step relation に対する Acc proof
を生成する。

## 課題
- datatype declaration environment の well-formedness と positivity 判定
- Set の鏡像に対する case と induction の raw syntax、typing、reduction の生成規則
- inductive type や record を定義する際に気を付けるのは、dependent sum type と W-type にしたときの大きさ
    - 基本的には \(\mathcal{R}\) と同じものを使ってよい。
    - impredicative にならないように、\((*^s, *^p, *^s) \in \mathcal{R}\) にすること。
        - これが必要になるのはおかしい気がする（subtype で対応するべきだから。）。
- judgement を stratified（\(\Gamma \vdash^s t: T\)）にしなくてもいいのでは...
- \(\Ty\) を2引数にしない場合
    - \(\Ty(A, B)\) の代わりに \(t: \Ty B\) と \(B: \Power A\) を premise に入れる。
- take elim prop の set-theoretic な意味は、普通に \(\bullet \in \lbrack T \rbrack\) への map になっているということ？
    - take elim は \(X: *^p\) なら cut elimination に見える。
- reduction の仮定にあらわれる合同性について：
    - Pred: \(\Pred (A, \{x: B \mid P\}, t) \Rightarrow_s (\lambda x: B. P) @ t\) としたが、同値関係としての \(\beta\) を定めるときには、\(\Pred (A, \{x: B \mid P\}, t) \cong (\lambda x: B. P) @ t\) if \(A \cong B\) のようにしてもいいかも。
    - Rf-U-App、Rf-C-App と二つの runCase rule は、重複する annotation を同じ metavariable にせず左線形にした。well-typed な source に必要な component の convertibility は generation から回収する。

### CBPV

上の節で raw syntax、context、judgement、reduction、typing rule の核は定まる。
完全な形式体系として閉じるためには、さらに次を固定する必要がある。

- mixed context に対する renaming、weakening、substitution
- Program type/value/computation category の一意性
- PTS reduction と reflection reduction の全 evaluation context
- Rf-Thunk、Rf-U-App、Rf-C-App、Rf-Ind、Rf-Ctor の critical-pair analysis
- PTS と Program の subject reduction
- RunInv の reduction と substitution による保存
- Acc-Descent と run/runCase の model soundness
- 妥当な closing substitution に相対化した Program normalization

特に、偽の Acc assumption を含む open context では停止しない run を型付けできる可能性がある。
停止定理は空 context、または assumption が意味論的に妥当な closing substitution に相対化する。
