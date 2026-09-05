# 体系について
とりあえず、現在考えている core calculus をここにまとめる。
ただし、まだ定義できていない部分は載ってない。

体系は Set/Prop を記述する PTS 部分と、CBPV に基づく Program 部分からなる。
両者は別の構文、context、judgement を持つ。
Reflection は Program の raw 構文から Set/Prop の構文へのメタレベルの写像とする。
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
    - \(\{(s, s', s') \mid s \in \{* ^s_i, \sq^s_i\}, s' \in \{* ^p, \sq ^p\} \}\) ... \(* ^s\) についての命題を用意するため。

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
    - 停止性付き再帰
        | category | definition |
        | --- | --- |
        | run step type | \(\operatorname{RunStep}(t,t)\) |
        | continue | \(\operatorname{continue}_{t,t}(t)\) |
        | finish | \(\operatorname{finish}_{t,t}(t)\) |
        | run step recursor | \(\operatorname{prec}_{\operatorname{RunStep}(t,t)}(t,t,t,t)\) |
        | accessibility | \(\operatorname{Acc}_{t,t}(t,t)\) |
        | run | \(\operatorname{run}_{t,t}(t,t)\) |
        | run case | \(\operatorname{runCase}_{t,t}(t,t,t)\) |
    - Boxed Program
        | category | definition |
        | --- | --- |
        | boxed Program type | \(\operatorname{Box}(P)\) |
        | boxed Program | \(\operatorname{box}_P(p)\) |
        | force boxed Program | \(\operatorname{Force}_P(t)\) |
        | boxed application | \(t@^{\operatorname{Box}}t\) |
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

#### Set/Prop

- context: \(\Gamma=\)
    | category | definition |
    | --- | --- |
    | empty context | \(\emptyset\) |
    | PTS concat | \(\Gamma, x^s:t:s\) |

- judgement:
    | category | definition |
    | --- | --- |
    | well formed context | \(\operatorname{WF}(\Gamma)\) |
    | PTS sorting | \(\Gamma\vdash t:s\) |
    | PTS typing | \(\Gamma\vdash t:T:s\) |
    | provable | \(\Gamma\vDash P\) |

#### Program

- context: \(\Delta=\)
    | category | definition |
    | --- | --- |
    | empty context | \(\emptyset\) |
    | Program type concat | \(\Delta,X:\mathsf{vtype}\) |
    | Program value concat | \(\Delta,x^v:A:\mathsf{value}\) |

- judgement:
    | category | definition |
    | --- | --- |
    | well formed context | \(\operatorname{WF}_v(\Delta)\) |
    | value type formation | \(\Delta\vdash A\ \mathsf{vtype}\) |
    | computation type formation | \(\Delta\vdash\underline B\ \mathsf{ctype}\) |
    | value typing | \(\Delta\vdash_vV:A\) |
    | computation typing | \(\Delta\vdash_cM:\underline B\) |
    | well-terminated value | \(\Delta\Vdash_vV:A\) |
    | well-terminated computation | \(\Delta\Vdash_cM:\underline B\) |

## reduction

### Set/Prop

\(\Rightarrow_s\) は通常の Lambda 項の reduction と次の root rule の compatible closure とする。

\[
\Pred (A, \{x^s: B \mid P\}, t)
\Rightarrow_s
(\lambda x^s: B. P) @ t.
\]

\[
\begin{aligned}
\operatorname{prec}_{\operatorname{RunStep}(A,B)}
(P,c,d,\operatorname{continue}_{A,B}(a))
&\Rightarrow_s c@a,\\
\operatorname{prec}_{\operatorname{RunStep}(A,B)}
(P,c,d,\operatorname{finish}_{A,B}(b))
&\Rightarrow_s d@b,\\
\operatorname{run}_{A,B}(f,a)
&\Rightarrow_s
\operatorname{runCase}_{A,B}(f,a,f@a),\\
\operatorname{runCase}_{A,B}
(f,a,\operatorname{continue}_{A,B}(a'))
&\Rightarrow_s\operatorname{run}_{A,B}(f,a'),\\
\operatorname{runCase}_{A,B}
(f,a,\operatorname{finish}_{A,B}(b))
&\Rightarrow_s b.
\end{aligned}
\]

#### Boxed Program

| category | reduction | other |
| --- | --- | --- |
| box step | \(\operatorname{box}_{\underline B}(M)\Rightarrow_s\operatorname{box}_{\underline B}(M')\) | \(M\Rightarrow_cM'\) |
| force box | \(\operatorname{Force}_P(\operatorname{box}_P(r))\Rightarrow_s\operatorname{RfTerm}(r)\) | \(\emptyset\vdash_Pr:P\)<br>\(\nexists r'.\ r\Rightarrow_cr'\) |
| boxed application | \(\operatorname{box}_{A\Rightarrow\underline B}(M)@^{\operatorname{Box}}\operatorname{box}_A(V)\Rightarrow_s\operatorname{box}_{\underline B}(M@^cV)\) | |

\[
C_{\operatorname{Box}}::=
[\,]
\mid\operatorname{Force}_P(C_{\operatorname{Box}})
\mid C_{\operatorname{Box}}@^{\operatorname{Box}}t
\mid t@^{\operatorname{Box}}C_{\operatorname{Box}}.
\]

\[
t\Rightarrow_st'
\quad\Longrightarrow\quad
C_{\operatorname{Box}}[t]\Rightarrow_sC_{\operatorname{Box}}[t'].
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

#### RunStep

ここで \(k=\max(i,j)\) とする。

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| run step form | \(\Gamma\vdash\operatorname{RunStep}(A,B):*^s_k\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash B:*^s_j\) | |
| continue intro | \(\Gamma\vdash\operatorname{continue}_{A,B}(a):\operatorname{RunStep}(A,B):*^s_k\) | \(\Gamma\vdash a:A:*^s_i\)<br>\(\Gamma\vdash B:*^s_j\) | |
| finish intro | \(\Gamma\vdash\operatorname{finish}_{A,B}(b):\operatorname{RunStep}(A,B):*^s_k\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash b:B:*^s_j\) | |
| prec | \(\Gamma\vdash\operatorname{prec}_{\operatorname{RunStep}(A,B)}(P,c,d,r):P[x:=r]:s\) | \(\Gamma\vdash r:\operatorname{RunStep}(A,B):*^s_k\)<br>\(\Gamma,x:\operatorname{RunStep}(A,B):*^s_k\vdash P:s\)<br>\(\Gamma\vdash c:(a:A)\to P[x:=\operatorname{continue}_{A,B}(a)]:s_c\)<br>\(\Gamma\vdash d:(b:B)\to P[x:=\operatorname{finish}_{A,B}(b)]:s_d\) | 各 product は \(\mathcal R\) により形成可能 |

#### Acc と run

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| acc form | \(\Gamma\vdash\operatorname{Acc}_{A,B}(f,a):*^p\) | \(\Gamma\vdash f:A\to\operatorname{RunStep}(A,B):*^s_k\)<br>\(\Gamma\vdash a:A:*^s_i\) | |
| acc intro | \(\Gamma\vDash\operatorname{Acc}_{A,B}(f,a)\) | \(\Gamma\vdash f:A\to\operatorname{RunStep}(A,B):*^s_k\)<br>\(\Gamma\vdash a:A:*^s_i\)<br>\(\Gamma,b:A:*^s_i\vDash(f@a=\operatorname{continue}_{A,B}(b))\to\operatorname{Acc}_{A,B}(f,b)\) | |
| acc descent | \(\Gamma\vDash\operatorname{Acc}_{A,B}(f,b)\) | \(\Gamma\vDash\operatorname{Acc}_{A,B}(f,a)\)<br>\(\Gamma\vDash f@a=\operatorname{continue}_{A,B}(b)\) | |
| run | \(\Gamma\vdash\operatorname{run}_{A,B}(f,a):B:*^s_j\) | \(\Gamma\vdash f:A\to\operatorname{RunStep}(A,B):*^s_k\)<br>\(\Gamma\vdash a:A:*^s_i\)<br>\(\Gamma\vDash\operatorname{Acc}_{A,B}(f,a)\) | |
| run case | \(\Gamma\vdash\operatorname{runCase}_{A,B}(f,a,r):B:*^s_j\) | \(\Gamma\vdash f:A\to\operatorname{RunStep}(A,B):*^s_k\)<br>\(\Gamma\vdash a:A:*^s_i\)<br>\(\Gamma\vdash r:\operatorname{RunStep}(A,B):*^s_k\)<br>\(\Gamma\vDash\operatorname{Acc}_{A,B}(f,a)\)<br>\(\Gamma\vDash f@a=r\) | |

### Program

#### Program context と type formation

\(\Delta\vdash_PJ\) は value type formation、computation type formation、
value typing、computation typing のいずれか一つを表す。

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| empty | \(\operatorname{WF}_v(\emptyset)\) | | |
| value type start | \(\operatorname{WF}_v(\Delta,X:\mathsf{vtype})\) | \(\operatorname{WF}_v(\Delta)\) | \(X\notin\Delta\) |
| value type variable | \(\Delta,X:\mathsf{vtype}\vdash X\ \mathsf{vtype}\) | \(\operatorname{WF}_v(\Delta,X:\mathsf{vtype})\) | |
| value start | \(\operatorname{WF}_v(\Delta,x^v:A:\mathsf{value})\) | \(\operatorname{WF}_v(\Delta)\)<br>\(\Delta\vdash A\ \mathsf{vtype}\) | \(x^v\notin\Delta\) |
| Program weak | \(\Delta,e\vdash_PJ\) | \(\Delta\vdash_PJ\)<br>\(\operatorname{WF}_v(\Delta,e)\) | \(J\) の自由変数を capture しない |
| \(\text{F}\) form | \(\Delta\vdash \text{F} A\ \mathsf{ctype}\) | \(\Delta\vdash A\ \mathsf{vtype}\) | |
| \(\text{U}\) form | \(\Delta\vdash \text{U}\underline B\ \mathsf{vtype}\) | \(\Delta\vdash\underline B\ \mathsf{ctype}\) | |
| function form | \(\Delta\vdash A\Rightarrow\underline B\ \mathsf{ctype}\) | \(\Delta\vdash A\ \mathsf{vtype}\)<br>\(\Delta\vdash\underline B\ \mathsf{ctype}\) | |
| run step form | \(\Delta\vdash\operatorname{RunStep}(A,B)\ \mathsf{vtype}\) | \(\Delta\vdash A\ \mathsf{vtype}\)<br>\(\Delta\vdash B\ \mathsf{vtype}\) | |

#### Program typing

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| value variable | \(\Delta,x^v:A:\mathsf{value}\vdash_vx^v:A\) | \(\operatorname{WF}_v(\Delta,x^v:A:\mathsf{value})\) | |
| return | \(\Delta\vdash_c\operatorname{return}(V):\text{F} A\) | \(\Delta\vdash_vV:A\) | |
| thunk | \(\Delta\vdash_v\operatorname{thunk}(M):\text{U}\underline B\) | \(\Delta\vdash_cM:\underline B\) | |
| force | \(\Delta\vdash_c\operatorname{force}(V):\underline B\) | \(\Delta\vdash_vV:\text{U}\underline B\) | |
| function intro | \(\Delta\vdash_c\lambda x^v:A.M:A\Rightarrow\underline B\) | \(\Delta,x^v:A:\mathsf{value}\vdash_cM:\underline B\) | \(x^v\notin\Delta\) |
| function elim | \(\Delta\vdash_cM @^c V:\underline B\) | \(\Delta\vdash_cM:A\Rightarrow\underline B\)<br>\(\Delta\vdash_vV:A\) | |
| sequence | \(\Delta\vdash_c M\ \operatorname{to}\ x^v:A\ \operatorname{in}\ N:\underline B\) | \(\Delta\vdash_cM:\text{F} A\)<br>\(\Delta,x^v:A:\mathsf{value}\vdash_cN:\underline B\) | \(x^v\notin\Delta\) |
| value let | \(\Delta\vdash_c\operatorname{let}^v x^v=V\ \operatorname{in}\ N:\underline B\) | \(\Delta\vdash_vV:A\)<br>\(\Delta,x^v:A:\mathsf{value}\vdash_cN:\underline B\) | \(x^v\notin\Delta\) |
| continue intro | \(\Delta\vdash_v\operatorname{continue}_{A,B}(a):\operatorname{RunStep}(A,B)\) | \(\Delta\vdash_v a:A\)<br>\(\Delta\vdash B\ \mathsf{vtype}\) | |
| finish intro | \(\Delta\vdash_v\operatorname{finish}_{A,B}(b):\operatorname{RunStep}(A,B)\) | \(\Delta\vdash A\ \mathsf{vtype}\)<br>\(\Delta\vdash_v b:B\) | |
| run | \(\Delta\vdash_c\operatorname{run}_{A,B}(f,a):\text{F}B\) | \(\Delta\vdash_vf:\text{U}(A\Rightarrow\text{F}(\operatorname{RunStep}(A,B)))\)<br>\(\Delta\vdash_va:A\) | |
| run case | \(\Delta\vdash_c\operatorname{runCase}_{A,B}(f,a,M):\text{F}B\) | \(\Delta\vdash_vf:\text{U}(A\Rightarrow\text{F}(\operatorname{RunStep}(A,B)))\)<br>\(\Delta\vdash_va:A\)<br>\(\Delta\vdash_cM:\text{F}(\operatorname{RunStep}(A,B))\) | |

#### Reflection

##### Meta-level maps

\[
\begin{aligned}
\operatorname{RfType}&:\mathsf{ProgramTypeSyntax}
\longrightarrow\mathsf{SetTermSyntax},\\
\operatorname{RfTerm}&:\mathsf{ProgramTermSyntax}
\longrightarrow\mathsf{SetTermSyntax}.
\end{aligned}
\]

##### Type and context

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
(\operatorname{RfType}(A),\operatorname{RfType}(B)),\\[4pt]
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

##### Value

\[
\begin{aligned}
\operatorname{RfTerm}(x^v)
&:=x^{*^s_0},
\\
\operatorname{RfTerm}(\operatorname{thunk}(M))
&:=\operatorname{RfTerm}(M),
\\
\operatorname{RfTerm}(\operatorname{continue}_{A,B}(a))
&:=
\operatorname{continue}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}
(\operatorname{RfTerm}(a)),
\\
\operatorname{RfTerm}(\operatorname{finish}_{A,B}(b))
&:=
\operatorname{finish}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}(\operatorname{RfTerm}(b)).
\end{aligned}
\]

##### Computation

\[
\begin{aligned}
\operatorname{RfTerm}(\operatorname{return}(V))
&:=\operatorname{RfTerm}(V),
\\
\operatorname{RfTerm}(\operatorname{force}(V))
&:=\operatorname{RfTerm}(V),
\\
\operatorname{RfTerm}(\lambda x^v:A.M)
&:=
\lambda x^{*^s_0}:\operatorname{RfType}(A).
\operatorname{RfTerm}(M),
\\
\operatorname{RfTerm}(M@^cV)
&:=
\operatorname{RfTerm}(M)
@\operatorname{RfTerm}(V),
\\
\operatorname{RfTerm} (M\ \operatorname{to}\ x^v:A\ \operatorname{in}\ N)
&:=
(\lambda x^{*^s_0}:\operatorname{RfType}(A).
\operatorname{RfTerm}(N)) @ \operatorname{RfTerm}(M),
\\
\operatorname{RfTerm}(\operatorname{let}^v x^v=V\ \operatorname{in}\ N)
&:=
(\lambda x^{*^s_0}:\operatorname{RfType}(A).
\operatorname{RfTerm}(N)) @ \operatorname{RfTerm}(V),
\\
\operatorname{RfTerm}(\operatorname{run}_{A,B}(f,a))
&:=
\operatorname{run}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}
\left( \operatorname{RfTerm}(f), \operatorname{RfTerm}(a) \right),
\\
\operatorname{RfTerm}
(\operatorname{runCase}_{A,B}(f,a,M))
&:=
\operatorname{runCase}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}
\left(
\operatorname{RfTerm}(f),
\operatorname{RfTerm}(a),
\operatorname{RfTerm}(M)
\right).
\end{aligned}
\]

#### Well-termination

\[
\begin{aligned}
\Delta\Vdash_vV:A
\quad:\Longleftrightarrow\quad
&\Delta\vdash_vV:A\\
&\land
\operatorname{RfCtx}(\Delta)\vdash
\operatorname{RfTerm}(V):\operatorname{RfType}(A):*^s_0,\\[4pt]
\Delta\Vdash_cM:\underline B
\quad:\Longleftrightarrow\quad
&\Delta\vdash_cM:\underline B\\
&\land
\operatorname{RfCtx}(\Delta)\vdash
\operatorname{RfTerm}(M):
\operatorname{RfType}(\underline B):*^s_0.
\end{aligned}
\]

### Boxed Program

#### Judgement abbreviations

| \(P\) | \(p\) | \(\emptyset\vdash P\ \mathsf{ptype}\) | \(\emptyset\vdash_Pp:P\) | \(\emptyset\Vdash p:P\) |
| --- | --- | --- | --- | --- |
| \(A\) | \(V\) | \(\emptyset\vdash A\ \mathsf{vtype}\) | \(\emptyset\vdash_vV:A\) | \(\emptyset\Vdash_vV:A\) |
| \(\underline B\) | \(M\) | \(\emptyset\vdash\underline B\ \mathsf{ctype}\) | \(\emptyset\vdash_cM:\underline B\) | \(\emptyset\Vdash_cM:\underline B\) |

#### Typing

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| box type | \(\Gamma\vdash\operatorname{Box}(P):*^s_0\) | \(\operatorname{WF}(\Gamma)\)<br>\(\emptyset\vdash P\ \mathsf{ptype}\) | |
| box intro | \(\Gamma\vdash\operatorname{box}_P(p):\operatorname{Box}(P):*^s_0\) | \(\operatorname{WF}(\Gamma)\)<br>\(\emptyset\Vdash p:P\) | |
| force box | \(\Gamma\vdash\operatorname{Force}_P(b):\operatorname{RfType}(P):*^s_0\) | \(\Gamma\vdash b:\operatorname{Box}(P):*^s_0\) | |
| boxed application | \(\Gamma\vdash f@^{\operatorname{Box}}a:\operatorname{Box}(\underline B):*^s_0\) | \(\Gamma\vdash f:\operatorname{Box}(A\Rightarrow\underline B):*^s_0\)<br>\(\Gamma\vdash a:\operatorname{Box}(A):*^s_0\) | |

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
鏡像の type parameter は通常の Set variable とする。
Program field type \(A_{ij}\) の鏡像 \(A^s_{ij}\) は、
\(\operatorname{RfType}(A_{ij})\) に現れる
\(\operatorname{RfType}(X_\ell)\) を対応する Set variable
\(X^s_\ell\) で置き換えたものとする。

\[
\begin{aligned}
I^s(X^s_1:*^s_0,\ldots,X^s_n:*^s_0)&:*^s_0,\\
C_i^s&:
A^s_{i1}\to\cdots\to A^s_{ik_i}\to I^s(\vec X^s).
\end{aligned}
\]

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
| inductive type form | \(\Delta\vdash I^v(\vec A)\ \mathsf{vtype}\) | \(\Delta\vdash A_\ell\ \mathsf{vtype}\) for all \(\ell\) | \(I^v\) は well-formed な declaration |
| constructor intro | \(\Delta\vdash_v C_i^v[\vec A](\vec V):I^v(\vec A)\) | \(\Delta\vdash_vV_j:A_{ij}[\vec X:=\vec A]\) for all \(j\) | |
| case | \(\Delta\vdash_c\operatorname{case}^v\left(V;\overline{C_i^v(\vec x_i^v)\mapsto M_i}\right):\underline B\) | \(\Delta\vdash_vV:I^v(\vec A)\)<br>\(\Delta,\vec x_i^v:\vec A_i[\vec X:=\vec A]:\mathsf{value}\vdash_cM_i:\underline B\) for all \(i\) | 各 constructor の branch がちょうど一つ<br>branch binder は fresh |

### Set の鏡像と reflection

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| reflected inductive type form | \(\Gamma\vdash I^s(\vec S):*^s_0\) | \(\Gamma\vdash S_\ell:*^s_0\) for all \(\ell\) | \(I^v\) は well-formed な declaration |
| reflected constructor intro | \(\Gamma\vdash C_i^s[\vec S](\vec t):I^s(\vec S):*^s_0\) | \(\Gamma\vdash S_\ell:*^s_0\) for all \(\ell\)<br>\(\Gamma\vdash t_j:A^s_{ij}[\vec X^s:=\vec S]:*^s_0\) for all \(j\) | |

\[
\operatorname{RfType}(I^v(\vec A))
:=
I^s(\operatorname{RfType}(\vec A)).
\]

\[
\begin{aligned}
&
\operatorname{RfTerm}
\left(C_i^v[\vec A](\vec V)\right)\\
&\qquad:=
C_i^s[\operatorname{RfType}(\vec A)]
\left(
\overrightarrow{
\operatorname{RfTerm}(V_j)
}
\right).
\end{aligned}
\]

Program case は Set case へ写す。

\[
\begin{aligned}
&\operatorname{RfTerm}
\left(
\operatorname{case}^v
(V;\overline{C_i^v(\vec x_i^v)\mapsto M_i})
\right)\\
&\qquad:=
\operatorname{case}^s
\left(
\operatorname{RfTerm}(V);
\overline{
C_i^s(\vec x_i^{*^s_0})
\mapsto\operatorname{RfTerm}(M_i)
}
\right).
\end{aligned}
\]

Set case と induction は declaration から生成される通常の規則を持つ。

### case と run への elaboration

Program 側の構造再帰を surface syntax として提供する場合、core では
case を使う一段の step function へ elaboration する。再帰呼び出し後に処理を続ける定義や
複数の recursive field を処理する定義では、Program state に
未処理の field、途中結果、defunctionalize した continuation stack を
含める。

elaboration が生成する Program step function は case で state の外側を一層だけ
観察し、continue で次状態を返す。Reflection によって得られる Set step
function に対して Acc proof を構成し、Set の run を適用する。

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
