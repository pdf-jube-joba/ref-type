# 体系について
とりあえず、現在考えている core calculus をここにまとめる。
ただし、まだ定義できていない部分は載ってない。

## Sort
purr type system のような形で \(S, A, R\) の組を次のように定義する。
以降は特別に書かない限り \(i \in \mathbb{N}\) とする。

- \(\mathcal{S} = \{*^s_{i}, \sq^s_{i} \mid i \in \mathbb{N}\} \cup \{*^p, \sq^p\} \cup \{*^t, \sq^t\}\)
    - \(*^s_{i}, \sq^s_{i}\) は set 用の sort
    - \(*^p, \sq^p\) は proposition 用の sort
    - \(*^t, \sq^t\) は compute 用の sort
- \(\mathcal{A} = \{(*^s_{i}, \sq^s_{i})\} \cup \{(*^p, \sq^p)\} \cup \{(*^t, \sq^t)\}\)
- \(\mathcal{R} =\) union of
    - \(\{(*^s_i, *^s_j, *^s_{\max(i,j)}), (*^s_i, \sq^s_j, \sq^s_{\max(i,j)}), (\sq^s_i, \sq^s_j, \sq^s_{\max(i,j)})\}\) ... universe level の異なる dependent product は最小の共通 level に置く
    - \(\{(\sq^s_i, *^s_j, *^s_{\max(i+1,j)})\}\) ... universe 自身を走る場合だけ domain 側の level を一つ上げる
    - \(\{(*^p, *^p, *^p), (\sq^p, *^p, *^p), (\sq^p, \sq^p, \sq^p)\}\) ... \(*^p\) は impredicative だけど依存型のような \((*^p, \sq^p, \sq^p)\) はない。
    - \(\{(*^s_i, *^p, *^p), (*^s_i, \sq^p, \sq^p)\}\) ... \(*^s\) についての命題を用意するため。
    - \(\{(*^t, *^t, *^t)\}\)

普通の変数を \(x\) とする。
\(s\) や \(s_i\) は \(\mathcal{S}\) の元とする。

> [!note]
> - 変数に sort をつけて \(x^s\) にする
> - typing に sort をつける

\[
\begin{aligned}
\operatorname{FV}(t)
&\subseteq
\{x^s\mid x\in\operatorname{Name},\ s\in\mathcal S\},\\
\operatorname{Names}(V)
&:=
\{x\mid\exists s.\ x^s\in V\}.
\end{aligned}
\]

## Term, Context, Judgement
（2つあるものは、別の書き方として用意している。）

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
        | equality type | \( t = t\) |
        | existence | \(\exists t\) |
        | take operator | \(\Take(X,T,f)\) |
    - 一般再帰に関する項
        | category | definition |
        | --- | --- |
        | run step type | \(\operatorname{RunStep}(A,B)\) |
        | continue | \(\operatorname{continue}_{A,B}(a)\) |
        | finish | \(\operatorname{finish}_{A,B}(b)\) |
        | accessibility | \(\operatorname{Acc}_{A,B}(f,a)\) |
        | run | \(\operatorname{run}_{A,B}(f,a)\) |
        | run case | \(\operatorname{runCase}_{A,B}(f,a,u)\) |
        | type reflection | \(\operatorname{RfType}(A)\) |
        | term reflection | \(\operatorname{RfTerm}_A(m)\) |
- context: \(\Gamma=\)
    | category | definition |
    | --- | --- |
    | empty context | \(\emptyset\) |
    | concat | \(\Gamma, x:t:s\) |
- judgement:
    | category | definition |
    | --- | --- |
    | well formed context | \(\text{WF}(\Gamma)\) |
    | sorting | \(\Gamma \vdash t: s\) |
    | typing | \(\Gamma \vdash t: t: s\) |
    | provable  | \(\Gamma \vDash t\) |

### 略記

\[
\begin{aligned}
\operatorname{continueFun}_{A,B}
&:=
\lambda z^{*^t}:A.\operatorname{continue}_{A,B}(z^{*^t})
:
A\to\operatorname{RunStep}(A,B),\\
\operatorname{Terminates}_{A,B}(f,a)
&:=
\operatorname{Acc}_{A,B}
\left(f,\operatorname{RfTerm}_A(a)\right),\\
\operatorname{RunInv}_{A,B}(f,a,u)
&:=
\operatorname{RfTerm}_{\operatorname{RunStep}(A,B)}(f@a)
=
\operatorname{RfTerm}_{\operatorname{RunStep}(A,B)}(u).
\end{aligned}
\]

## reduction
\(\Rightarrow\) は通常の Lambda 項の reduction と次の root rule の compatible closure とする。

### subset

\[
\Pred (A, \{x: B \mid P\}, t)
\Rightarrow
(\lambda x: B. P) @ t.
\]

### reflection

\[
\begin{aligned}
\operatorname{RfType}((x^{*^t}:A)\to B)
&\Rightarrow
(z^{*^s_0}:\operatorname{RfType}(A))
\to\operatorname{RfType}(B)
\qquad
\left(
  x^{*^t}\notin\operatorname{FV}(B),
  z\notin\operatorname{Names}(\operatorname{FV}(A)\cup\operatorname{FV}(B))
\right),\\
\operatorname{RfTerm}_{A\to B}(f)
@\operatorname{RfTerm}_C(a)
&\Rightarrow
\operatorname{RfTerm}_B(f@a).
\end{aligned}
\]

### recursion

\[
\begin{aligned}
\operatorname{run}_{A,B}(f,a)
&\Rightarrow
\operatorname{runCase}_{A,B}(f,a,f@a),\\
\operatorname{runCase}_{A,B}
(f,a,\operatorname{continue}_{C,D}(a'))
&\Rightarrow
\operatorname{run}_{A,B}(f,a'),\\
\operatorname{runCase}_{A,B}
(f,a,\operatorname{finish}_{C,D}(b))
&\Rightarrow b.
\end{aligned}
\]

後二規則の target には外側の `runCase` の parameter `A,B` を使う。well-typed な source では
generation と conversion から `A≡C`、`B≡D` が従う。外側を選べば、`f` の domain、
再帰先の termination predicate、`runCase` 全体の result type を変換せずに保てる。

### definitional equality

\[
\equiv\;:=\;(\Rightarrow\cup\Leftarrow)^*.
\]

## derivation
### pure type system 部分
PTS とは書いているが、普通のとは違って stratified されています。

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| empty | \(\text{WF}(\emptyset)\) | | |
| axiom | \(\emptyset \vdash s_1: s_2\) | | \(s_1,s_2\in\mathcal{S}\)<br>\((s_1, s_2) \in \mathcal{A}\) |
| start | \(\text{WF}(\Gamma::(x: t: s))\) | \(\text{WF}(\Gamma)\), <br> \(\Gamma \vdash t: s\) | \(x\in\operatorname{Name}\)<br>\(s\in\mathcal{S}\)<br>\(x \notin \Gamma\) |
| weak sort | \(\Gamma :: (x: t: s) \vdash t_1: s'\) | \(\Gamma \vdash t_1: s'\) <br> \(\text{WF}(\Gamma :: (x: t: s))\) | \(x\in\operatorname{Name}\)<br>\(s,s'\in\mathcal{S}\)<br>\(x \notin \Gamma\) |
| weak type | \(\Gamma :: (x: t: s) \vdash t_1: t_2: s\) | \(\Gamma \vdash t_1: t_2: s\) <br> \(\text{WF}(\Gamma :: (x: t: s))\) | \(x\in\operatorname{Name}\)<br>\(s\in\mathcal{S}\)<br>\(x \notin \Gamma\) |
| variable | \(\Gamma :: (x: t: s) \vdash x^s: t: s\) | \(\text{WF}(\Gamma :: (x: t: s))\) | \(x\in\operatorname{Name}\)<br>\(s\in\mathcal{S}\) |
| conversion | \(\Gamma \vdash t: T_2: s\) | \(\Gamma \vdash t: T_1: s\) <br> \(\Gamma \vdash T_2: s\) | \(s\in\mathcal{S}\)<br>\(T_1 \equiv T_2\) |
| dep form | \(\Gamma \vdash (\Pi x^{s_1}:t. T): s_3\) | \(\Gamma \vdash t: s_1\) <br> \(\Gamma:: (x: t: s_1) \vdash T: s_2\) | \(x\in\operatorname{Name}\)<br>\(s_1,s_2,s_3\in\mathcal{S}\)<br>\((s_1, s_2, s_3) \in \mathcal{R}\) <br> \(x \notin \Gamma \) |
| dep intro | \(\Gamma \vdash (\lambda x^{s_1}:t.m): (\Pi x^{s_1}:t.M) : s_3\) | \(\Gamma \vdash (\Pi x^{s_1}:t. M): s_3\) <br> \(\Gamma:: (x:t: s_1) \vdash m: M: s_2\) | \(x\in\operatorname{Name}\)<br>\(s_1,s_2,s_3\in\mathcal{S}\)<br>\(x \notin \Gamma\) |
| dep elim | \(\Gamma \vdash (f @ a): T[x := a]: s_2\) | \(\Gamma \vdash f: (\Pi x^{s_1}: t. T): s_3\) <br> \(\Gamma \vdash a: t: s_1\) | \(x\in\operatorname{Name}\)<br>\(s_1,s_2,s_3\in\mathcal{S}\) |
| type elem | \(\Gamma \vdash A: s: t\) | \(\Gamma \vdash A: s\), \(\Gamma \vdash s: t\) | \(s,t\in\mathcal{S}\) |
| type sort | \(\Gamma \vdash A: s\) | \(\Gamma \vdash A: s: t\) | \(s,t\in\mathcal{S}\) |

### provable
| category | conclusion | premises | other |
| --- | --- | --- | --- |
| provable | \(\Gamma \vDash P \) | \(\Gamma \vdash p: P: *^p\) | |
| proof term | \(\Gamma \vdash \Proof P: P: *^p\) | \(\Gamma \vDash P\) | |

### power set, subset
ここで出てくる \(*^s\) は全部 \(i\) を同じにする。
| category | conclusion | premises | other |
| --- | --- | --- | --- |
| power set form | \(\Gamma \vdash \Power A: *^s\) | \(\Gamma \vdash A: *^s\) | |
| power set intro | \(\Gamma \vdash \Ty (A, B): *^s\) | \(\Gamma \vdash B: \Power A: *^s\) | |
| predicate | \(\Gamma \vdash \Pred (A, B, t): *^p\) | \(\Gamma \vdash B: \Power A: *^s\) <br> \(\Gamma \vdash t: A: *^s\) | |
| subset form | \(\Gamma \vdash \{x^{*^s}: A \mid P\}: \Power A: *^s\) | \(\Gamma \vdash A: *^s, \Gamma:: x: A: *^s \vdash P: *^p\) | \(x\in\operatorname{Name}\) |
| subset intro | \(\Gamma \vdash t : \Ty (A, B) : *^s\) | \(\Gamma \vdash B : \Power A : *^s, \\ \Gamma \vdash t: A: *^s, \Gamma \vDash \Pred (A, B, t)\) | |
| subset weak | \(\Gamma \vdash t: A: *^s\) | \(\Gamma \vdash t: \Ty (A, B): *^s\) | |
| susbet prop | \(\Gamma \vDash \Pred(A, B, t)\) | \(\Gamma \vdash t: \Ty (A, B): *^s\) | |

### equality
| category | conclusion | premises | other |
| --- | --- | --- | --- |
| id form | \(\Gamma \vdash a = b: *^p\) | \(\Gamma \vdash a: A: *^s, \Gamma \vdash b: A: *^s\) | |
| id intro | \(\Gamma \vDash a = a\) | \(\Gamma \vdash a: A: *^s\) | |
| id elim | \(\Gamma \vDash (\lambda x: A. P) @ b\) | \(\Gamma \vdash a: A: *^s, \Gamma \vdash b: A: *^s, \\ \Gamma \vDash a = b, \\ \Gamma::(x: A: *^s) \vdash P: *^p \\ \Gamma \vDash (\lambda x: A. P) @ a\) | \(x\in\operatorname{Name}\) |

### choice
| category | conclusion | premises | other |
| --- | --- | --- | --- |
| exists form | \(\Gamma \vdash (\exists t): *^p\) | \(\Gamma \vdash t: *^s\) | |
| exists intro | \(\Gamma \vDash \exists t\) | \(\Gamma \vdash e : t : *^s\) | |
| take elim set | \(\Gamma \vdash \Take(X,T,f): T: *^s\) | \(\Gamma \vdash X: *^s, \Gamma \vdash T: *^s \\ \Gamma \vdash f: X \to T: *^s \\ \Gamma \vDash \exists X, \\
    \Gamma \vDash (x_1: X) \to (x_2: X) \to f @ x_1 = f @ x_2\) | \(x_1,x_2\in\operatorname{Name}\) |
| take elim prop | \(\Gamma \vdash \Take(X,T,f): T :*^p\) | \(\Gamma \vdash X: *^s, \Gamma \vdash T: *^p \\ \Gamma \vdash f: X \to T: *^p \\ \Gamma \vDash \exists X \) | |
| take equal | \(\Gamma \vDash \Take(X,T,f) = f @ t\) | \(\Gamma \vdash \Take(X,T,f): T: *^s \\ \Gamma \vdash t: X: *^s\) | |

### general recursion

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| run step form | \(\Gamma\vdash\operatorname{RunStep}(A,B):*^t\) | \(\Gamma\vdash A:*^t\)<br>\(\Gamma\vdash B:*^t\) | |
| continue intro | \(\Gamma\vdash\operatorname{continue}_{A,B}(a):\operatorname{RunStep}(A,B):*^t\) | \(\Gamma\vdash a:A:*^t\)<br>\(\Gamma\vdash B:*^t\) | |
| finish intro | \(\Gamma\vdash\operatorname{finish}_{A,B}(b):\operatorname{RunStep}(A,B):*^t\) | \(\Gamma\vdash A:*^t\)<br>\(\Gamma\vdash b:B:*^t\) | |
| acc form | \(\Gamma\vdash\operatorname{Acc}_{A,B}(f,a):*^p\) | \(\Gamma\vdash A:*^t\)<br>\(\Gamma\vdash B:*^t\)<br>\(\Gamma\vdash f:A\to\operatorname{RunStep}(A,B):*^t\)<br>\(\Gamma\vdash a:\operatorname{RfType}(A):*^s_0\) | |
| acc intro | \(\Gamma\vDash\operatorname{Acc}_{A,B}(f,a)\) | \(\Gamma\vdash A:*^t\)<br>\(\Gamma\vdash B:*^t\)<br>\(\Gamma\vdash f:A\to\operatorname{RunStep}(A,B):*^t\)<br>\(\Gamma\vdash a:\operatorname{RfType}(A):*^s_0\)<br>\(\Gamma\vDash\left((b:\operatorname{RfType}(A))\to\left(\operatorname{RfTerm}_{A\to\operatorname{RunStep}(A,B)}(f)@a=\operatorname{RfTerm}_{A\to\operatorname{RunStep}(A,B)}(\operatorname{continueFun}_{A,B})@b\right)\to\operatorname{Acc}_{A,B}(f,b)\right)\) | \(b\in\operatorname{Name}\) |
| acc descent | \(\Gamma\vDash\operatorname{Acc}_{A,B}(f,b)\) | \(\Gamma\vDash\operatorname{Acc}_{A,B}(f,a)\)<br>\(\Gamma\vDash\operatorname{RfTerm}_{A\to\operatorname{RunStep}(A,B)}(f)@a=\operatorname{RfTerm}_{A\to\operatorname{RunStep}(A,B)}(\operatorname{continueFun}_{A,B})@b\) | |
| reflection type | \(\Gamma\vdash\operatorname{RfType}(A):*^s_0\) | \(\Gamma\vdash A:*^t\) | |
| reflection term | \(\Gamma\vdash\operatorname{RfTerm}_A(m):\operatorname{RfType}(A):*^s_0\) | \(\Gamma\vdash m:A:*^t\) | |

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| run | \(\Gamma\vdash\operatorname{run}_{A,B}(f,a):B:*^t\) | \(\Gamma\vdash A:*^t\)<br>\(\Gamma\vdash B:*^t\)<br>\(\Gamma\vdash f:A\to\operatorname{RunStep}(A,B):*^t\)<br>\(\Gamma\vdash a:A:*^t\)<br>\(\Gamma\vDash\operatorname{Terminates}_{A,B}(f,a)\) | |
| run case | \(\Gamma\vdash\operatorname{runCase}_{A,B}(f,a,u):B:*^t\) | \(\Gamma\vdash A:*^t\)<br>\(\Gamma\vdash B:*^t\)<br>\(\Gamma\vdash f:A\to\operatorname{RunStep}(A,B):*^t\)<br>\(\Gamma\vdash a:A:*^t\)<br>\(\Gamma\vdash u:\operatorname{RunStep}(A,B):*^t\)<br>\(\Gamma\vDash\operatorname{Terminates}_{A,B}(f,a)\)<br>\(\Gamma\vDash\operatorname{RunInv}_{A,B}(f,a,u)\) | |

## 課題

- judgement を stratified （ \(\Gamma \vdash^s t: T\)） にしなくてもいいのでは...
- \(\Ty\) を2引数にしない場合
    - \(\Ty(A, B)\) の代わりに \(t: \Ty B\) と \(B: \Power A\) を premise に入れる。
- take elim prop の set-theoretic な意味は、普通に \(\bullet \in \lbrack T \rbrack\) への map になっているということ？
    - take elim は \(X: *^p\) なら cut elimination に見える。
- inductive type や record を定義する際に気を付けるのは、 dependent sum type と W-type にしたときの大きさ
    - 基本的には \(\mathcal{R}\) と同じものを使ってよい。
    - impredicative にならないように、 \((*^s, *^p, *^s) \in \mathcal{R}\) にすること。
        - これが必要になるのはおかしい気がする（ subtype で対応するべきだから。）
- reduction の仮定にあらわれる合同性について：
    - Pred: \(\Pred (A, \{x: B \mid P\}, t) \Rightarrow (\lambda x: B. P) @ t\) としたが、
    同値関係としての \(\beta\) を定めるときには、
    \(\Pred (A, \{x: B \mid P\}, t) \cong (\lambda x: B. P) @ t\) if \(A \cong B\) のようにしてもいいかも。
    - Rf-App と二つの runCase rule は、重複する annotation を同じ metavariable にせず左線形にした。
      well-typed な source に必要な component の convertibility は generation から回収する。
