# 体系について
とりあえず、現在考えている体系をここにまとめる。
ただし、まだ formal に定義できていない部分は載ってない。

## Sort
- $\mathcal{S} = \{*^s_{i}, \sq^s_{i} \mid i \in \mathbb{N}\} \cup \{*^p, \sq^p\}$
    - $*^s_{i}, \sq^s_{i}$ は set 用の sort
    - $*^p, \sq^p$ は proposition 用の sort
- $\mathcal{A} = \{(*^s_{i}, \sq^s_{i})\} \cup \{(*^p, \sq^p)\}$
- $\mathcal{R} =$ union of
    - $\{(*^s_{i}, *^s_{i}, *^s_{i}), (*^s_{i}, \sq^s_{i}, \sq^s_{i}), (\sq^s_{i}, \sq^s_{i}, \sq^s_{i})\}$ ... $*^s_i$ は ふつうの dependent + omega 
    - $\{(\sq^s_{i}, *^s_{i}, *^s_{i+1})\}$ ... impredicative っぽいものを level をあげる
    - $\{(*^p, *^p), (\sq^p, *^p), (\sq^p, \sq^p)\}$ ... $*^p$ は impredicative だけど dependent product はない。
    - $\{(*^s_i, *^p), (*^s_i, \sq^p)\}$ ... $*^s$ についての命題を用意するため。

普通の変数を $x$ とする。
$s$ や $s_i$ は $\mathcal{S}$ の元とする。

## Term, Context, Judgement
（2つあるものは、別の書き方として用意している。）

- term: $t = $
    - 普通の Lambda 項
        | category | definition |
        | --- | --- |
        | sort | $s$ |
        | variable | $x^s$ |
        | lambda abstraction | $\lambda x^s: t. t$ |
        | dependent product type | $\Pi x^s: t. t$ or $(x^s: t) \to t$ |
        | application | $t @ t$ or $t t$ |
    - 証明項
        | category | definition |
        | --- | --- |
        | "proof later" mark | $\Proof t$ |
    - 集合に関する項
        | category | definition |
        | --- | --- |
        | refinement type | $\{x^s: t \mid t\}$ |
        | power set | $\Power t$ |
        | type lift | $\Ty (t, t)$ |
        | predicate | $\Pred_t t (t)$ or $\Pred(t, t, t)$ |
    - equiality の記述
        | category | definition |
        | --- | --- |
        | equality type | $ t = t$ |
        | existence | $\exists t$ |
        | take operator | $\Take t$ |
- context: $\Gamma=$
    | category | definition |
    | --- | --- |
    | empty context | $\emptyset$ |
    | concat | $\Gamma, x:t:s$ |
- judgement
    - well-formed context: $\Gamma$

## reduction
- $\Pred (A, \{x: B \mid P\}, t) \to (\lambda x: B. P) @ t$
- これ以外は普通のもの。

## context, judgement
Context は普通に定義して、メタ変数 $\Gamma$ で表す。

| category | definition |
| --- | --- |
| well formed context | $\text{WF}(\Gamma)$ |
| sort | $\Gamma \vdash t: s$ |
| typing | $\Gamma \vdash t: t: s$ |
| probable | $\Gamma \vDash t$ |

## derivation
### pure type system 部分
| category | conclusion | premises | other |
| --- | --- | --- | --- |
| empty | $\text{WF}(\emptyset)$ | | |
| axiom | $\emptyset \vdash s_1: s_2$ | | $(s_1, s_2) \in \mathcal{A}$ |
| start | $\text{WF}(\Gamma::(x: t: s))$ | $\vdash \Gamma$, <br> $\Gamma \vdash t: s$ | $x \notin \Gamma$ |
| weak.sort | $\Gamma :: (x: t: s) \vdash t_1: s'$ | $\Gamma \vdash t_1: s'$ <br> $\text{WF}(\Gamma :: (x: t: s))$ | $x \notin \Gamma$ |
| weak.type | $\Gamma :: (x: t: s) \vdash t_1: t_2$ | $\Gamma \vdash^s t_1: t_2$ <br> $\text{WF}(\Gamma :: (x: t: s))$ | $x \notin \Gamma$ |
| variable | $\Gamma :: (x: t: s) \vdash x^s: t: s$ | $\text{WF}(\Gamma :: (x: t: s))$ |
| conversion | $\Gamma \vdash t: T_2: s$ | $\Gamma \vdash t: T_1: s$ <br> $\Gamma \vdash T_2: s$ | $T_1 \equiv^\beta T_2$ |
| dep.form | $\Gamma \vdash (\Pi x:t. T): s_3$ | $\Gamma \vdash t: s_1$ <br> $\Gamma:: (x: t: s) \vdash T: s_2$ | $(s_1, s_2, s_3) \in \mathcal{R}$ <br> $x \notin \Gamma $
| dep.intro | $\Gamma \vdash (\lambda x^{s_1}:t.m): (\Pi x^{s_1}:t.M) : s_3$ | $\Gamma \vdash (\Pi x^{s_1}:t. M): s_3$ <br> $\Gamma:: (x:t: s_1) \vdash m: M: s_2$ | $x \notin \Gamma$ |
| dep.elim | $\Gamma \vdash (f @ a): T[x := a]: s_3$ | $\Gamma \vdash f: (\Pi x^{s_1}: t. T): s_2$ <br> $\Gamma \vdash a: t: s_1$ | |
| type.elem | $\Gamma \vdash A: s: s'$ | $\Gamma \vdash A: s$, $\Gamma \vdash s: s'$|

### provable
| category | conclusion | premises |
| --- | --- | --- |
| provable | $\Gamma \vDash P $ | $\Gamma \vdash p: P: *^p$ |
| proof term | $\Gamma \vdash \Proof P: P: *^p$ | $\Gamma \vDash P$ |

### power set, subset
ここで出てくる $*^s$ は全部階層を同じにする。
| category | conclusion | premises |
| --- | --- | --- |
| power set form | $\Gamma \vdash \Power A: *^s$ | $\Gamma \vdash A: *^s$ |
| power set intro | $\Gamma \vdash \Ty (A, B): *^s$ | $\Gamma \vdash B: \Power A: *^s$ |
| predicate | $\Gamma \vdash \Pred (A, B, t): *^p$ | $\Gamma \vdash B: \Power A: *^s$ <br> $\Gamma \vdash t: A: *^s$ |
| subset form | $\Gamma \vdash \{x^{*^s}: A \mid P\}: \Power A: *^s$ | $\Gamma \vdash A: *^s, \Gamma:: x: A: *^s \vdash P: *^p$ |
| subset intro | $\Gamma \vdash t : \Ty (A, B) : *^s$ | $\Gamma \vdash B : \Power A : *^s, \\ \Gamma \vdash t: A: *^s, \Gamma \vDash \Pred (A, B, t)$ |
| subset weak | $\Gamma \vdash t: A: *^s$ | $\Gamma \vdash t: \Ty (A, B): *^s$ |
| susbet prop | $\Gamma \vDash \Pred(A, B, t)$ | $\Gamma \vdash t: \Ty (A, B): *^s$ |

### equality
| category | conclusion | premises |
| --- | --- | --- |
| id form | $\Gamma \vdash a = b: *^p$ | $\Gamma \vdash a: A: *^s, \Gamma \vdash b: A: *^s$ |
| id intro | $\Gamma \vDash a = a$ | $\Gamma \vdash a: A: *^s$ |
| id elim | $\Gamma \vDash (\lambda x: A. P) @ b$ | $\Gamma \vdash a: A: *^s, \Gamma \vdash b: A: *^s, \\ \Gamma \vDash a = b, \\ \Gamma::(x: A: *^s) \vdash P: *^p \\ \Gamma \vDash (\lambda x: A. P) @ a$ |

### choice
| category | conclusion | premises |
| --- | --- | --- |
| exists form | $\Gamma \vdash (\exists t): *^p$ | $\Gamma \vdash t: *^s$ |
| exists intro | $\Gamma \vDash \exists t$ | $\Gamma \vdash e : t : *^s$ |
| take elim set | $\Gamma \vdash^{*^s} (\Take f): T$ | $\Gamma \vdash X: *^s, \Gamma \vdash T: *^s \\ \Gamma \vdash f: X \to T: *^s \\ \Gamma \vDash \exists X, \\
    \Gamma \vDash (x_1: X) \to (x_2: X) \to f @ x_1 = f @ x_2$ |
| take elim prop | $\Gamma \vdash^{*^p} (\Take f): T$ | $\Gamma \vdash X: *^s, \Gamma \vdash T: *^p \\ \Gamma \vdash f: X \to T: *^p \\ \Gamma \vDash \exists X $ |
| take equal | $\Gamma \vDash \Take f = f @ t$ | $\Gamma \vdash \Take f: T: *^s \\ \Gamma \vdash f: X \to T \\ \Gamma \vdash t: X: *^s$ |

課題：
- judgement を stratified （ $\Gamma \vdash^s t: T$） にしなくてもいいのでは...
- $\Ty$ を2引数にしない場合
    - $\Ty(A, B)$ の代わりに $t: \Ty B$ と $B: \Power A$ を premise に入れる。
- take elim prop の set-theoretic な意味は、普通に $\bullet \in \lbrack T \rbrack$ への map になっているということ？
    - take elim は $X: *^p$ なら cut elimination に見える。
- inductive type や record を定義する際に気を付けるのは、 dependent sum type と W-type にしたときの大きさ
    - 基本的には $\mathcal{R}$ と同じものを使ってよい。
    - impredicative にならないように、 $(*^s, *^p, *^s) \in \mathcal{R}$ にすること。
        - これが必要になるのはおかしい気がする（ subtype で対応するべきだから。）
