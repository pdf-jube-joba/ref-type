# 体系について
とりあえず、現在考えている体系をここにまとめる。
ただし、まだ formal に定義できていない部分は載ってない。

## Sort
- $\mathcal{S} = \{*^s_{i} \mid i \in \mathbb{N}\} \cup \{*^p, \square\}$
    - $*^s_i$ は set 用の sort
    - $*^p$ は proposition 用の sort
    - $\square$ は universe 
- $\mathcal{A} = \{(*^s_{i}, *^s_{i+1})\} \cup \{(*^p, \square)\}$
- $\mathcal{R} =$ union of
    - $\{(*^s_{i}, *^s_{j}) \mid i \leq j\}$ ... $*^s_i$ は predicative になる。
    - $\{(*^p, *^p), (\square, *^p), (\square, \square)\}$ ... $*^p$ は impredicative だけど dependent はない。
    - $\{(*^s_i, *^p), (*^s_i, \square)\}$ ... $*^s$ についての命題を用意するため。

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
        | proof of proposition | $\Proof t$ |
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
| typing | $\Gamma \vdash^s t: t$ |
| probable | $\Gamma \vDash t$ |

## derivation
### pure type system 部分
| category | conclusion | premises | other |
| --- | --- | --- | --- |
| empty | $\text{WF}(\emptyset)$ | | |
| axiom | $\emptyset \vdash s_1: s_2$ | | $(s_1, s_2) \in \mathcal{A}$ |
| start | $\text{WF}(\Gamma::(x: t: s))$ | $\vdash \Gamma$, <br> $\Gamma \vdash t: s$ | $x \notin \Gamma$ |
| weak.sort | $\Gamma :: (x: t: s) \vdash t_1: s'$ | $\Gamma \vdash t_1: s'$ <br> $\text{WF}(\Gamma :: (x: t: s))$ | $x \notin \Gamma$ |
| weak.type | $\Gamma :: (x: t: s) \vdash^s t_1: t_2$ | $\Gamma \vdash^s t_1: t_2$ <br> $\text{WF}(\Gamma :: (x: t: s))$ | $x \notin \Gamma$ |
| variable | $\Gamma :: (x: t: s) \vdash^s x^s: t$ | $\text{WF}(\Gamma :: (x: t: s))$ |
| conversion | $\Gamma \vdash^s t: T_2$ | $\Gamma \vdash^s t: T_1$ <br> $\Gamma \vdash T_2: s$ | $T_1 \equiv^\beta T_2$ |
| dep.form | $\Gamma \vdash (\Pi x:t. T): s_3$ | $\Gamma \vdash t: s_1$ <br> $\Gamma:: (x: t: s) \vdash T: s_2$ | $(s_1, s_2, s_3) \in \mathcal{R}$ <br> $x \notin \Gamma $
| dep.intro | $\Gamma \vdash^{s_3} (\lambda x^{s_1}:t.m): (\Pi x^{s_1}:t.M)$ | $\Gamma \vdash (\Pi x^{s_1}:t. M): s_3$ <br> $\Gamma:: (x:t: s_1) \vdash^{s_2} m: M$ | $x \notin \Gamma$ |
| dep.elim | $\Gamma \vdash^{s_3} (f @ a): T[x := a]$ | $\Gamma \vdash^{s_3} f: (\Pi x^{s_1}: t. T)$ <br> $\Gamma \vdash^{s_1} a: t$ | |
| type.elem | $\Gamma \vdash^{s'} A: s$ | $\Gamma \vdash A: s$, $\Gamma \vdash s: s'$|

### provable
| category | conclusion | premises |
| --- | --- | --- |
| provable | $\Gamma \vDash P $ | $\Gamma \vdash^{*^p} p: P, \Gamma \vdash P: *^p$ |
| proof term | $\Gamma \vdash^{*^p} \Proof P: P$ | $\Gamma \vDash P$ |

### power set, subset
ここで出てくる $*^s$ は全部階層を同じにする。
| category | conclusion | premises |
| --- | --- | --- |
| power set form | $\Gamma \vdash \Power A: *^s$ | $\Gamma \vdash A: *^s$ |
| power set intro | $\Gamma \vdash \Ty (A, B): *^s$ | $\Gamma \vdash^{*^s} B: \Power A$ |
| predicate | $\Gamma \vdash \Pred (A, B, t): *^p$ | $\Gamma \vdash^{*^s} B: \Power A$ <br> $\Gamma \vdash^{*^s} t: A$ |
| subset form | $\Gamma \vdash^{*^s} \{x^{*^s}: A \mid P\}: \Power A$ | $\Gamma \vdash A: *^s, \Gamma:: x: A \vdash P: *^p$ |
| subset intro | $\Gamma \vdash^{*^s} t: \Ty (A, B)$ | $\Gamma \vdash^{*^s} B: \Power A, \\ \Gamma \vdash^{*^s} t: A, \Gamma \vDash \Pred (A, B, t)$ |
| subset weak | $\Gamma \vdash^{*^s} t: A$ | $\Gamma \vdash \Ty (A, B): *^s, \\ \Gamma \vdash^{*^s} t: \Ty (A, B)$ |
| susbet prop | $\Gamma \vDash \Pred(A, B, t)$ | $\Gamma \vdash \Ty (A, B): *^s, \\ \Gamma \vdash^{*^s} t: \Ty (A, B)$ |

### equality
| category | conclusion | premises |
| --- | --- | --- |
| id form | $\Gamma \vdash a = b: *^p$ | $\Gamma \vdash A: *^s, \Gamma \vdash^{*^s} a: A, \Gamma \vdash^{*^s} b: A$ |
| id intro | $\Gamma \vDash a = a$ | $\Gamma \vdash A: *^s, \Gamma \vdash^{*^s} a: A$ |
| id elim | $\Gamma \vDash P @ b$ | $\Gamma \vdash A: *^s, \Gamma \vdash^{*^s} a: A, \Gamma \vdash^{*^s} b: A, \Gamma \vDash a = b, \\ \Gamma \vdash^{\square} P: A \to *^p, \Gamma \vDash P @ a$ |

### choice
| category | conclusion | premises |
| --- | --- | --- |
| exists form | $\Gamma \vdash (\exists t): *^p$ | $\Gamma \vdash t: *^s$ |
| exists intro | $\Gamma \vDash \exists t$ | $\Gamma \vdash (\exists t): *^p, \Gamma \vdash^{*^s} e: t$ |
| take elim set | $\Gamma \vdash^{*^s} (\Take f): T$ | $\Gamma \vdash X: *^s, \Gamma \vdash T: *^s, \Gamma \vdash^{*^s} f: X \to T \\ \Gamma \vDash \exists X, \\ \Gamma \vDash (x_1: T) \to (x_2: T) \to f @ x_1 = f @ x_2$ |
| take elim prop | $\Gamma \vdash^{*^p} (\Take f): T$ | $\Gamma \vdash X: *^s, \Gamma \vdash T: *^p, \Gamma \vdash^{*^p} f: X \to T \\ \Gamma \vDash \exists X $ |
| take equal | $\Gamma \vDash \Take f = t$ | $\Gamma \vdash^{*^s} \Take f: T, \Gamma^{*^s} \vdash t: T$ |

課題：
- judgement を stratified にしなくてもいいのでは...
- $\Ty$ を2引数にしない場合
    - $\Ty(A, B)$ の代わりに $t: \Ty B$ と $B: \Power A$ を premise に入れる。
- take elim prop の set-theoretic な意味は、普通に $\bullet \in \lbracket T \rbracket$ への map になっているということ？
- take elim は $X: *^p$ なら cut elimination に見える。
