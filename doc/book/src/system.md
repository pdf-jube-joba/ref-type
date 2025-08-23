# 体系について
とりあえず、現在考えている体系をここにまとめる。
ただし、まだ formal に定義できていない部分は載ってない。
あと、 bind が発生するのがめんどくさいので、 $\{x: A \mid P\}$ ではなくて、 $\{A \mid P\}$ にしておく。
この場合、 $\Pred(A, \{A' \mid P\}) \to_\beta P$ とする必要がある。

## Sort
- $\mathcal{S} = \{*^p, *^s, \square\}$
    - $*^s$ は set 用の sort
    - $*^p$ は proposition 用の sort
    - $\square$ は universe 
- $\mathcal{A} = {(*^p, \square), (*^s, \square)}$
- $\mathcal{R} =$ union of
    - $\{(*^p, *^p), (*^p, \square), (\square, \square)\}$ $*^p$ は impredicative だけど dependent はない
    - $\{(*^s, *^s), (*^s, \square), (*^s, *^p)\}$ $*^s$ は predicative + dependent

普通の変数を $x$ とする。
$s$ や $s_i$ は $\mathcal{S}$ の元とする。

## Term, Context, Judgement
（2つあるものは、別の書き方として用意している。）

- term: $t = $
    - 普通の Lambda 項
        | category | definition |
        | --- | --- |
        | kind | $s \in \mathcal{S}$ |
        | variable | $x$ |
        | lambda abstraction | $\lambda x: t. t$ |
        | dependent product type | $\Pi x: t. t$ or $(x: t) \to t$ |
        | application | $t @ t$ or $t t$ |
    - 証明項
        | category | definition |
        | --- | --- |
        | proof of proposition | $\Proof t$ |
    - 集合に関する項
        | category | definition |
        | --- | --- |
        | refinement type | $\{t \mid t\}$ |
        | power set | $\Power t$ |
        | predicate | $\Pred_t t$ or $\Pred(A, B)$ |
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
    | concat | $\Gamma, x:t$ |
- judgement
    - well-formed context: $\Gamma$

## reduction
- $\Pred _A \{x: t \mid P\} \rightarrow^\beta \lambda x:t. P$
    - $A \equiv t$ のときをほぼ想定
- あるいは、　$\Pred(A, \{B \mid P\}) \rightarrow^\beta P$
- これ以外は普通のもの。

## context, judgement
Context は普通に定義して、メタ変数 $\Gamma$ で表す。

| category | definition |
| --- | --- |
| well formed context | $\vdash \Gamma$ |
| typing | $\Gamma \vdash t: t$ |
| subtyping | $\Gamma \vdash t \leq t$ |
| probable | $\Gamma \vDash t$ |

## derivation
### Calculus of Constructions 部分
| category | conclusion | premises | other |
| --- | --- | --- | --- |
| empty | $\vdash \emptyset$ | | |
| axiom | $\emptyset \vdash s_1: s_2$ | | $(s_1, s_2) \in \mathcal{A}$ |
| start | $\vdash \Gamma::(x: t)$ | $\vdash \Gamma, \Gamma \vdash t: s$ | $x \notin \Gamma$ |
| weak | $\Gamma :: (x: t) \vdash t_1: t_2$ | $\Gamma \vdash t_1: t_2, \vdash \Gamma :: (x: t)$ | $x \notin \Gamma$ |
| variable | $\Gamma :: (x: t) \vdash x: t$ | $\vdash \Gamma :: x: t$ |
| conversion | $\Gamma \vdash t: T_2$ | $\Gamma \vdash t: T_1, \Gamma \vdash T_2: s$ | $T_1 \equiv^\beta T_2$ |
| dependent product form | $\Gamma \vdash (\Pi x:t. T): s_3$ | $\Gamma \vdash t: s_1, \\ \Gamma:: (x: t) \vdash T: s_2$ | $(s_1, s_2, s_3) \in \mathcal{R}, x \notin \Gamma $
| dep.prd. intro | $\Gamma \vdash (\lambda x:t.m): (\Pi x:t.M)$ | $\Gamma \vdash (\Pi x:t. M): s, \\ \Gamma:: (x:t) \vdash m: M$ | $x \notin \Gamma$ |
| dep.prd. elim | $\Gamma \vdash (f @ a): T[x := a]$ | $\Gamma \vdash f: (\Pi x: t. T), \Gamma \vdash a: t$ | |

### provable
| category | conclusion | premises |
| --- | --- | --- |
| provable | $\Gamma \vDash P $ | $\Gamma \vdash p: P, \Gamma \vdash P: *^p$ |
| proof term | $\Gamma \vdash \Proof P: P$ | $\Gamma \vDash P$ |

### power set, subset
| category | conclusion | premises |
| --- | --- | --- |
| power set form | $\Gamma \vdash \Power A: *^s$ | $\Gamma \vdash A: *^s$ |
| power set weak | $\Gamma \vdash B: *^s$ | $\Gamma \vdash B: \Power A$ |
| subset form | $\Gamma \vdash \{A \mid P\}: \Power A$ | $\Gamma \vdash A: *^s, \Gamma \vdash P: A \to *^p$ |
| predicate form | $\Gamma \vdash \Pred_A B: A \to *^p$ | $\Gamma \vdash B: \Power A$ |
| subset intro | $\Gamma \vdash t: B$ | $\Gamma \vdash B: \Power A, \\ \Gamma \vdash t: A, \Gamma \vDash (\Pred_A B) @ t$ |
| susbet weak | $\Gamma \vDash (\Pred_A B)@ t$ | $\Gamma \vdash B: \Power A, \Gamma \vdash t: B$ |

### set rel
| category | conclusion | premises | other |
| --- | --- | --- | --- |
| setrel refl | $\Gamma \vdash X \leq X'$ | $\Gamma \vdash X: *^s, \Gamma \vdash X': *^s$ | $X \equiv^\beta X'$ |
| setrel trans | $\Gamma \vdash X_1 \leq X_3$ | $\Gamma \vdash X_1 \leq X_2, \\ \Gamma \vdash X_2 \leq X_3$ | |
| setrel sub | $\Gamma \vdash X_1 \leq X_2$ | $\Gamma \vdash X_1: \Power X_2, \\ \Gamma \vdash X_1: *^s, \\ \Gamma \vdash X_2: *^s$ | |
| setrel codomain | $\Gamma \vdash (\Pi x: X. X_1) \leq (\Pi x: X. X_2)$ | $\Gamma \vdash X: *^s \\ \Gamma, x: X \vdash X_1 \leq X_2$ | $x \notin \Gamma$ |
| subset element | $\Gamma \vdash t: X_2$ | $\Gamma \vdash X_1 \leq X_2, \\ \Gamma \vdash t: X_1$ | |

### Identity
| category | conclusion | premises |
| --- | --- | --- |
| id form | $\Gamma \vdash a = b: *^p$ | $\Gamma \vdash A: *^s, \Gamma \vdash a: A, \Gamma \vdash b: A$ |
| id intro | $\Gamma \vDash a = a$ | $\Gamma \vdash A: *^s, \Gamma \vdash a: A$ |
| id elim | $\Gamma \vDash P @ b$ | $\Gamma \vdash A: *^s, \Gamma \vdash a: A, \Gamma \vdash b: A, \Gamma \vDash a = b, \\ \Gamma \vdash P: A \to *^p, \Gamma \vDash P @ a$ |

### independent choice
| category | conclusion | premises |
| --- | --- | --- |
| exists form | $\Gamma \vdash (\exists t): *^p$ | $\Gamma \vdash t: *^s$ |
| exists intro | $\Gamma \vDash \exists t$ | $\Gamma \vdash (\exists t): *^p, \Gamma  \vdash e: t$ |
| take intro | $\Gamma \vdash (\Take f): Y$ | $\Gamma \vdash X: *^s, \Gamma \vdash Y: *^s, \Gamma \vdash f: X \to Y \\ \Gamma \vDash \exists X, \\ \Gamma :: (y_1: X) :: (y_2: X) \vdash f @ y_1 = f @ y_2$ |
| take elim | $\Gamma \vDash \Take f = f @ e$ | $\Gamma \vdash Y: *^s \\ \Gamma \vdash \Take f: Y, \Gamma \vdash e: Y$

以下、議論を簡単にするために調整したもの
- setrel sub の $:*^s$
- take.elim の $\Gamma \vdash Y:*^s$
