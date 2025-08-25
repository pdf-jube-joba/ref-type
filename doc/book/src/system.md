# 体系について
とりあえず、現在考えている体系をここにまとめる。
ただし、まだ formal に定義できていない部分は載ってない。
$\Pred(A, \{A' \mid P\}) \to_\beta P$ とする必要がある。

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
        | type lift | $\Ty t$ |
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
    | concat | $\Gamma, x:t:s$ |
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
| sort | $\Gamma \vdash t: s$ |
| typing | $\Gamma \vdash^s t: t$ |
| probable | $\Gamma \vDash t$ |

## derivation
### Calculus of Constructions 部分
| category | conclusion | premises | other |
| --- | --- | --- | --- |
| empty | $\vdash \emptyset$ | | |
| axiom | $\emptyset \vdash s_1: s_2$ | | $(s_1, s_2) \in \mathcal{A}$ |
| start | $\vdash \Gamma::(x: t: s)$ | $\vdash \Gamma, \Gamma \vdash t: s$ | $x \notin \Gamma$ |
| weak.sort | $\Gamma :: (x: t: s) \vdash t_1: s'$ | $\Gamma \vdash t_1: s', \vdash \Gamma :: (x: t: s)$ | $x \notin \Gamma$ |
| weak.type | $\Gamma :: (x: t: s) \vdash^s t_1: t_2$ | $\Gamma \vdash^s t_1: t_2, \vdash \Gamma :: (x: t: s)$ | $x \notin \Gamma$ |
| variable | $\Gamma :: (x: t: s) \vdash^s x^s: t$ | $\vdash \Gamma :: (x: t: s)$ |
| conversion | $\Gamma \vdash^s t: T_2$ | $\Gamma \vdash^s t: T_1, \Gamma \vdash T_2: s$ | $T_1 \equiv^\beta T_2$ |
| dep.form | $\Gamma \vdash (\Pi x:t. T): s_3$ | $\Gamma \vdash t: s_1, \\ \Gamma:: (x: t: s) \vdash T: s_2$ | $(s_1, s_2, s_3) \in \mathcal{R}, x \notin \Gamma $
| dep.intro | $\Gamma \vdash^{s_3} (\lambda x^{s_1}:t.m): (\Pi x^{s_1}:t.M)$ | $\Gamma \vdash (\Pi x^{s_1}:t. M): s_3, \\ \Gamma:: (x:t: s_1) \vdash m: M$ | $x \notin \Gamma$ |
| dep.elim | $\Gamma \vdash^{s_3} (f @ a): T[x := a]$ | $\Gamma \vdash^{s_3} f: (\Pi x^{s_1}: t. T), \Gamma \vdash^{s_1} a: t$ | |

### provable
| category | conclusion | premises |
| --- | --- | --- |
| provable | $\Gamma \vDash P $ | $\Gamma \vdash^{*^p} p: P, \Gamma \vdash P: *^p$ |
| proof term | $\Gamma \vdash^{*^p} \Proof P: P$ | $\Gamma \vDash P$ |

### power set, subset
| category | conclusion | premises |
| --- | --- | --- |
| power set form | $\Gamma \vdash \Power A: *^s$ | $\Gamma \vdash A: *^s$ |
| power set weak | $\Gamma \vdash \Ty B: *^s$ | $\Gamma \vdash^{*^s} B: \Power A$ |
| subset form | $\Gamma \vdash^{*^s} \{A \mid P\}: \Power A$ | $\Gamma \vdash A: *^s, \Gamma \vdash^{\square} P: A \to *^p$ |
| predicate form | $\Gamma \vdash^{\square} \Pred_A B: A \to *^p$ | $\Gamma \vdash^{*^s} B: \Power A$ |
| subset intro | $\Gamma \vdash^{*^s} t: \Ty B$ | $\Gamma \vdash^{*^s} B: \Power A, \\ \Gamma \vdash^{*^s} t: A, \Gamma \vDash (\Pred_A B) @ t$ |
| subset weak | $\Gamma \vdash^{*^s} t: A$ | $\Gamma \vdash^{*^s} B: \Power A, \\ \Gamma \vdash^{*^s} t: \Ty B, $ |
| susbet prop | $\Gamma \vDash (\Pred_A B)@ t$ | $\Gamma \vdash^{*^s} B: \Power A, \Gamma \vdash^{*^s} t: \Ty B$ |

### Identity
| category | conclusion | premises |
| --- | --- | --- |
| id form | $\Gamma \vdash a = b: *^p$ | $\Gamma \vdash A: *^s, \Gamma \vdash^{*^s} a: A, \Gamma \vdash^{*^s} b: A$ |
| id intro | $\Gamma \vDash a = a$ | $\Gamma \vdash A: *^s, \Gamma \vdash^{*^s} a: A$ |
| id elim | $\Gamma \vDash P @ b$ | $\Gamma \vdash A: *^s, \Gamma \vdash^{*^s} a: A, \Gamma \vdash^{*^s} b: A, \Gamma \vDash a = b, \\ \Gamma \vdash^{\square} P: A \to *^p, \Gamma \vDash P @ a$ |

### independent choice
| category | conclusion | premises |
| --- | --- | --- |
| exists form | $\Gamma \vdash (\exists t): *^p$ | $\Gamma \vdash t: *^s$ |
| exists intro | $\Gamma \vDash \exists t$ | $\Gamma \vdash (\exists t): *^p, \Gamma \vdash^{*^s} e: t$ |
| take intro | $\Gamma \vdash^{*^s} (\Take f): Y$ | $\Gamma \vdash X: *^s, \Gamma \vdash Y: *^s, \Gamma \vdash^{*^s} f: X \to Y \\ \Gamma \vDash \exists X, \\ \Gamma :: (y_1: X) :: (y_2: X) \vdash f @ y_1 = f @ y_2$ |
| take elim | $\Gamma \vDash \Take f = f @ e$ | $\Gamma \vdash Y: *^s \\ \Gamma \vdash^{*^s} \Take f: Y, \Gamma^{*^s} \vdash e: Y$

以下、議論を簡単にするために調整したもの
- setrel sub の $:*^s$
- take.elim の $\Gamma \vdash Y:*^s$
