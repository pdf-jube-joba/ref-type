# 体系について
とりあえず、現在考えている体系をここにまとめる。
ただし、まだ formal に定義できていない部分は載ってない。

## Sort
- $\mathcal{S} = \{*^p, *^s, \square\}$
    - $*^s$ は set 用の sort
    - $*^p$ は proposition 用の sort
    - $\square$ は universe 
- $\mathcal{A} = {(*^p, \square), (*^s, \square)}$
- $\mathcal{R} =$ union of
    - $\{(*^p, *^p), (*^p, \square), (\square, *^p), (\square, \square)\}$
    - $\{(*^s, *^s), (*^s, \square), (*^s, *^p)\}$

普通の変数を $x$ とする。
$s$ や $s_i$ は $\mathcal{S}$ の元とする。

## Term, Context, Judgement

- term: $t = $
    - 普通の Lambda 項
        | category | definition |
        | --- | --- |
        | kind | $s \in \mathcal{S}$ |
        | variable | $x$ |
        | lambda abstraction | $\lambda x: t. t$ |
        | dependent product type | $\Pi x: t. t$ |
        | application | $t @ t$ |
    - 証明項
        | category | definition |
        | --- | --- |
        | proof of proposition | $\Proof t$ |
    - 集合に関する項
        | category | definition |
        | --- | --- |
        | refinement type | $\{x: t \mid t\}$
        | power set | $\Power t$
        | predicate | $\Pred_t t$
    - equiality の記述
        | category | definition |
        | --- | --- |
        | equality type | $ t =_t t$ |
        | existence | $\exists t$ |
        | take operator | $\Take x.t: t$ |
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
| category | conclusion | premises |
| --- | --- | --- |
| empty | $\vdash \emptyset$ | |
| axiom | $\emptyset \vdash s_1: s_2$ | $(s_1, s_2) \in \mathcal{A}$ |
| start | $\vdash \Gamma::(x: t)$ | $\vdash \Gamma, x \notin \Gamma \\ \Gamma \vdash t: s$ |
| weak | $\Gamma :: (x: t) \vdash t_1: t_2$ | $\Gamma \vdash t_1: t_2, \vdash \Gamma :: (x: t)$ |
| variable | $\Gamma \vdash x: t$ | $\vdash \Gamma, (x:t) \in \Gamma$ |
| conversion | $\Gamma \vdash t: T_2$ | $\Gamma \vdash t: T_1, T_1 \equiv^\beta T_2$ |
| dependent product form | $\Gamma \vdash (\Pi x:t. T): s_3$ | $\Gamma \vdash t: s_1, \Gamma:: (x: t) \vdash T: s_2, \\ (s_1, s_2, s_3) \in \mathcal{R}$
| dep.prd. intro | $\Gamma \vdash (\lambda x:t.m): (\Pi x:t.M)$ | $\Gamma \vdash (\Pi x:t. M): s, \\ \Gamma:: (x:t) \vdash m: M$ |
| dep.prd. elim | $\Gamma \vdash (f @ a): T[x := a]$ | $\Gamma \vdash f: (\Pi x: t. T), \Gamma \vdash a: t$ | 

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
| subset form | $\Gamma \vdash \{x: A \mid P\}: \Power A$ | $\Gamma \vdash A: *^s, \Gamma:: (x: A) \vdash P: *^p$ |
| predicate form | $\Gamma \vdash \Pred_A B: A \to *^p$ | $\Gamma \vdash A: *^s, \Gamma \vdash B: \Power A$ |
| subset intro | $\Gamma \vdash t: B$ | $\Gamma \vdash B: \Power A, \Gamma \vdash t: A, \\ \Gamma \vDash (\Pred_A B) @ t$ |
| susbet weak | $\Gamma \vDash (\Pred_A B)@ t$ | $\Gamma \vdash B: \Power A, \Gamma \vdash t: B$ |

### set rel
| category | conclusion | premises |
| --- | --- | --- |
| setrel refl | $\Gamma \vdash X \leq X$ | $\Gamma \vdash X: *^s$ |
| setrel trans | $\Gamma \vdash X_1 \leq X_3$ | $\Gamma \vdash X_1 \leq X_2, \Gamma \vdash X_2 \leq X_3$ | 
| setrel sub | $\Gamma \vdash X_1 \leq X_2$ | $\Gamma \vdash X_1: \Power X_2$ |
| setrel codomain | $\Gamma \vdash (\Pi x: X. X_1) \leq (\Pi x: X. X_2)$ | $\Gamma, x: X \vdash X_1 \leq X_2$ |
| subset element | $\Gamma \vdash t: X_2$ | $\Gamma \vdash X_1 \leq X_2, \Gamma \vdash t: X_1$ |

### Identity
| category | conclusion | premises |
| --- | --- | --- |
| id form | $\Gamma \vdash a =_A b: *^p$ | $\Gamma \vdash A: *^s, \Gamma \vdash a: A, \Gamma \vdash b: A$ |
| id intro | $\Gamma \vDash a =_A a$ | $\Gamma \vdash a =_A a: *^p$ |
| id elim | $\Gamma \vDash P @ b$ | $\Gamma \vDash a =_A b, \Gamma \vdash P: A \to *^p, \Gamma \vDash P @ a$ |
| id superset | $\Gamma \vDash a =_A b$ | $\Gamma \vDash a =_B b, \Gamma \vdash B: \Power A$ |
| id subset | $\Gamma \vDash a =_B b$ | $\Gamma \vDash a =_A b, \Gamma \vdash B: \Power A$ |

### independent choice
| category | conclusion | premises |
| --- | --- | --- |
| exists form | $\Gamma \vdash (\exists t): *^p$ | $\Gamma \vdash t: *^s$ |
| exists intro | $\Gamma \vDash \exists t$ | $\Gamma \vdash (\exists t): *^p, \Gamma  \vdash e: t$ |
| take intro | $\Gamma \vdash (\Take x: T. t): M$ | $\Gamma \vdash T: *^s, \Gamma:: x: T \vdash t: M, \Gamma \vdash M: *^s \\ \Gamma \vDash \exists t, \\ \Gamma \vDash \Pi (y_1: T). \Pi (y_2: T). t[x := y_1] =_M t[x := y_2]$ |
| take elim | $\Gamma \vDash (\Take x: T. t) =_M t[x := e]$ | $\Gamma \vdash (\Take x: T): M, \Gamma \vdash e: T$
