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

## Term, Context, Judgement
普通の変数を $x$ とする。

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
