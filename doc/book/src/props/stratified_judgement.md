# sorted PTS
一般の PTS ($S$, $A$, $R$) を考えておく。
- PTS は functional を仮定する。
    - $s$ に対して $(s, s') \in A$ な $s'$ は一意 ... $s'$ を $A(s)$ と書く。
    - $s_1, s_2$ に対して $(s_1, s_2, s_3) \in R$ な $s_3$ は一意 ... $s_3$ を $R(s_1, s_2)$ と書く。
- $s_1: s_1', s_2: s_2'$ なら $R(s_1, s_2): R(s_1', s_2')$ を仮定する。
    - CoC では成り立つ。 ... $s_1 = s_2 = *, s_1' = s_2' = \square$ しかないので
    - $\text{CC}_\omega$ は成り立たない。 $\square_2: \square_3, *: \square_0$ だが、 $R(\square_2, *) = *$ で $R(\square_3, \square_0) = \square_3$ のため。


以下は定義
- term $t$ = $S$ | $V^S$ | $\lambda V^S: t. t$ | $(V^S: t) \mapsto t$ | $t @ t$
- context $\Gamma$ = list of $V^S: t$

judgement について
| category | conclusion | premises |
| --- | --- | --- |
| axiom | $\emptyset \vdash s_1: s_2$ | $(s_1, s_2) \in A$ |
| start | $\Gamma; x^s: A \vdash x^s: A$| $\Gamma \vdash A: s, x \notin \Gamma$ |
| weak | $\Gamma; x^s: A \vdash M: N$ | $\Gamma \vdash M: N, \Gamma \vdash C: s, x \notin \Gamma$ |
| conversion | $\Gamma \vdash t: T_2$ | $\Gamma \vdash t: T_1, \Gamma \vdash T_2: s, T_1 \equiv^\beta T_2$ |
| dep.form | $\Gamma \vdash (x^{s_1}: A) \to B: s_3$ | $\Gamma \vdash A: s_1, \Gamma; x^{s_1}: A \vdash B: s_2, (s_1, s_2, s_3) \in R$ |
| dep.intro | $\Gamma \vdash (\lambda x^s: A. m): (x^s: A) \to M$ | $\Gamma \vdash (x^s: A) \to M: s', \Gamma; x^s: A \vdash m: M$ |
| dep.elim | $\Gamma \vdash f @ a: M[x := a]$ | $\Gamma \vdash f: (x^s: A) \to M, \Gamma \vdash a: A$ |

よくある成り立つ奴はまとめておく。
> - subject reduction $\Gamma \vdash t: T$ かつ $t \to_\beta t'$ なら $\Gamma \vdash t': T$
> - uniqueness of type $\Gamma \vdash t: T_1$ かつ $\Gamma \vdash t: T_2$ なら $T_1 \equiv T_2$

ここで、 sort elem func: $\text{Term} \to S$ を sort 以外に対して帰納的に定義する。
- $s(s) = \text{None}$
- $s(x^s) = s$
- $s(\lambda x^s: t_1. t_2) = R(s, s(t_2))$
- $s((x^s: t_1) \to t_2) = R(s(t_1), s(t_2))$
- $s(t u) = s(t)$ ただし $s(u)$ が定義されている。

また、 redux が well-sorted とは $(\lambda x^s: t_1. t_2) @ t$ に対して $s(t) = s$ を満たすこと。
term が well-sorted とは、全ての subterm が well-sorted かつ redux も well-sorted なこと。ちゃんと定義すると：
- $s$, $x^s$ は well-sorted
- $(x^s: t_1) \to t_2$ は $t_1$, $t_2$ がそうなら
- $\lambda x^s: t_1. t_2$ は $t_1$, $t_2$ がそうなら
- $t @ u$ は
    - $t$ が $\lambda$ じゃないなら、 $t$, $u$ がそうなら
    - $(\lambda x^s: t_1. t_2) @ t$ は $s(t) = s$ かつ $t$, $t_1$, $t_2$ がそうなら

このとき、次が成り立つ。
> $T$, $x$, $s$ に対して、 $x$ の free occurence が $x^s$ の形であるなら、
> $s(t) = s$ を満たす $t$ に対して $s(T[x := t]) = s(T)$ 

証明：項の形の帰納法
- $s(s) = s(s[x := t])$ で両方 $\text{None}$
- $s(y^{s'}[x := t]) = s(y^{s'}) = s'$
- $s(x^{s}[x := t]) = s(t)$
- $s((\lambda y^{s'}: t_1. t_2)[x := t]) = s(\lambda y^{s'}: (t_1[x := t]). (t_2[x := t])) = R(s(t_1[x := t]), s(t_2[x := t])) = R(s(t_1), s(t_2)) = s(\lambda y^{s'}: t_1. t_2)$
- 他は同じ。

> $t_1 \to_\beta t_2$ で $t_1$ が well-sorted なら $t_2$ も well-sorted で $s(t_1) = s(t_2)$

証明： $\to_\beta$ の導出の帰納法
- $\lambda x^s: t_1. t_2 \to_\beta \lambda x^s: t_1'. t_2$ if $t_1 \to_\beta t_1'$ なら帰納法の仮定から、
    - $t_1$, $t_2$ は well-sorted なので $\lambda x^s: t_1'. t_2$ は well-sorted
    - $s(t_1) = s(t_1')$ なので、 $s(\lambda x^s: t_1. t_2) = s(\lambda x^s: t_1'. t_2)$
- 他の cong なものは同じ議論
- $(\lambda x^s: t_1. t_2) @ t \to_\beta t_2[x := t]$ のとき。
    - well-sorted の仮定から、 $t_1, t_2, t$ は well-sorted かつ $s = s(t)$
    - 全体が well-sorted であることは定義から。
    - 上の命題から、 $s(t_2) = s(t_2[x := t])$
    - $s((\lambda x^s: t_1. t_2)@ t) = s(t_2) = s(t_2[x := t])$ で示された。

> $\Gamma \vdash t: T$ なら $t$ と $T$ は well-sorted かつ、次のどちらかが成り立つ。
>   1. $s(t)$ が定義されて、 $\Gamma \vdash T: s(t)$
>   2. $s(t)$ が定義されず、 $T \to_\beta^* s$

なんかしょうもない話： (a -> b) & (~a -> c) <=> (a & b) | (~a & c) ... Truth は FTFTFFTT
後者の意味にとっていい。
成り立たない？？

証明：導出木に関する帰納法を用いる。
- axiom: $s$ は well-sorted
    2. $s(s)$ は定義されてなくて $T$ は確かに $s_2$
- start: $x^s$ は well-sorted で、帰納法の仮定を $\Gamma \vdash A: s$ に適用すれば $A$ も well-sorted
    1. $s(x^s)$ が定義されている。 premise から $\Gamma \vdash A: s(x^s) = s$
- weak: premise にある $\Gamma \vdash M: N$ を見ればいい。
- conversion: $\Gamma \vdash t: T_2$ if $\Gamma \vdash t: T_1, \Gamma \vdash T_2: s, T_1 \equiv^\beta T_2$ の場合
    このとき、 $t$ と $T_2$ が well-sorted なのはすぐにわかる。
    帰納法の仮定を $\Gamma \vdash t: T_1$ に適用する。どっちが成り立つかで場合分けする。
    1. $s(t)$ が定義されかつ $\Gamma \vdash T_1: s(t)$ だったとする。
        $T_1 \equiv^\beta T_2$ に合流性を適用して
        $T_1 \rightarrow_\beta T_3 \rightarrow_\beta T_2$ を得るが、
        それぞれ subject reduction と $\Gamma \vdash T_{i = 1, 2}: \text{sort here}$ を適用して $\Gamma \vdash T_3: s(t)$ と $\Gamma \vdash T_3: s$ が得られる。
        ここで type uniqueness により $s = s(t)$ なので、 $\Gamma \vdash T_2: s = s(t)$ である。
        ので、 1. の $\Gamma \vdash T_2: s(t)$ が成り立つ。
    2. $s(t)$ が定義されていなくて $T_1 = s$ だったとする。
        $T_2 \equiv T_1 = s$ なので、 $T_2 \to_\beta^* s$ である。
        ので、 2. が成り立つ。
        定理には関係ないけど、 $\Gamma \vdash T_2: s$ なのでもし $s(T_2)$ が定義されていれば、
        $T_2 \to T_1 = s$ も $s(T_1)$ が定義されているはずだから、矛盾する。
        なので、 $s(T_2)$ は定義されていない。
- dep.form: 帰納法の仮定を適用すれば、 $A, B$ が well-sorted であることはわかるから、項は well-sorted である。
    - $s(A)$ と $s(B)$ がどちらも定義されているなら：
        示したいのは、 $\Gamma \vdash (s_3 = R(s_1, s_2)): R(s(A), s(B))$ が成り立っていること。
        $\Gamma \vdash A: s_1$ に帰納法の仮定を適用して $\Gamma \vdash s_1: s(A)$ がわかる。
        $\Gamma; x^{s_1}: A \vdash B: s_2$ に帰納法の仮定を適用して $\Gamma; x^{s_1}: A \vdash s_2: s(B)$ がわかる。
        なので、 $s((x^{s_1}: A) \to B) = R(s(A), s(B))$ も定義されている。
        この場合、次の命題が必要になる ... $R(s_1, s_2): R(A(s_1), A(s_2))$
    - $s(A)$ と $s(B)$ のどちらかが定義されない：
        $(x^{s_1}: A) \to B$ でも定義されてなくて、 $s_3$ がある。
- dep.intro: 帰納法の仮定を適用すれば、 well-sorted であるとわかる。
    - $s(m)$ が定義されているなら：
        示したいのは $\Gamma \vdash ((x^s: A) \to M): R(s, s(m))$ であること。
        inversion から $\Gamma \vdash A: s$ がわかる。
        $\Gamma; (x^s: A) \vdash m: M$ に帰納法の仮定を適用して $\Gamma; x^s: A \vdash M: s(m)$ がわかる。
        dep.form にいれて $\Gamma \vdash (x^s: A) \to M: R(s, s(m))$ が成り立つ。
    - $s(m)$ が定義されていないなら： $M \to_\beta^* s$ とわかる。


- dep.elim: 帰納法の仮定を適用すれば、 well-sorted とわかる。
    $\Gamma \vdash f: (x^s: A) \to M$ に帰納法の仮定を適用すると、 $(x^s: A) \to B \not \equiv_\beta s$ であるから、
    「$s(f)$ が定義されていて $\Gamma \vdash (x^s: A) \to M: s(f)$」の方が成り立っているとわかる。
    もし $s(a)$ が定義されているなら：
    $s(f @ a)$ も定義されているのと、帰納法の仮定から $\Gamma \vdash A: s(a)$ である。
    また、 inversion から $\Gamma; x^s: A \vdash M: s(f)$ がわかる。
    このとき、 $\Gamma \vdash M[x := a]: s(f @ a)$ は substitution lemma を適用すればいい。
    もし $s(a)$ が定義されていないなら：

$\text{CC}_\omega$ だと次のようなのは valid
- $\vdash (\lambda x^{\square_{i+2}}: \square_{i+1}. \square_j) @ \square_i: \square_{j+1}$
    - $\vdash (\lambda x^{\square_{i+2}}: \square_{i+1}. \square_j): (x^{\square_{i+2}}: \square_{i+1}) \to \square_{j+1}$
        - $\vdash (x^{\square_{i+2}}) \to \square_{j+1}: s$
    - $\vdash \square_{i}: \square_{i+1}$

# stratified judgement

これの judgement を stratified にすることができるか？
- $\Gamma \vdash^s t: T$ ... $s$-element の判定 ($s \in S$ が動く)
- $\Gamma \vdash_t t: s$ ... $s$-type の判定

例 ... CoC なら sort は $\{*, \square\}$ で $\Gamma \vdash^* t: T$ が term: type になり $\Gamma \vdash^\square t: T$ が constructor: type になる。

とりあえずやってみる。

| category | conclusion | premises |
| --- | --- | --- |
| axiom | $\emptyset \vdash_t s_1: s_2$ | $(s_1, s_2) \in A$ |
| start | $\Gamma; x^s: A \vdash^s x^s: A$| $\Gamma \vdash_t A: s, x \notin \Gamma$ |
| weak el | $\Gamma; x^s: A \vdash^{s'} M: N$ | $\Gamma \vdash^{s'} M: N, \Gamma \vdash_t C: s, x \notin \Gamma$ |
| weak ty | $\Gamma; x^s: A \vdash_t M: s$ | $\Gamma \vdash_t M: s, \Gamma \vdash_t C: s, x \notin \Gamma$ |
| conversion el | $\Gamma \vdash^s t: T_2$ | $\Gamma \vdash^s t: T_1, \Gamma \vdash_t T_2: s, T_1 \equiv^\beta T_2$ |
| dep.form | $\Gamma \vdash_t (x^{s_1}: A) \to B: s_3$ | $\Gamma \vdash_t A: s_1, \Gamma; x^{s_1}: A \vdash_t B: s_2$ <br> $(s_1, s_2, s_3) \in R$ |
| dep.intro | $\Gamma \vdash^{s_3} (\lambda x^{s_1}: A. m): (x^{s_1}: A) \to M$ | $\Gamma \vdash_t (x^{s_1}: A) \to M: s_3$, <br> $\Gamma; x^{s_1}: A \vdash^{s_2} m: M$ |
| dep.elim | $\Gamma \vdash^{s_3} f @ a: M[x := a]$ | $\Gamma \vdash^{s_3} f: (x^{s_1}: A) \to M, \Gamma \vdash^{s_1} a: A$ |

- $\vdash_t, \vdash^s$ から $\vdash$ は項を忘れるだけでいいから、 valid はよい。

$\Gamma \vdash t: T$ とする。
- $T \equiv s$ なら $\Gamma \vdash_t t: s$
- $s(t)$ が定義されるなら $\Gamma \vdash
