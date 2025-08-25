# sorted PTS
一般の PTS ($S$, $A$, $R$) を考えておく。
- PTS は functional を仮定する。
    - $s$ に対して $(s, s') \in A$ な $s'$ は一意 ... $s'$ を $A(s)$ と書く。
    - $s_1, s_2$ に対して $(s_1, s_2, s_3) \in R$ な $s_3$ は一意 ... $s_3$ を $R(s_1, s_2)$ と書く。
- $s_1: s_1', s_2: s_2'$ なら $R(s_1, s_2): R(s_1', s_2')$ を仮定する。
    - CoC では成り立つ。 ... $s_1 = s_2 = *, s_1' = s_2' = \square$ しかないので
    - $\text{CC}_\omega$ は成り立たない。 $\square_2: \square_3, *: \square_0$ だが、 $R(\square_2, *) = *$ で $R(\square_3, \square_0) = \square_3$ のため。
- $(s_1, s_2, s_3) \in R$ なら $s_2 = s_3$ を仮定する。
    - これのうれしいのは、 $s_1, s_3$ から $s_2$ が決まること。
    - これも $\text{CC}_\omega$ では成り立たない。
        とくに、 $(\square_2, \square_1, \square_2), (\square_2, \square_0, \square_2) \in R$ なので、
        「$s_2$ が決まる」性質も成り立たない。

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

それと、 $s$-element としての uniqueness がある。これは証明を書いておく。
> $\Gamma \vdash t: T$ なら unique に $s$ が存在して $\Gamma \vdash T: s$ か $T = s$

証明：
uniqueness は type uniqueness からわかる。
それ以外は、導出木を見れば、 dep.elim 以外は確かに入っている。
帰納法の仮定から、 $\Gamma \vdash (x^s: A) \to B: s'$ がある。
inversion と subst lemma により、 $\Gamma \vdash B[x := a]: s'$ がわかる。

ここで、 sort elem func $e$: partial $\text{Term} \to S$ を次のように定義する。
（ $(s_1, s_2, s_2)$ にした時点で $\lambda, \Pi$ は後ろだけ取ればよくなる。）
- $e(s) = \text{None}$
- $e(x^s) = s$
- $e(\lambda x^s: t_1. t_2) = R(e, e(t_2))$ if $e(t_1)$ defined
- $e((x^s: t_1) \to t_2) = R(s, e(t_2))$
- $e(t u) = e(t)$ if $e(u)$ defined

また、 sort type func $a$: partial $\text{Term} \to S$ を次のように定義する。
- $a(s) = A(s)$
- $a(x^s) = \text{None}$
- $a(\lambda x^s: t_1. t_2) = \text{None}$
- $a((x^s: t_1) \to t_2) = R(s, a(t_2))$
- $a(t u) = \text{None}$

この形を見れば、 $a(t)$ が定義されているなら $t = (x_1^{s_1}: A_1) \to \ldots \to (x_n^{s_n}: A_n) \to s$ の形しかないことがわかり、 $A_i$ 自身もその形である。
つまり、 BNF として $S$ | $S \to S$ で生成されるもののみを対象にしている。

また、 redux が well-sorted とは $(\lambda x^s: t_1. t_2) @ t$ に対して $e(t) = s$ を満たすこと。
term が well-sorted とは、全ての subterm が well-sorted かつ redux も well-sorted なこと。ちゃんと定義すると：
- $s$, $x^s$ は well-sorted
- $(x^s: t_1) \to t_2$ は $t_1$, $t_2$ がそうなら
- $\lambda x^s: t_1. t_2$ は $t_1$, $t_2$ がそうなら
- $t @ u$ は
    - $t$ が $\lambda$ じゃないなら、 $t$, $u$ がそうなら
    - $(\lambda x^s: t_1. t_2) @ t$ は $e(t) = s$ かつ $t$, $t_1$, $t_2$ がそうなら

> $T$, $x$, $s$ に対して、 $T$ における $x$ の free occurence が $x^s$ の形であるなら、
> $e(t) = s$ を満たす $t$ に対して $e(T[x := t]) = e(T)$ 

証明：項の形の帰納法
- $T = s$ なら $T[x := t] = T$ より。
- $T = y^{s'}$ なら、 $T[x := t] = T$ より。
- $T = x^s$ なら、 $T[x := t] = t$ より、 $e(T) = e(x^s) = s = e(t) = e(T[x := t])$
- $e((\lambda y^{s'}: t_1. t_2)[x := t]) = e(\lambda y^{s'}: (t_1[x := t]). (t_2[x := t])) = R(e(t_1[x := t]), e(t_2[x := t])) = R(e(t_1), e(t_2)) = e(\lambda y^{s'}: t_1. t_2)$
- 他は同じ。

> $t_1 \to_\beta t_2$ で $t_1$ が well-sorted なら $t_2$ も well-sorted で $e(t_1) = e(t_2)$

証明： $\to_\beta$ の導出の帰納法
- $\lambda x^s: t_1. t_2 \to_\beta \lambda x^s: t_1'. t_2$ if $t_1 \to_\beta t_1'$ なら帰納法の仮定から、
    - $t_1$, $t_2$ は well-sorted なので $\lambda x^s: t_1'. t_2$ は well-sorted
    - $e(t_1) = e(t_1')$ なので、 $e(\lambda x^s: t_1. t_2) = e(\lambda x^s: t_1'. t_2)$
- 他の cong なものは同じ議論
- $(\lambda x^s: t_1. t_2) @ t \to_\beta t_2[x := t]$ のとき。
    - well-sorted の仮定から、 $t_1, t_2, t$ は well-sorted かつ $s = e(t)$
    - 全体が well-sorted であることは定義から。
    - 上の命題から、 $e(t_2) = e(t_2[x := t])$
    - $e((\lambda x^s: t_1. t_2)@ t) = e(t_2) = e(t_2[x := t])$ で示された。

> $\Gamma \vdash t: T$ なら $t$ と $T$ は well-sorted かつ、次のどちらかも成り立つ。
>   1. $e(t)$ が定義される $\implies$ $\Gamma \vdash T: e(t)$
>   2. $a(t)$ が定義されるなら $\implies$ $T \to_\beta^* a(t)$

証明：導出木に関する帰納法を用いる。
- axiom: $s$ は well-sorted
    1. $e(s_1)$ は定義されないから成り立つ。
    2. $a(s_1)$ が定義されて $T = s_2 = a(s_1)$
- start: $x^s$ は well-sorted で、帰納法の仮定を $\Gamma \vdash A: s$ に適用すれば $A$ も well-sorted
    1. $e(x^s)$ が定義されている。 premise から $\Gamma \vdash A: e(x^s) = s$
    2. $a(x^s)$ は定義されないから成り立つ。
- weak: premise にある $\Gamma \vdash M: N$ を見ればいい。
- conversion: $\Gamma \vdash t: T_2$ if $\Gamma \vdash t: T_1, \Gamma \vdash T_2: s, T_1 \equiv^\beta T_2$ の場合
    このとき、 $t$ と $T_2$ が well-sorted なのはすぐにわかる。
    帰納法の仮定を $\Gamma \vdash t: T_1$ に適用する。どっちが成り立つかで場合分けする。
    1. $e(t)$ が定義されているとする。
        $\Gamma \vdash t: T_1$ に仮定を適用して、 $\Gamma \vdash T_1: e(t)$ が得られる。
        $T_1 \equiv^\beta T_2$ に合流性を適用して
        $T_1 \rightarrow_\beta T_3 \rightarrow_\beta T_2$ を得るが、
        それぞれ subject reduction と $\Gamma \vdash T_{i = 1, 2}: \text{sort here}$ を適用して $\Gamma \vdash T_3: e(t)$ と $\Gamma \vdash T_3: s$ が得られる。
        ここで type uniqueness により $s = e(t)$ なので、 $\Gamma \vdash T_2: s = e(t)$ である。
        ので、 1. の $\Gamma \vdash T_2: e(t)$ が成り立つ。
    2. $a(t)$ が定義されているとする。
        $\Gamma \vdash t: T_1$ に仮定を適用して、 $T_1 \to_\beta^* a(t)$ である。
        このとき、 $T_1 \equiv_\beta T_2$ より $T_2 \to_\beta^* a(t)$ である。
- dep.form: 帰納法の仮定を適用すれば、 $A, B$ が well-sorted であることはわかるから、項は well-sorted である。
    1. $e((x^{s_1}: A) \to B)$ が定義されているなら $e(A)$ と $e(B)$ は定義されている。
        仮定を適用して $\Gamma \vdash s_1: e(A)$ と $\Gamma; x^s: A \vdash s_2: e(B)$ がわかる。
        $R(s_1, s_2): e((x^{s_1}: A) \to B) = R(e(A), e(B))$ よりよい。
    2. $a(x^{s_1}: A \to B)$ が定義されているなら $a(A)$ と $a(B)$ が定義されている。
        仮定を適用して $s_1 = a(A), s_2 = a(B)$ がわかる。
        よって、 $a((x^{s_1}: A) \to B) = R(a(A), a(B)) = R(s_1, s_2) = s_3$ である。
- dep.intro: 帰納法の仮定を適用すれば、 well-sorted であるとわかる。
    1. $e(\lambda x^s: A. m)$ が定義されているなら $e(B)$ が定義されている。
        仮定を適用して $\Gamma \vdash M: s(m)$ がわかる。
        $\Gamma \vdash (x^s: A) \to M: s'$ が得られているので、 $s' = R(e(A), e(m))$ を示すのが目標。
        ただ、 uniqueness があるので、 inversion と合わせて $\Gamma \vdash (x^s: A) \to M: R(e(A), e(m))$ よりこれはわかる。
    2. $a()$ が定義されていないからよい。
- dep.elim: 帰納法の仮定を適用すれば、 well-sorted とわかる。
    1. $e(f @ a)$ が定義されているなら $e(f)$ と $e(a)$ が定義されている。
        帰納法の仮定から $\Gamma \vdash (x^s: A) \to B: e(f)$ と $\Gamma \vdash A: e(a)$ がわかる。
        inversion から、 $\Gamma \vdash A: s$ と $\exists s', \Gamma; x^s: A \vdash B: s'$ かつ $(s, s', e(f)) \in R$ がわかる。
        type uniqueness から $s = e(a)$ がわかり、 $R$ の仮定から $s' = e(f)$ もわかる。
        subst lemma により、 $\Gamma \vdash B[x := a]: s' = e(f) = e(f @ a)$ である。
    2. $a()$ が定義されていないからよい。

$e(t)$ も $a(t)$ も定義されないことがあるが、 $e(t)$ か $a(T)$ のどちらかは定義される？

いずれにせよ、 $s$-element としての $s$ は一意である。

いくつか気が付いたこと
1.  HOL に $(\square, \triangle, \triangle)$ を加えるとかだと次のことができる。
    - $\vdash (\lambda x: *. *): (x: *) \to \square$
        - $\vdash (x: *) \to \square: \triangle$
            - $\vdash *: \square$
            - $x: * \vdash \square: \triangle$
        - $x: * \vdash * : \square$
    
    これに対しては $e$ も $a$ も普通には定義できないし、 $* \to \square$ は sort ではない。
2. $s_2, s_3$ の仮定がないと、 $e(f^{\square_3} @ a^{\square_3})$ がうまく定義できない。
    これは、 $\text{CC}_\omega$ に対して $f: \square_2 \to \square_{0, 1}, a: \square_2 \vdash f @ a: \square_{0, 1}$ のようになるため。
    つまり、 $f: T$ をとってきて、 $T$ の行き先を見なければいけないが、それを見ようとすると型システムを用いた帰納定義になるので無理。
    逆に、この仮定があるから、 $e(f @ a) = e(f)$ が正当化される。
    何も仮定がないなら $e(f @ a)$ が $e(f)$ と $e(a)$ から決定できない。

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

> $\Gamma \vdash t: T$ とする。
> 1. $T = s$ なら $\Gamma \vdash_t t: s$
> 2. $s$ であって $\Gamma \vdash T: s$ を満たすものがあれば、 $\Gamma \vdash^s t: T$

証明：なんかうまくいきそう。
- [ ] TODO
