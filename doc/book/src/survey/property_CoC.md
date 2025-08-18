一回、 CoC の性質についていろいろ証明を見ておく。
# PTS としての CoC について
PTS 自体が定義が複数ある。
judgement はほとんどは The Structural Theory of Pure Type System に従う。

- judgement に context の WF を入れる
- judgemental equality ではなく beta conversion （外部）を使うとする
- 変数に sort のラベルが付き、 context にも sort を入れておく。
- var は top の変数を出し、 weak として 「$\Gamma \vdash M: N$ かつ $\text{WF}(\Gamma:: x^s: A)$ なら $\Gamma :: x^s:A \vdash M: N$」 を入れる。

# confluence (Church-Rosser)
代入やα変換についてまじめに考える必要がある。
例： $\lambda x. y \equiv \lambda x'. y$ とみたいので、 $(\lambda x. y)[y := x]$ はそのまま計算すると具合が悪い。
こんな感じで、 free occurence に気を付ける必要がある。
以降では、α同値で項を同一視する。
これがつらい場合には、 de-Brujin index を用いること。
（定理証明支援系で示すとかの場合にはそれを使った方がいいかも。）

普通の $\beta$ reduction は次のような感じ

#def1
1. $\lambda x: A. t \to_\beta \lambda x: A'. t$ if $A \to_\beta A'$
2. $\lambda x: A. t \to_\beta \lambda x: A. t'$ if $t \to_\beta t'$
3. $(x: A) \to t \to_\beta (x: A') \to t$ if $A \to_\beta A'$
4. $(x: A) \to t \to_\beta (x: A) \to t'$ if $t \to_\beta t'$
5. $t_1 t_2 \to_\beta t_1' t_2$ if $t_1 \to_\beta t_1'$
6. $t_1 t_2 \to_\beta t_1 t_2'$ if $t_2 \to_\beta t_2'$
7. $(\lambda x: A. t_1) t_2 \to_\beta t_1[x := t_2]$
  - $t_2$ の FV が $x$ を含まないようにとれているとすることができる。

示したいのは、「 $t \to_\beta t_1$ かつ $t \to_\beta t_2$ ならば、 $t'$ があって $t_1 \to_\beta^* t'$ かつ $t_2 \to_beta^* t'$ が成り立つ。」である。
（この性質を合流性 (confluence) とか church-Rosser という。）


これを示すのに、 parallel reduction と呼ばれる別の簡約を定義して、
もとの簡約との関係を用いる方法がある。
（ Tait, Martin-L"of method ?）
この簡約は、項 $M$ に対して定義される $M^*$ を用いると非常に強い性質が示せる。
（Takahashi による証明）

#def2
1. $s \Rightarrow s$
2. $x \Rightarrow x$
3. $\lambda x: A. t \Rightarrow \lambda x: A'. t'$ if $A \Rightarrow A'$ and $t \Rightarrow t'$
4. $(x: A) \to t \Rightarrow (x: A') \to t'$ if $A \Rightarrow A'$ and $t \Rightarrow t'$
5. $t_1 t_2 \Rightarrow t_1' t_2'$ if $t_1 \Rightarrow t_1'$ and $t_2 \Rightarrow t_2'$
6. $(\lambda x: A. t_1) t_2 \Rightarrow t_1'[x:= t_2']$ if $t_1 \Rightarrow t_1'$ and $t_2 \Rightarrow t_2'$ and $A \Rightarrow A'$
  - $A \Rightarrow A'$ は帰納法が強くなるようにするため。

このとき、次が成り立つ。

#thm1
1. $t \Rightarrow t$
2. $t \to_\beta t'$ なら $t \Rightarrow t'$
3. $t \Rightarrow t'$ なら $t \to_beta^* t'$
4. $t \Rightarrow t'$, $l \Rightarrow l'$ なら $t[y := l] \Rightarrow t'[y := l']$

証明：
1. $t$ の構造についての帰納法を用いれば、明らか。
2. $t \to_\beta t'$ の導出木に関する帰納法を用いる。
    1. $t_1 t_2 \to_\beta t_1 t_2'$ の場合：帰納法の仮定から、 $t_2 \Rightarrow t_2'$ なので、 #thm1.1 と合わせて $t_1 t_2 \Rightarrow t_1 t_2'$
    2. $t_1 t_2 \to t_1' t_2$ の場合：上と同様
    3. $\lambda x: A. t \to_\beta \lambda x: A'. t$ の場合：上と同様
    4. $\lambda x: A. t \to_\beta \lambda x: A. t'$ の場合：上と同様
    5. $(x: A) \to t \to_\beta (x: A') \to t$ の場合：上と同様
    6. $(x: A) \to t \to_\beta (x: A) \to t'$ の場合：上と同様
    7. $(\lambda x:A. t_1) t_2 \to_\beta t_1[x := t_2]$ の場合：$t_1 \Rightarrow t_1$ と $t_2 \Rightarrow t_2$ より、 #def2.6 から。
3. $t \Rightarrow t'$ の導出木に関する帰納法を用いる。
    1. $s \Rightarrow s$ の場合： $s \to_\beta^* s$ は明らか。
    2. $x \Rightarrow x$ の場合： $x \to_\beta^* x$ は明らか。
    3. $\lambda x: A. t \Rightarrow \lambda x: A'. t'$ の場合：帰納法の仮定から、 $A \to_\beta^* A'$ と $t \to_\beta^* t'$ があるので、 $\lambda x: A. t \to_\beta^* \lambda x:A'. t \to_\beta^* \lambda x:A'. t'$ ができる。
    4. $(x: A) \to t \Rightarrow (x: A') \to t'$ の場合：上と同様。
    5. $t_1 t_2 \Rightarrow t_1' t_2'$ の場合：上と同様。
    6. $(\lambda x: A. t_1) t_2 \Rightarrow t_1'[x:= t_2']$ の場合：帰納法の仮定から $t_1 \to_\beta^* t_1'$ と $t_2 \to_\beta^* t_2'$ と $A \to_\beta^* A'$ があるから、 $(\lambda x: A. t_1) t_2 \to_\beta^* (\lambda x: A'. t_1') t_2' \to_\beta t_1'[x := t_2']$ がわかる。
4. $t \Rightarrow t'$ の導出木に関する帰納法を用いる。
    1. $s \Rightarrow s$ の場合： $s[y := l] \equiv s \Rightarrow s \equiv s[y := l']$ より
    2. $x \Rightarrow x$ の場合：
        - $x = y$ なら、 $x[y := l] \equiv l \Rightarrow l' \equiv x[y := l]$
        - $x \neq y$ なら、 $x[y := l] \equiv x \Rightarrow x \equiv x[y := l']$
    3. $\lambda x: A. t \Rightarrow \lambda x: A'. t'$ の場合：帰納法の仮定から、 $A[y := l] \Rightarrow A'[y := l']$ と $t[y := l] \Rightarrow t'[y := l']$ が得られていて、さらに、 $A \Rightarrow A'$ かつ $t \Rightarrow t'$ である。
        - $x = y$ なら $(\lambda x: A. t)[x := l] \equiv \lambda x:(A[y := l]). t \Rightarrow \lambda x: (A'[y := l']). t' \equiv (\lambda x: A'. t')[y := l']$
        - $x \neq y$ なら、上の議論が $t, t'$ の部分に $[y := l], [y := l']$ が付いただけ。
    4. $(x: A) \to t \Rightarrow (x: A' \to t')$ の場合：上と同様。
    5. $t_1 t_2 \Rightarrow t_1' t_2'$ の場合：帰納法の仮定は $t_1[y := l] \Rightarrow t_1'[y := l']$ と $t_2[y := l] \Rightarrow t_2'[y := l']$ なので、$(t_1 t_2)[y := l]$ を見ればよい。
    6. $(\lambda x: A. t_1) t_2 \Rightarrow t_1'[x:= t_2']$ の場合：帰納法の仮定は、 $t_1[y := l] \Rightarrow t_1'[y := l']$ と $t_2[y := l] \Rightarrow t_2'[y := l']$ と $A[y := l] \Rightarrow A'[y := l']$ である。
      - $x = y$ なら、 $((\lambda x: A. t_1) t_2)[y :=  l] \equiv (\lambda x: A[y := l].t_1) (t_2[y := l]) \Rightarrow t_1'[x := (t_2'[y := l'])] \equiv t_1'[x := t_2'][y := l']$
      - $x \neq y$ なら $((\lambda x: A. t_1) t_2)[y := l] \equiv (\lambda x: A[y := l]. t_1[y := l]) t_2 \Rightarrow (t_1'[y := l'])[x := t_2'[y := l']] \equiv t_1'[x := t_2'][y := l']$ **ラムダ抽象への代入が行える条件から、 $l$はFVに$x$を持ってはいけない。なので、代入の順序を入れ替える補題が使える。**

代入に関する補題として次を用いた。
#lem1
1. $t_1[x := t_2[x := l]] \equiv t_1[x := t_2][x := l]$
2. $x \neq y$ で $x \notin \text{FV}(l)$ なら $t_1[y := l][x := t_2[y := l]] \equiv t_1[x := t_2][y := l]$

証明：
1. $t_1$ に関する帰納法を用いればいい。
    1. $t_1 = s$ なら関係ない
    2. $t_1 = x'$ なら
        - $x = x'$ のとき $x'[x := t_2[x := l]] \equiv t_2[x := l] \equiv x'[x := t_2][x := l]$
        - そうじゃないときは、両辺は $x'$ のまま
    3. $\lambda x':A. t$ なら、
        - $x = x'$ なら $(\lambda x':A. t)[x := t_2[x := l]] \equiv \lambda x': (A[x := t_2[x := l]]). t \equiv \lambda x': (A [x := t_2][x := l]). t \equiv (\lambda x: A. t)[x := t_2][x := l]$
    4. $(x':A) \to t$ なら、上と同様。
    5. $t_1 t_2$ なら、これはそのまま計算した結果が（帰納法の仮定と合わせて）出てくる。
2. $t_1$ に関する帰納法を用いればいい。
    1. $t_1 = s$ なら関係ない
    2. $t_1 = x'$ なら
        - $x' = y$ のときは、 $x \neq y$ より $x \neq x'$ に注意して $x'[y := l][x := t_2[y := l]] \equiv l[x := t_2[y := l]]$
        - $x' \neq y$ のときも同様にして計算する。
    3. 残りは消化試合。

次に、 $M^*$ を次のように定義する。

#def3
1. $s^* = s$
2. $x^* = x$
3. $(\lambda x:A. t)^* = \lambda x: A^*. t^*$
4. $((x: A) \to t)^* = (x: A^*) \to t^*$
5. $(t_1 t_2)^* = t_1^* t_2^*$ if $t_1 \neq \lambda x: A. t$
6. $((\lambda x: A. t) t_2)^* = t^*[x := t_2^*]$

このとき、次が成り立つ。
#lem2
1. $M \Rightarrow N$ なら $N \Rightarrow M^*$

証明：
1. $M$ の構造に関する帰納法を用いる。
    1. $s$ のの場合： $M \Rightarrow N$ なら $N = M = M^*$ である。
    2. $x$ の場合：上と同様
    3. $\lambda x:A. t$ の場合： $N = \lambda x: A'. t'$ のみが考えられる。帰納法の仮定から $A \Rightarrow A' \Rightarrow A^*$, $t \Rightarrow t' \Rightarrow t^*$ が得られている。なので、 $\lambda x: A'. t' \Rightarrow \lambda x: A^*. t^*$
    4. $(x: A) \to t$ の場合は上と同様。
    5. $t_1 t_2$ の場合：
        - $t_1$ が $\lambda$ の形をしていない場合を考える。
            このとき、 $t_1 t_2 \Rightarrow N$ は $t_1 \Rightarrow t_1'$, $t_2 \Rightarrow t_2'$ によって $N = t_1' t_2'$ と書ける。
            帰納法の仮定から、 $t_i' \Rightarrow t_i^:*$ なので、 $t_1 t_2 \Rightarrow t_1' t_2' \Rightarrow t_1^* t_2^*$ よりよい。
        - $t_1 = \lambda x:A. t$ の場合。
            - もし #def5 を用いて導出されたなら、 $\lambda x:A.t \Rightarrow t_1'$ と $t_2 \Rightarrow t_2'$ を用いて
                $M = (\lambda x:A. t) t_2 \Rightarrow t_1' t_2' = N$ となっている。
                ここで、この $t_1'$ は必ず $\lambda x: A'. t'$ の形をしていて、 $A \Rightarrow A', t_1 \Rightarrow t_1'$ であることが（定義を調べると）わかる。
                また、帰納法の仮定から、 $A \rightarrow A' \Rightarrow A^*$, $t \Rightarrow t' \Rightarrow t^*$ が得られている。
                $N = t_1' t_2' = (\lambda x: A'. t') t_2' \Rightarrow t^* [x := t_2^*] = (\lambda x: A. t)^* t_2^*$ 
            - もし #def6 を用いて導出されたなら、 $t'$, $A'$, $t_2'$ によって $\lambda x: A. t \Rightarrow \lambda x:A'. t'$ と $t_2 \Rightarrow t_2^*$ を用いて
                $M = (\lambda x: A. t) t_2 \Rightarrow t'[x := t_2'] = N$ となっている。
                ところで帰納法の仮定から、 $\lambda x: A'. t' \Rightarrow \lambda x: A^*. t^*$ と $t_2' \Rightarrow t_2^*$ が成り立っている。
                $t'[x := t_2'] \Rightarrow t^*[x := t_2^*]$ が示せる。

よって、 $\Rightarrow$ の合流性は示せた。

# type system の性質
barendregt の lambda calculi with typesね。
#def4
- context $\Gamma$ と $s$ に対して $\Gamma \vdash A: s$ となるものを $\Gamma$-type of $s$
- context $\Gamma$ と $s$ に対して $\exists B, \Gamma \vdash A: B, \Gamma \vdash B: s$ となるものを $\Gamma$-element of $s$

CoC の場合は、 term を 4 つに分類することができる：
- $\square$
- $\square$-type
- $\square$-element $\supset$ $*$-type
- $*$-element

この分類をもとにモデルを考えたりする。

#### variable
次が成り立つ（帰納法の議論のため、一緒にした方がいい。）
1. $\Gamma \vdash A: B$ なら $\text{FV}(A), \text{FV}(B) \subset \{x \mid x \in \Gamma\}$
2. $\vdash \Gamma = x_1^{s_1}: A_1 :: \cdots :: x_n: A_n$ なら $\text{FV}(A_i) \subset \{x_1, \ldots, x_{i-1}\}$

証明：
導出木に関する帰納法を用いる。
- empty の場合(2) $\text{WF} \emptyset$ なので、 2 は満たされる
- wf の場合(2) 「$\Gamma \vdash A: s$ かつ $x \notin \Gamma$ なら $\text{WF}(\Gamma::x^s: A)$」 に対して $\text{FV}(A) \subset \Gamma$ を示せばよい。これは帰納法の仮定の $\Gamma \vdash A: s$ からわかる。
- axiom の場合(1) 「$\text{WF}(\Gamma)$ なら $\Gamma \vdash s_1: s_2$」 については、 $s_1, s_2$ は FV がないのでよい。
- var の場合(1) 「$\text{WF}(\Gamma:: x^s: A)$ なら $\証明mma \vdash x: A$」に対して、 $\text{FV}(A) \subset \Gamma$ を示せばいい。これは帰納法の仮定から。
- weak の場合(1) 「$\Gamma \vdash M:N$ かつ $\text{WF}(\Gamma::x^s:A)$ なら $\Gamma::x^s:A \vdash M:N$」 に対して、 $\text{FV}(M), \text{FV}(N) \subset \Gamma::x^s: A$ を示すが、これは帰納法の仮定からすでに $\subset \Gamma$ が示せている。
- prod の場合(1) 「$\Gamma \vdash A: s_1$ かつ $\Gamma::x^{s_1}:A \vdash B: s_2$ なら $\Gamma \vdash ((x^{s_1}: A) \to B): s_3$」に対して $\text{FV}((x^{s_1}: A) \to B) \subset \Gamma$ を示す。これは、帰納法の仮定から $\text{FV}(A) \subset \Gamma$ と $\text{FV}(B) \subset \Gamma \cup x$ がわかっているので、 $\text{FV}((x^{s_1}: A) \to B) = \text{FV}(B) - \{x\} \cup \text{FV}(A) \subset \Gamma$ である。
- abs の場合(1) 「$\Gamma::x^s:A \vdash t: B$ かつ $\Gamma \vdash ((x^s: A) \to B): s'$ なら $\Gamma \vdash (\lambda x^s: A. t): ((x^s: A) \to B)$」 に対して $\text{FV}(\lambda x^s: A. t), \text{FV}((x^s: A) \to B) \subset \Gamma$ を示す。これは、帰納法の仮定からわかる。
- app の場合(1) 「 $\Gamma \vdash t: (x^s:A) \to B$ かつ $\Gamma \vdash y: A$ なら $\Gamma \vdash t @ u: B[x := u]$」に対して $\text{FV}(u @ v), \text{FV}(B[x := u]) \subset \Gamma$ を示す。 $\text{FV}(u @ v) $ についてはそのままわかる。 $\text{FV}(B[x := u]) = \text{FV}(B) - \{x\} \cup \text{FV}(u)$ なので、 $\text{FV}((x^s:A) \to B) \subset \Gamma$ とかからわかる。
- conv の場合(1) これは conversion で beta が変わらないのでいい。

#### substituion
仮定
$\Gamma \vdash t: A$
結論
1. $\text{WF}(\Gamma :: x: A :: \Gamma')$ なら $\text{WF}(\Gamma :: \Gamma'[x := t])$
2. $\Gamma :: x: A :: \Gamma' \vdash B: C$ なら $\Gamma :: \Gamma'[x := t] \vdash B[x := t]: C[x := t]$

これの $\Gamma' = \emptyset$ で derivation が var のときが base case として次のようになっている。
$$\Gamma x: A \vdash x: A \implies \Gamma \vdash x[x:=t] : A[x := t]$$

証明：
結論の前提に関する帰納法を用いる。
- empty の場合 (1) $\Gamma$ も $\Gamma'$ も empty になるからよい
- wf の場合 (1) 

#### generation
- $\Gamma \vdash s: A$ なら $\exists s'$ s.t.
    - $A \equiv s'$
    - $(s, s') \in \mathcal{A}$
- $\Gamma \vdash x: A$ なら $\exists B$ s.t.
    - $\Gamma \vdash B: s$
    - $A =_\beta B$
    - $(x: B) \in \Gamma$
- $\Gamma \vdash ((x: M) \to N): A$ なら $\exists (s_1, s_2) \in \mathcal{R}$ s.t.
    - $\Gamma \vdash M: s_1$
    - $\Gamma::x:M \vdash N: s_2$
    - $A =_\beta s_3$
- $\Gamma \vdash (\lambda x: M. t): A$ なら $\exists s, B$ s.t.
    - $\Gamma \vdash (x: M) \to B: s$
    - $\Gamma:: x: A \vdash b: B$
    - $A =_\beta (x: M) \to B$
- $\Gamma \vdash (F a): A$ なら $\exists M, B$ s.t.
    - $\Gamma \vdash F: (x: M) \to B$
    - $\Gamma \vdash a: M$
    - $A \equiv B[x := a]$

#### sort
$\Gamma \vdash A: B$ なら $B \equiv s$ か $\Gamma \vdash B: s$

#### subject reduction
- $\Gamma \vdash A: B$ かつ $A \to_\beta A'$ なら $\Gamma \vdash A': B$
- $\Gamma \vdash A: B$ かつ $B \to_\beta B'$ なら $\Gamma \vdash A: B'$

#### uniqueness of type
$\Gamma \vdash A: B_1, \Gamma \vdash A: B_2$ なら $B_1 =_\beta B_2$

## classification

classifycation のために次のものを定義する。
- $\mathcal{V}$: term to $\{0,1,2,3\}$
    - $\mathcal{V}(\square) = 3$, $\mathcal{V}(*) = 2$
    - $\mathcal{V}(x^\square) = 1$, $\mathcal{V}(x^*) = 0$
    - $\mathcal{V}(\lambda x: A. B) = \mathcal{V}((x: A) \to B) = \mathcal{V}(B A) = \mathcal{V}(B)$

#thm 
- $\mathcal{V}(x^s) = \mathcal{V}(M)$ なら $\mathcal{V}(P[x := M]) = \mathcal{V}(P)$

#thm
- not $\Gamma \vdash \square: A$
- not $\Gamma \vdash A B: \square$
- not $\Gamma \vdash (\lambda x: A. b): \square$
- $\Gamma \vdash A: \square$ なら $\mathcal{V}(A) = 2$
- $\Gamma \vdash A: B$ かつ $\mathcal{V}(A) \in \{2, 3\}$ なら $B \equiv \square$
- $\Gamma \vdash A: B$ なら $\mathcal{V}(A) + 1 = \mathcal{V}(B)$

これは階層を番号付けしているわけなので、単純に sort を見るだけなら $s$ という関数を次のように定義すればいい。
- $s(x^s) = s$ for $s \in \{*, \square\}$
- $s(\lambda x. A. B) = s((x: A) \to B) = s(A B) = s(B)$

これは、 $s$-element を見つけるのに役立つ。
#def
- $s(t) = *$ ... proof term
- $s(t) = \square$ ... predicate

#thm
- $\Gamma \vdash t: T$ なら $\Gamma \vdash T: s(t)$ か $T \equiv \square$ のどちらか一方のみが成り立つ。

# モデルと consistency
polymorphic is not set-theoretic によると、
impredicative な sort は $\{0 = \emptyset, 1 = \{0\}\}$ という bool みたいな集合に移し、
$*$-type は $0$ か $1$ になるようにしないといけない。
この場合、 $*$-element はなんでも $0$ に移す interpretation にすることで、
type は inhabitant かどうか、 term は項が存在するかどうかになってしまう。
（つまり、 term を区別せずに $0$ に移してしまう。）
逆にこれを守れば、 set-theoretic な interpretation ができるようになる。
impredicative な sort $*$ の解釈を、 "proof-irrelevant" なモデルに対応させてしまうしかないということ。

set-theoretic なモデルを考える以外にも、 interpretation を考えることができる。
- $\Gamma$ のもとでの classification を考えることで、項や variable を階層分けしたうえで、 interpretation を考える
    - saturated set と normalizing な項の集合を考える ... strong normalization を示すのにわかりやすい。型に対して、停止する項全体の集合を与える。
    - realization model ... よくわかんない
    - (partial) combinatorial algebra を使う ... 集合というよりは構造付きで考えるほうが都合がいい。
    - domain theory ... untyped な lambda でもできるし、一応そういう研究はあるみたい。
- 階層分けしない ... set-theoretic なものしかみないかも。

## set theoretic な話
CoC を広げて、 impredicative な sort $*$ と predicative な sort $\square^i$ を加えた $\text{CoC}_\omega$ を考えておく。
これをちょっと cumulative （ $\Gamma \vdash A: *$ なら $\Gamma \vdash A:\square^i$ ）にしたものに、
ZFC での interpretation を与えたのが set in types, type in sets に書かれている。
このとき ZFC + inaccesible な cardinal が $\mathbb{N}$ ぐらいあって階層になっている体系を考えたら、
その集合の体系が無矛盾なら $\text{CoC}_\omega$ が無矛盾になる。
（なぜなら、 $\vdash t: (P:*). P$ となる項 $t$ があれば $(P:*). P$ に対応する集合が空じゃなくなるが、これは普通は空集合になるから？）
この話をちゃんと読んでおきたい。
一応、 not so simple model constructions of CoC の sorted system の議論の方がわかりやすいのでこっちをとりたい。
こっちは cumulative じゃないので、こっちの方が好きかも。

注意点として、
- ZFC は一回述語論理なので、こっち側ではすべてが "式" として定義されている。
- 「well-formed / well-typed なもの以外にも定義しているので、 partial な定義であるが、 well-* な場合にはうまくいく」ようにやっている。
    - **$\Gamma \vdash t$ は全ての $\Gamma$ と $t$ に対して定義されている。**
- sorted な system を用いることで、 $\Gamma \vdash t$ の場合分けを楽に記述する。
    - if proof-term は Werner の方でも書かれていた場合分けだと思う。

#def
- $\lvert \Gamma \rvert$: $n$-tuples of ZFC-sets (partial) where $n$ is length of context :=
    - $\lvert [] \rvert$ = $()$
    - $\lvert \Gamma; x: A \rvert$ = $\{(\gamma, \alpha) \mid \gamma \in \lvert \Gamma \rvert, \alpha \in \lvert \Gamma \vdash A \rvert (\gamma)\}$
- $\lvert \Gamma \vdash t \rvert$: partial function of $\lvert \Gamma \rvert$ to ZFC-sets :=
    - $\lvert \Gamma \vdash t \rvert (\gamma) = 0$ if $s(t) = *$
    - $\lvert \Gamma \vdash * \rvert (\gamma) = \{0, 1\}$
    - $\lvert \Gamma \vdash \square \rvert (\gamma) = U$
    - $\lvert \Gamma \vdash x^\square \rvert (\gamma) = \pi_i \gamma$ if $x^\square$ is $i$-th
    - $\lvert \Gamma \vdash t u \rvert(\gamma) = \lvert \Gamma \vdash t \rvert (\gamma) ( \lvert \Gamma \vdash u \rvert (\gamma))$
        - これは set-theoretic な関数の適用のため、well-typed じゃない一般の状況では定義されていないことに注意。例： $A: *, B: * \vdash A B$ は意味がない。
    - $\lvert \Gamma \vdash \lambda x^s: A. t \rvert (\gamma) = \alpha \in \lvert \Gamma \vdash A \rvert(\gamma) \mapsto \lvert \Gamma; x^s: A \vdash t \rvert(\gamma, \alpha)$
    - $\lvert \Gamma \vdash (x^s: A) \to B \rvert$ = $\bigcap_{\alpha \in \lvert \Gamma \vdash A \rvert} \lvert \Gamma; x^s: A \vdash B \rvert (\gamma, \alpha)$ if $B$ is predicate ... iff $(x^s: A) \to B$ is predicate
    - $\lvert \Gamma \vdash (x^s: A) \to B \rvert$ = $\Pi_{\alpha \in \lvert \Gamma \vdash A \rvert} \lvert \Gamma: x^s: A \vdash B \rvert (\gamma \alpha)$

まあこれはうまくいきそうということで。
predicate かどうかの場合分けの際に、 proof はありえないが、 $a: *, p: a \to *$ のような場合には $a \to *$ は predicate でないことに注意。
これは CoC でやっているので $\square$ が top sort ということからちょっとめんどくさいことがいろいろ出てくると思うが、
Lean や Coq のような hierarchy を作る場合には、もうちょっと楽な気がする（ sort function が total になるので、 well-* なもののみ考えることができる。）
依存型を入れるのに $(*, \square, \square)$ を入れるのは、 $*$ を型と強く思う場合なので、 $\square^i$ を型の住む本体と考えれば、 $(*, \square)$ はいらない。
代わりに、"述語" として $A: \square^i$ に対して $(A \to *): \square^i$ が欲しくなる。
しかしこれはふつうの $(\square^i, \square^j , \square^{\text{max}(i, j)})$ 則で対応可能。

- $S = \{*, \square^i\}$
- $A = \{(*, \square^1), (\square^i, \square^{i+1})\}$
- $R = \{(*, *, *), (\square^i, *, *), (\square^i, \square^j, \square^{\text{max}(i, j)})\}$

これで、 sort-labeled な PTS を考えれば、 $s(t)$ は全射になる。
（ $\Gamma t: T : s(t)$ を考えたいので level が 2 つ上がる。）
- $s(*)$ = $\square^2$
- $s(\square^i)$ = $\square^{i+2}$
- $s(x^s)$ = $s$
- $s((x^s: A) \to B)$ = $(s(A), s(B), s)$ かつ $s: s'$ となる $s, s'$ が一意なので、この $s'$ 
- $s(\lambda x^s: A. B)$ = 上と同様の定義。
- $s(t u)$ = $s(t)$

このとき、次が成り立つ。（ Generation 省略）
#thm
- $\Gamma \vdash t: T$ なら $\Gamma \vdash T: s(t)$
