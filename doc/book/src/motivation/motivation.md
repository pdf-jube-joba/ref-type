# 動機
次のような性質を持つ型理論が欲しい。
- より自然に property に関する subtyping が使える
  - $2$ が自然数でもあり偶数でもある。
    - Coq の場合は $2$ と $2$ が偶数であることの証明の組が偶数として型付けされる。
  - 部分集合が本当に部分集合になり、キャストが簡単（書かなくていい）
  - 結果として型付けの一意性はないと思うけど、それでもいい
- 証明項を真に区別する必要がない or 証明項を扱うことができない
  - 群が等しいとは群の演算が等しいこと、証明項まで等しいこととみなしたくない
  - 証明項を構成することもできるが、それの存在を覚えておくだけぐらいでいい
  - あと関数の外延性などの axiom をいい感じにしたい
- well-definedness や等式の話をもっと簡単に扱いたい
  - 商写像の扱いのような、"取り方によらない構成"を書きたい。
- べき集合が欲しい

他に欲しいもの
- non-structural な再帰関数を"そのまま"受け入れることができるようにしたい。
  - 関数の定義の中に停止性の証明を書かずに、関数の定義とは別で停止性の証明を書きたい。
- universe level polymorphism みたいなのを、楽に書く。
  - type in type ができる部分を用意して、 consistent な部分だけ持ってくるとか。（発想は、対応する structural recursion が書ける non-structural recursion を項として受け入れるのと同じ。）
- 構造に関する部分型（？）も使えると楽
  - 環は群の部分型とみなしたい（キャストを明示的に書きたくない）
  - これをやると部分空間の扱いが絶対にめんどくさい
  - 公称型みたいな感じで扱った方がいいかも
  - これは trait っぽい。

結局、証明項みたいなものを排除する体系なので、 proof-term omitted と呼ぶことにする。
（ refinement type = subset type 以外もいろいろ入りすぎている。）

# ほしい機能の実現
## 証明と証明項の抽象化
$P: *^p$ に対して $t: P$ の項を区別する必要はなく、存在することだけ取り出せればよい。
- $\Gamma \vDash P$ を 「$\Gamma$ の下で $P$ が証明可能」を表すように導入する。
- $\Gamma \vDash P$ ならその証明項として $\Proof P$ をもって $\Gamma \vDash t: P$ なる $t$ のように扱う。

| category | conclusion | premises |
| --- | --- | --- |
| 証明可能 | $\Gamma \vDash P$ | $\Gamma \vdash t: P, \Gamma \vdash P: *^p$ |
| 抽象的な証明項 | $\Gamma \vdash \Proof P: P$ | $\Gamma \vDash P$ |

### 例
$\Gamma \vDash P_1$ かつ $\Gamma \vDash P_1 \to P_2$ なら、 $\Gamma \vdash (\Proof P_1) @ (\Proof (P_1 \to P_2)): P_2$ のように使える。

## refinement type と power type の導入
"集合" $A$ に対して $\{x: A \mid P\}$ や $\Power A$ が書けるとうれしい。
さらに、 $\{x: A \mid P\}$ から述語が取り出せた方が扱いやすい。
このため、 $\Pred(A, B)$ という項を入れて、 $\Pred(A, \{x: B \mid P\}) \to_\beta \lambda x: B. P$ のように関係を導入する。
こうすれば、一般の $A$ と $B$ に対して、 $t: A$ が $t: B$ になる条件を記述できる。

### 例
自然数を例に考えると、 $n: \mathbb{N} \vdash \{x: \Power \mathbb{N} \mid \forall m: x. m \mathrel{div} n = 0\} =: A$ とかが書けて、
$(\Gamma = n: \mathbb{N}:: (y: A):: (k: y)) \vDash k \mathrel{div} n$ が導出できるようになっていてほしい。
- $\Gamma \vdash y: \{x: \Power \mathbb{N} \mid \forall m: x. m \mathrel{div} n = 0\}$
- $\Gamma \vDash \forall m: y. m \mathrel{div} n = 0$
- $\Gamma \vdash \Proof (\forall m: y. m \mathrel{div} n = 0) @ k: (m \mathrel{div} n = 0)[m := k]$
- $\Gamma \vDash l \mathrel{div} n = 0$

### 注意点
CoC の $*$ は impredicative なので、これに対して部分集合とべき集合を与えると、矛盾しやすくなると思われる。
そのため、これができる "集合" は predicative な sort にしておく方が無難。

## independen な choice について
商集合を扱うことができるようになったので、これをさらに便利にするために、 quotient のようなことができるとうれしい。
これを動機として、 $\Take x: T. t$ を
- $T$ は空でない集合で $t \in M$
- $t$ は実は $x$ の取り方によらない

場合に、$T \to M$ という関数ではなく $M$ の元が定まっているとしたい。
取り方によらなさを表すために $=$ や"元の存在"が必要になる。

### 例
よくある構成は商集合として、集合 $A$ の同値関係 $R$ があったときに、 $A / R$ からの写像を構成するのに使う。
- $f$ は $A \to Y$ で $x \mathrel{R} y \implies f(x) = f(y)$ とする。
- $\tilde{f} = \lambda y: A / R. \Take x: y. f(x)$ は $A / R \to Y$ になってほしい。

実質的には、 $A \overset{f}{\to} B$ で特定の条件を満たす $f$ から $B$ の元を記述していることになる。

# 現状の課題
## 空間を集めてくる操作がつらい。
$X$ 上のベクトル束の同型類のなすモノイドをよりよく扱うには、 $*^s$ 上で部分集合とべき集合を集めても意味がない。
（その universe を超えるので）
ただ、普通に $\square^i$ にそれを導入すると、 ${p: *^p | ...}$ のように、 「 proposition $p$ であって ... を満たすもの」のようなやばそうなことができてしまう。
なので、 unvierse を $\lambda_{\text{PRED}}$ のようにわけるのも手かもしれない。
具体的には、
$*^p: \square^0$, $\square^i: \square^(o+1)$ とは別に、 $*^s_i: *^s_(i+1)$ と階層を用意しておいて、
$*^s_i$ と $\square^i$ はそれぞれ predicative にして inductive type まわりを整備したうえで、
$(\square^i, *^p), (*^s_i, *^p)$ を用意すれば、 $x: *^s$ に対して $(y: *^s, f: y \to x)$ を全部集めてきたような"集合"を扱えている？

## non-structural recursion がほしい。
全てが structural recursion や recursor による記述だとつらい。
proof-term の存在が示せればよかったように、普通の rec も、 upper bound が存在することが示せれば、
structural recursion になっていなくても項として受け入れたほうがいい。
これについては motivation のほかの部分に入れた。

# 具体例
## 位相空間
べきと部分集合と述語があれば位相空間ができる。
ただし、 $\vdash t: B$ と $\vDash \Pred_A B@t$ の違いに注意する。
- $O_1, O_1: \Power X$ に対して、 $O_1 \cap O_2 := \{x: X \mid \Pred_X O_1 x \wedge \Pred_X O_2 x\}$ と書ける。
- $\Lambda: *^s$ により $f: \Lambda \to \Power X$ があるなら $\bigcup_{\lambda \in \Lambda} f(\lambda) := \{x: X \mid \exists \lambda. \Pred_X f(\lambda) x\}$

これで頑張れば、 $\mathop{\text{is-topology}} (X: *^s) (O: \Power \Power X): *^p$ が作れる。
ただし、 topological space を帰納型というか record 型というかそんな感じのやつにしたいなら、
それは $*^s$ ではなくて $\square$ に住むことになる。
そのため、「 hoge を満たす位相空間 」を記述したい場合には、 $\square$ を predicative な形で階層を付ける必要がある。
（ sum 型が predicative になるために制限があるような感じ）

この場合には、 propositional equality では $t_1, t_2: {x: A | P}$ に対して $t_1 =_A t_2 => t_1 =_{x: A | P} t_2$ ができていたものを、
再び $\square$ のレベルで似たような equality が示せないと使いにくい。
具体的には、位相空間の compactness が定義されていたとき、 $2$ つの位相空間の等しさの判定時に、 compactness の証明まで要求されるようになってしまう。
だけど、構造の $=$ を要求することは少ないはずで、どちらかといえば同型が登場するので良い。
また compactness などの"構造に対する性質"については、 topology の定義を "expand" して、prop を与えることでも得られる。
こういうのをうまくやる仕組みがあればいい？
