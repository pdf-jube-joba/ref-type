# 動機
ここでは、 Core calculus っぽい部分について扱う。

# ほしい機能の実現
## 証明と証明項の抽象化
$P: *^p$ に対して $t: P$ の項を区別する必要はなく、存在することだけ取り出せればよいはず。
- $\Gamma \vDash P$ を 「$\Gamma$ の下で $P$ が証明可能」を表すように導入する。
- $\Gamma \vDash P$ ならその証明項として $\Proof P$ をもって $\Gamma \vDash t: P$ なる $t$ のように扱う。

## refinement type と power type と predicate の導入
"集合" $A$ に対して $\{x: A \mid P\}$ や $\Power A$ が書けるとうれしい。
さらに、 $\{x: A \mid P\}$ から述語が取り出せた方が扱いやすい。
このため、 $\Pred(A, B, t)$ という項を入れて、 $\Pred(A, \{x: B \mid P\}, t) \to_\beta (\lambda x: B. P) @ t$ のように関係を導入する。
こうすれば、一般の $A$ と $B$ に対して、 $t: A$ が $t: B$ になる条件を記述できる。
ただし、 term のレベルと type のレベルを合わせたいので次のような感じにしている。
| 説明 | term level | type level |
| --- | --- | --- |
| 普通の項 | $t$ | $A$ |
| Power set の元 | $\{x: A \mid P\}, B$ | $\Power A$ |
| subset 関係 | $t$ | $\Ty (A, \{x: A \mid P\}), \Ty (A, B)$ |

## definite description について
商集合を扱うことができるようになったので、これをさらに便利にするために、 quotient のようなことができるとうれしい。
一応すでに商集合自体は記述ができるが、写像を記述することが難しい。
これを動機として、 $\Take T$ を $T$ が空でなくかつ元が1つしかない場合に $T$ の元とする。
これの正当性を記述するために $=$ や"元の存在"が必要になる。

# 現状の課題（体系）
総じて、記述のための universe 以外に、 computation のための universe が欲しいということに見える。
（というかそれ用に `rust` 側で用意していたのだった。）

- $*^s_{i}: *^s_{i+1}$: ちゃんとした数学のための厳密な universe
  - 項が computational じゃなくても、 canonical じゃなくてもよい
  - 再帰にはちゃんとした well-foundedness を要求する側
- $*^c$: 
  - 項が（基本的には） computational になっている。
  - $*^s$ 側で見たときに停止するなら、厳密な recursion の形をしていなくてもいい。
  - マクロやメタプログラミングのような、コード自体を扱えてほしい。

## non-structural recursion がほしい。
全てが structural recursion や recursor による記述だとつらい。
proof-term の存在が示せればよかったように、普通の rec も、 upper bound が存在することが示せれば、
structural recursion になっていなくても項として受け入れたほうがいい。

## universe level polymorphism について
構造として $X: *^s_{i}$, $\mu: X \times X \to X$ の組を考えてみる。
このとき $(X, \mu): (X: *^s_{i}) \times (X \times X \to X): *^s_{i+1}$ のようになるが、
このレベルが上がるのは仕方がない。
（これをやるにはさらに $(*^s_{i+1}, *^s_{i}, *^s_{i+1}) \in \mathcal{R}$ とか cumulative （$T: *^s_i \implies T: *^s_{i+1}$）が必要になるが、そこは本題じゃない。）
理由は、「台集合 $\subset *^s_i$ とその上の二項演算の組」の集合を考えればそれが $*^s_i$ には入らないのは当然だから。
ただここでの問題は、そうなると、定義を universe ごとに繰り返さなければいけないこと。
例えば群を例にすれば、 $*^s_{0}, *^s_{1}, *^s_{2}$ それぞれで帰納的な型やレコード型として定義する必要がある。
これはめんどくさいので、 universe level を受け取っての定義ができるとうれしいが、もっと根本的に解決できないか。

## decidable について
Bool 型を用いて $f: X \to \text{Bool}$ と $p: X \to *^p$ がいい感じになっていたとき、ある程度の範囲では自動的に Prop を計算できたらうれしい。
例として、 $3 < 5$ は計算できるはず。つまり、 `leq` と `leb` を自動で補完する？
これをやるにはそもそもなにか結び付けを宣言する機構が必要になるので、やめたほうがいいかも。

Rocq だと decidable は $P \vee \neg P$ として定義されているけど、 LEM を公理に入れるとあまりいいことにならない。
（計算ができない。）

## $(*^p, *^s, *^s)$ がない。
必要かどうかはわからないが、 $(*^p, *^s, *^s) \in \mathcal{R}$ を入れてない。
入れても多分大丈夫そうだが、とりあえず分けてる。
モデルの側で考えるとどうなるのか... $X: *^p, Y: *^s \vdash X \to Y: *^s$ に対しては、
$X \in S_i, Y \in \{\bullet, \{\bullet\}\}$ が適用されて、 $(\Pi_{\alpha \in X} Y) \in S_i$ が要求される。
これは $\bullet \in S_i$ と $\{\bullet\} \in S_i$ ならいいので楽勝。

pure type system としては functional + injective は保っていても、
普通のやつの組み合わせにはなっていない。
（ 『structural theory ...』 でいうところの $\forall \mathcal{P}. \mathcal{Q}$ の形にはなっていない。）

この場合、 $X: *^s, Y: *^s \vdash X = Y \to X \to Y$ が type を持たないことになっている。
一応、 $X: *^s, Y: *^s, p: X = Y \vdash X \to Y: *^s$ のように型はつくが、 context から pop することができない。
こんな感じで、 context として push するしかないものがいくつかある。

この点で、コードとしての定理や関数の定義において、引数の意味合いが変わる可能性がある。
例として、
```
variable X, Y: Set(0);
f0 (p: X = Y): X -> Y := (t: X) => t; // これは context に push した記述
f1: (X = Y) -> X -> Y := (p: X = Y) => (t: x) => t; // これは context から pop した記述
```
この場合には定理の適用の仕方も異なって、
subst lemma 的に代入するものと関数適用をするもので別れる？

### 部分集合の場合は？
$X = Y \to X \to Y$ が欲しいのはいつかと考えると、そのほとんどは部分集合と $\Pred$ で賄えると思う。
普通に考えて $\text{Bool} = \text{Nat} \to \text{Bool} \to \text{Nat}$ は使わない。
$n \text{Nat} := \{m : \text{Nat} \mid \text{div}(m, n) = 0\}$ に対して $n_1 = n_2 \to \Ty(n_1 \text{Nat}) \to \Ty(n_2 \text{Nat})$ は作れないが、
$n_1 = n_2 \to (m: \text{Nat}) \to \Pred(n_1 \text{Nat}, m) \to \Pred(n_2 \text{Nat}, m)$ は示せるとか。

### $X = Y \to X \to Y$ について
$*^s_i$ の階層があることを考えると、どうにか $Z: *^s_i$ に対して $\Pred(*^s_{i+1}, *^s_{i}, Z)$ が作れるようなら、
$X = Y$ を入れて $\lambda t: X. t$ が $X \to Y$ と型付けされるようになるので、 $X \to Y$ が inhabited になる。
ただこれのためには $X: \Power(*^s_{i})$ でなければいけない。
もともとは $X: *^s_{i}$ であり $*^s_{i}: *^s_{i+1}$ にはなっていて、 $\Power(*^s_{i}): *^s_{i+1}$ にはなっていた。
ただ、そのまま $X: *^s_{i}$ なら $X: \Power{*^s_{i}}$ を入れるのは、あまりいい感じがしない。

考えたこととして、 $*^s$ と $\square^s$ をわけて、 $*^s_{i}$ から $*^s_{i+1}$ へのリフトを与えることで、階層と整合性をとりつつできないか？
$X: *^s_{i}$ に対して $\Pred(?, ?, "X")$ が作れればいい。

## $\exists$ について
$\exists T$ という項を導入したけれど、これは新たに導入せずに CoC の impredicative encoding の話が使うこともできそう。
CoC だと、 $A: *$, $P: A \to *$ に対して、 $\exists x: A. P := \forall (C: *), (C \to) \to ... $
ただし、 first projection は定義できても second projection はいい感じのものにならない。
これは使える？

現状だと、 $\exists$ は $\Take$ を elim に持つようになっていて、強い結びつきがあるから、これを壊さないようにしたい。

## fun ext をどうにかして導出できないか？
これは現状ではできなそう。
$X, Y: *^s$ と $f, g: X \to Y$ を用意して、 $p_{f = g}: (x: X) \to f x = g x$ としておく。
（ここは依存型でもいい。）
このときに $f = g$ がほしい、という話。

### 関係としての関数：
関係としての関数： $R: (x: X) \to (y: X) \to *^p$ であって、次を満たすもののことを考えている。
1. $p_1: (x: X) \to \exists \{y: Y \mid R x y\}$ 
2. $p_2: (x: X) \to (y_1, y_2: Y) \to R x y_1 \to R x y_2 \to y_1 = y_2$

ここから関数を取り出すとすると、 $\lambda (x: X). \Take \{y: Y \mid R x y\}$ がちゃんと $X \to Y$ に型付けされる。
だから関数は取り出せている。
これを $\text{Func}(R)$ と書いておく。
これを考えると、 $f: X \to Y$ に対して、 "unique に定まる" proposition からの取り出しができる。
つまり、 $R_f := (x: X) \to (y: Y) \to f x = y$ とすることで $f \mapsto \text{Func}(R_f)$ ができる。

$R_f, R_g$ は関係なので、 $R_f = R_g$ を書くことができない。
かわりに、 $(x: X) \to (y: Y) \to (R_f x y \Leftrightarrow R_g x y)$ はできる。
（$p_{f = g}$ から $f x = y \Leftrightarrow g x = y$ が示せるから。）


$\text{Func}$ 自体の考察：
$\text{Func} := (X, Y: *^s) \mapsto (R: X \to Y \to *^p) \mapsto (p_1: (x: X) \to \exists \{y: Y \mid R x y\}) \mapsto (p_2: (x: X) \to (y_1, y_2: Y) \to R x y_1 \to T x y_2 \to y_1 = y_2) \mapsto (x: X) \mapsto \Take \{y: Y \mid R x y\} $ で、
これの型は $(X, Y: *^p) \to (R: X \to Y \to *^p) \to (\text{map all}) \to (\text{map unique}) \to X \to Y$ になっている。

### 集合としての関数：
集合論的には $X \times Y$ の部分集合のことになっている。
dependent でない sum は扱いがある程度楽だった気がする。
確か、 impredicative な encoding のもとで $A \times B := (C: *) \to (A \to B \to C) \to C$ だった。
ただ、帰納型でやるにせよ encoding を使うにせよ、$*^p$ と $*^s$ のどっちに属するのかを考えないといけないが、今はこの話をちょっと置いておく。

$\{z: X \times Y \mid f (\pi_1 z) = \pi_2 z\}$ が $f$ のグラフを表している。
$\{z: X \times Y \mid f (\pi_1 z) = \pi_2 z\}, \{z: X \times Y \mid g (\pi_1 z) = \pi_2 z\}$ はともに $\Power (X \times Y)$ の元。
（type のレベルじゃなくて term のレベルにある。）
これが $=$ であることは示せなさそう。

集合的な外延性が必要？
$X: *^s, Y_1, Y_2: \Power(X)$ に対して、 $((z: X) \to (\Pred(X, Y_1, z) \Leftrightarrow \Pred(X, Y_2, z))) \implies Y_1 = Y_2$ が axiom として入っているとする。
これなら確かに、 $\{\} = \{\}$ は成り立つ。

成り立つとしても、ここから $f = g$ は取り出せない。
