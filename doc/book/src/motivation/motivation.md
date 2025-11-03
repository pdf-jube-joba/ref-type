# 動機
ここでは、 Core calculus っぽい部分について扱う。

# ほしい機能の実現
## 証明と証明項の抽象化
$P: *^p$ に対して $t: P$ の項を区別する必要はなく、存在することだけ取り出せればよいはず。
- $\Gamma \vDash P$ を 「$\Gamma$ の下で $P$ が証明可能」を表すように導入する。
- $\Gamma \vDash P$ ならその証明項を具体的に扱わなくてもいいように、 $\Gamma \vdash \Proof P: P$ という項を導入できるようにする。

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
これを動機として、 $\Take x: T. t$ を $t: M$ が $x$ の元の取り方に**よらず**に定まるときに、 $M$ の元として扱う。
これの正当性を記述するために $=$ や"元の存在"が必要になる。

# 現状の課題（体系）
## ideal な世界としての computation や template 用の universe ?
次の問題は全部、ある種の computation 用の sort を用意しておいて、
そこの世界の template としての項を、
（条件付きで）持ってきてよいという感じに考えた方がよさそうに思えた。
つまり、理想的な記述の仕方（普通に矛盾しうる世界）を考えて、
それが well-grounded(?) なら Set 側の項として実現してよい。

### non-structural recursion がほしい。
全てが structural recursion や recursor による記述だとつらい。
proof-term の存在が示せればよかったように、普通の rec も、 upper bound が存在することが示せれば、
structural recursion になっていなくても項として受け入れたほうがいい。

### universe level polymorphism について
構造として $X: U_i$, $\mu: X \times X \to X$ の組を考えてみる。
このとき $(X, \mu): (X: U_i) \times (X \times X \to X): U_{i+1}$ のようになるが、
このレベルが上がるのは仕方がない。
（これをやるにはさらに $(U_{i+1}, U_i, U_{i+1}) \in \mathcal{R}$ とか cumulative （$T: U_i \implies T: U_{i+1}$）が必要になるが、そこは本題じゃない。）
理由は、「台集合 $\subset *^s_i$ とその上の二項演算の組」の集合を考えればそれが $U_i$ には入らないのは当然だから。
ただここでの問題は、そうなると、定義を universe ごとに繰り返さなければいけないこと。
例えば群を例にすれば、 $U_{0}, U_{1}, U_{2}$ それぞれで帰納的な型やレコード型として定義する必要がある。
これはめんどくさいので、 universe level を受け取っての定義ができるとうれしいが、もっと根本的に解決できないか。

### decidable について
Rocq だと decidable は $P \vee \neg P$ として定義されているけど、 排中律を公理に入れたときに、相性がよくない。
排中律自体はほしいが、 decidable の意味合いを壊したくない。
なので、 $*^p$ ではないところに2値の Bool 型をもっておくのがいいかも。
Bool 型を用いて $f: X \to \text{Bool}$ と $p: X \to *^p$ がいい感じになっていたとき、ある程度の範囲では自動的に Prop を計算できたらうれしい。
ただし、 $*^s$ のところに入れるとそのまま影響されてしまうことになりそうなので、
これも、 description 用の universe としての $*^s$ ではない、 computation 用の universe としての $*^c$ を用意してそこで定義するのがいいかも。

例として、 $3 < 5$ は計算できるはず。
なので、 `leq 3 5` を見たときに `by leqb 3 5` と簡単に結び付けられるといい。
つまり、 `leq` と `leb` を自動で補完する？
これをやるにはそもそもなにか結び付けを宣言する機構が必要になるので、やめたほうがいいかも。

## sort について
### stratification を行いたい
term: type: kind: $\square$ のような感じの階層構造があった方が説明が楽なので、
これを表現したかった。
基本的には PTS の $*: \square$ のみの設定が綺麗なので、
これに添え字をいろいろくっつけることでどうにかしたい。
- set 用の universes ... $*^s_{i \in \mathbb{N}}: \sq^s_{i \in \mathbb{N}}$
- prop 用の universes ... $*^p: \sq^p$

set 側は predicative にするために、 $(\sq^s_i, *^s_i, *^s_{i+1})$ とレベルをあげて、
cumulative を入れることで下のレベルを無理して挙げなくていいことにする。

### 構造付き集合を型にしたい
record 型を考えたときに、
```
record {
  X: s;
  mu: X -> X -> X;
}
```
がどの universe にいるか？
普通に sum で考えたら、 $(X, \mu): (X: s) \times (X \to X \to X)$ なので、 $\text{max}(s', s)$ ただし $s: s'$ みたいなところにいる。
だから、 $s = U_0$ なら record は $U_1$ に住む。

これを帰納型に持ってくる？
```
inductive Lift: s1 :=
| lift: (X: s) -> (mu: X -> X -> X) -> Lift
```
みたいなのを考えたときに、
$\textit{Lift}: s_1 \vdash [(X: s) \to (\mu: X \to X \to X) \to \textit{Lift}]: s_1$ である必要がある。
$s: s', (X \to X \to X: s), \textit{Lift}: s1$ と並んでいるので、
$R(A(s), R(s, s_1)) = s_1$ が満たされていればいい。

$s = *^s_0$ とすると、 $R(\sq^s_0, R(*^s_0, s_1)) = s_1$ 
現状だと $R(*^s_0, s_1)$ が書けるのが $*^s_0, \sq^s_0$ しかないので、
$\sq^s_0$ になってしまう。
一応、上の $U_0, U_1$ と同じようにはなっていて、 $\sq^s_0$ と $*^s_1$ が同じところに住んでいるイメージだからこれはいい。

ただ、 $\sq^s_0$ になっているのはこれはちょっと扱いにくいかも。
構造付き集合は、存在型と同じと思うことで、 type level に落としたい。
階層自体は上がるのはしょうがない。
cumulative があるので、 $(*^s_i, *^s_j, *^s_j) \in \mathcal{R}$ を $i < j$ に対して用意すれば自動的に max と同じような効果にはなる。（ついでに $(\sq^s_i, \sq^s_j, \sq^s_j) \in \mathcal{R}$ も入れておく。）
また、 $R(\sq^s_i, *^s_j, *^s_j)$ も $i < j$ に対して入れておく。
そうするとさっきのは解決できる。

結局、こんな感じになる：
- $*^s_i : \sq^s_i$
- $\{(*^s_i, *^s_j, *^s_j) \mid i \leq j\}$
- $\{(\sq^s_i, \sq^s_j, \sq^s_j) \mid i \leq j\}$
- $\{(*^s_i, \sq^s_i, \sq^s_i)\}$ ... これも $i \leq j$ にしていいかも
- $\{(\sq^s_i, *^s_j, *^s_j) \mid i < j\}$ ... これだけ $i < j$ じゃないといけない。

これは普通に $*^s_i \mapsto U_i, \sq^s_i \mapsto U_{i+1}$ とすれば普通の階層構造のものに埋め込める。

これで、 inductive type として、構造付き集合が書ける。
```
inductive Lift: \Set(1) :=
| lift: (X: \Set(0)) -> (mu: X -> X -> X) -> Lift
```
これのコンストラクタの検査が、 $L: *^s_1 \vdash [(X: *^s_0) \to (X \to X \to X) \to L]: *^s_1$ になっていて、導出は次
- $L: *^s_1 \vdash [(X: *^s_0) \to (X \to X \to X) \to L]: *^s_1$ ... $(\sq^s_0, *^s_1, *^s_1)$
  - $L: *^s_1 \vdash *^s_0: \sq^s_0$
  - $L: *^s_1, X: *^s_0 \vdash (X \to X \to X) \to L: *^s_1$ ... $(*^s_0, *^s_1, *^s_1)$
    - $L: *^s_1, X: *^s_0 \vdash (X \to X \to X): *^s_0$
    - $L: *^s_1, X: *^s_0, \_: (X \to X \to X): L: *^s_1$

### $(*^p, *^s, *^s)$ がない。
必要かどうかはわからないが、 $(*^p, *^s, *^s) \in \mathcal{R}$ を入れてない。
入れても多分大丈夫そうだが、とりあえず分けてる。
モデルの側で考えるとどうなるのか... $X: *^p, Y: *^s \vdash X \to Y: *^s$ に対しては、
$X \in S_i, Y \in \{\bullet, \{\bullet\}\}$ が適用されて、 $(\Pi_{\alpha \in X} Y) \in S_i$ が要求される。
これは $\bullet \in S_i$ と $\{\bullet\} \in S_i$ ならいいので楽勝。

pure type system としては functional + injective は保っていても、
普通のやつの組み合わせにはなっていない。
（ 『structural theory ...』 でいうところの $\forall \mathcal{P}. \mathcal{Q}$ の形にはなっていない。）

この場合、 $X: *^s, Y: *^s \vdash (X = Y) \to X \to Y$ が type を持たないことになっている。
一応、 $X: *^s, Y: *^s, p: (X = Y) \vdash X \to Y: *^s$ のように型はつくが、 context から pop することができない（し、 $t: X \to Y$ となる項が作れない）。
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
$(X = Y) \to X \to Y$ が欲しいのはいつかと考えると、そのほとんどは部分集合と $\Pred$ で賄えると思う。
普通に考えて $\text{Bool} = \text{Nat} \to \text{Bool} \to \text{Nat}$ は使わない。
$n \text{Nat} := \{m : \text{Nat} \mid \text{div}(m, n) = 0\}$ に対して $n_1 = n_2 \to \Ty(n_1 \text{Nat}) \to \Ty(n_2 \text{Nat})$ は作れないが、
$n_1 = n_2 \to (m: \text{Nat}) \to \Pred(n_1 \text{Nat}, m) \to \Pred(n_2 \text{Nat}, m)$ は示せるとか。

ただこの場合にも $n_1 = n_2 \to n_1 \text{Nat} \to n_2 \text{Nat}$ は定義できていない。
あくまでも、 $n_1 = n_2 \to ("m \in n_1 \text{Nat}") \to ("m \in n_1 \text{Nat}")$ という、 type じゃなくて prop としての $\in$ が表現できているだけ。

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

### その他考察
extensionality は項の (propositional な) uniqueness が、外部との関連から導き出せる話になっている。
$x, y: X: *^s$ に対して、$X$ という型の性質から定義される相互作用のようなものに対して、 $x$ と $y$ の振る舞いが同じなら $x = y$ みたいな感じ。
- set ext: $X: *^s, Y_1, Y_2: \Power (X) \vDash ((z: X) \to (\Pred(X, Y_1, z) \leftrightarrow \Pred(X, Y_2, z)))  \to Y_1 = Y_2$
- fun ext: $X: *^s, Y: *^s, f_1, f_2: X \to Y \vDash ((x: X) \to f_1 x = f_2 x) \to f_1 = f_2$

これの見方として、 $Y_1, Y_2$ を $X \to *^p$ のことだと思えば、
Coq の Prop ext （$*^p$ にも $=$ があって $(p \leftrightarrow q) \to (p = q)$） を仮定すれば、 set ext は fun ext になる。
（ fun ext でいう $Y$ を $*^p$ にして、 $\Pred(X, Y_i, z)$ は $Y_i z$ になっている。）
ちゃんと $\leftrightarrow$ を考えると、
$$p \leftrightarrow q = (p \to q) \wedge (q \to p) = (c: *^p) \to ((p \to q) \to c) \to ((q \to p) \to c) \to c$$
というふるまいだが、問題はなさそう。

逆はできなさそう。
つまり、 fun ext から set ext は厳しい気がする。
$(\Take x: T. m) = e$ があるので何とかなる気もするが。

## type level equation をどうにかしないといけない
長さ $n$ の list を作るとして、
- subset と predicate を用いる場合 : $\{x: \text{List} \mid \text{length} (x) = n\}$
- 普通の dependent を用いる場合 : `inductive List := | nil: List 0 ; | cons: A -> (n: Nat) -> List n -> List (Nat.succ n)`

前者の場合には、 $n = m$ から $l: \Ty (\text{ListLen} (n))$ から $l: \Ty(\text{ListLen} (m))$ が導出できるが、後者の場合にはできない気がする。
普通は、 $P: A \to s$ に対して $x = y -> P x -> P y$ が確かに書けるのでいいが、
（ singleton だから？）
今の状況だと $P: A \to *^p$ に限定しているのでだめ。

これをどうにかするなら、 TypeLevel での Equal をまずは書けるようにしないといけない。
現状だと $t_1, t_2: T: *^s_{i}$ じゃないと $t_1 = t_2$ が書けない。
- まずは $t_1, t_2: T: s$ に対して $t_1 =^{s} t_2$ を導入して $s = *^s$ はいままで通り。

考えたこと：
$X =^{\sq} Y$ について、
そもそももともとの $t: \Ty(A, B)$ if $t: A, \vDash \Pred(A, B)$ についても一般化してしまって、
type level の物に関しては、 $t: T_1, T_1 =^\sq T_2 \implies t: T_2$ を入れるのはどうか？
これと合わせて、 type level の場合には、「ある種の external なふるまいがあって、それに対して同じようにふるまうのであれば等しい」が入れられればいい。
例えば subset からくる場合は、 $(z: A) \to \Pred(A, x, z) \to \Pred(A, y, z)$ なら $\Ty(A, x) = \Ty(A, y)$ とする。

これを拡張すると関数のふるまいも同じようにできる気がする。
もともと関数は type level のものなので（ $X \to Y$ はべき集合 ... $f: X \to Y$ は subset の同一視だから）、これに対しても external な振る舞いとしての $f = g$ が $(x: X) \to f x \to g x$ から来ている。
subset の Lift の逆が起きている？
- $a: A: *$, $b: \Power A: *$ から $a: \Ty (A, b): *$ として、 subset は element から type level に引き上げている
- $f$ はもとから element レベルにいる設定だけど、これが実は type level から来ているものと思える？

これをやり始めたら、結局、 $*^p$ を impredicative かつ type と同じ階層にいると思って、
$X \to Y$ と $X \to *^p$ に対して同じ議論を適用する、そうすると subset と function が両方 extensionality で説明できる？
その話は HOL すぎる？
ちゃんと考察するのが難しい。

- 一般の $X: K: \sq$ に対して、 $t: X$ となる"条件" $\mathbb{P}(X, t)$ がある
- $\vdash \mathbb{P}(X, t)$ なら $t: X$ みたいにする？
- $T_1 =^\sq T_2$ に対する refl: $P: (X: K) \to *^p$ から $\vDash P T_1 \to P T_2$
  - これは、 $t_1 =^* t_2$ に対する refl: $P: (X: A) \to *^p \implies \vDash P t_1 \to P t_2$ （ただし $t_1, t_2: A$ ）から類推した。
- $\Ty(A, b): *: \sq$ の場合は $a: \Ty(A, b)$ if $\vDash \Pred(A, b, a)$ ... $\mathbb{P}(\Ty(A, b), a) = \Pred(A, b, a)$
  - $\mathbb{P}(\Ty(A, \{x: B \mid P\}), a) = (\lambda x: B. P) @ a = P[x := a]$
- $P: A \to *^s$ として $n = m$ から $\vDash \mathbb{P}(P n, t) \to \mathbb{P}(P m, t)$ 
- subset は $A \to *^p$ と思えるのは当然だけれど、 $A$
- Kind level equality は必要になる？

indexed family を使った場合の type level equalty の話は、
term level の eq から type level の eq を導くのではなく、本当に欲しいのは $n = m$ から $T n \to T m$ だと思う。
indexed type family の index が term であること気をつければいい。
あと、これをやるなら prop 側も変えて、 elim と induction を入れる方が綺麗かも。
つまり、 $(A: *^s) \to (a, b: A) \to (p: a = b) \to (P: A \to s) \to P a \to P b$ ができればいい、

この場合には、 computation があるといい？

- $\text{exp} = (e \text{"="} e) \mid \text{refl}(a) \mid J(A, a, b, p, P, r)$
- $J(A, P, r, a, a, \text{refl}(a)) \to r @ a$
- $\Gamma \vdash J(A, a, b, p, P, r):$ if
  - $\Gamma \vdash A: *^s$, $\Gamma \vdash a, b: A$
  - $\Gamma \vdash p: a = b$
  - $\Gamma \vdash P: A \to s$ where $s \in \{*^p, *^s_{i}\}$
  - $\Gamma \vdash r: (a: A) \to P a$

$(p: a = b) \to P a \to P b$ について、 $*^p$ を一度挟んでいるので、最後の sort が $*^s$ になっていないのは奇妙に思える。
これを解消するなら $\exists P a \to \exists P b$ を考えることになるが、
この場合は、 $(a: A) \to \exists (P a)$ に対しての elimination が使えるので、
そもそも書けている。

むしろ、 $\exists (P a \to P b)$ が一番欲しいものになっていて、
しかも、 computation のことを考えると、 $\exists (P a \to P a)$ が identity であることがないとめんどくさい。
「この構成によって定義される map が identity であること」を保証するのは、何かしら強力な公理とかを課している？
$(\exists X) \to (\exists Y)$ から $\exists (X \to Y)$ を取り出すのはやばい気がする。

今気が付いたが、 $\exists (P a \to P a)$ から $\exists (P a \to P b)$ が取り出せるから、 id を適用して大丈夫だ。

## 導出木と $\vDash$ について
type level の話を書いていて、（当然だけど）
結論に $\vDash$ が来る規則は、全部上側に型チェックが来るようにできる。
（上側の $\vDash$ を下に持ってきて mp にすればいいから）
