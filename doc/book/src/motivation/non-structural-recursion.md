division を計算するのに euclidean algorithm（ユークリッド互除法）があるが、
これは coq では楽に書けない。
まあ、停止性を証明しないといけないのはそうだけど、
証明項とかの帰納法を回す必要があってめんどくさい。

## rec について
型をあまり考えずにやってみる。項として次のものを追加する。
- $$\text{rec $x$ $x$ = $M$}$$
rec の reduction は単に次のようになる。
$$ \text{rec $f$ $x$ = $M$} \to^\beta \lambda x. (M[f := (\text{rec $f$ $x$ = $M$})]) $$
これを用いると、ユークリッド互除法は次のように書ける。
ただし、 $\mathbb{N}$ や $"bool"$ という型や、 $\leq$: $\mathbb{N} \times \mathbb{N} \to "bool"$ はいいとする。
$$ \begin{align*}
  \text{rec} f (x: \mathbb{N} \times \mathbb{N}) = \
    &\text{if $x.0 \leq x.1$  then $f (x.1, x.0)$ else} \\
    &\text{if $x.0 \mathrel{\text{div}} x.1 == 0$ then $x.1$ else $f (x.1, x.0 \mathrel{\text{div}} x.1)$} \
\end{align*} $$

型付きとして簡単にやるなら次のようになる。
$$
  \dfrac{\Gamma, f: T \to T', x: T \vdash M: T'}{\Gamma \vdash \text{rec $f$ $x$ = $M$}: T \to T'}
$$

## このままだとまずい理由
定理証明系としては、consistency が保たれている（ $\Gamma \vdash t: (\forall P: *^p. P)$ となる項 $t$ がない）必要があるが、
これを使うと $t$ ができてしまうのでだめ。
全ての rec がまずいのではなくて、無制限の rec がまずい。
呼び出されるごとに引数が減ることがわかっていたり、構造帰納法の形になるなら大丈夫。

例えば自然数を考える。
足し算の定義は次のように書ける。
```
rec add ((n, m): \mathbb{N} times \mathbb{N}) =
  match n with
  | Z => m
  | S n' => add n' (S m)
```
これを受け入れていいのは、実はこれは自然数の帰納法に似ているから。
つまり、
- `P = N -> (N -> N)` とする
- `P 0` の元として `m |-> m` がある。
- `P n -> P S n` の元として `m |-> S m` がある。
- 2 つを組み合わせれば `P n` が任意のところでできる。

この場合、実は fix を生で使っているというより、自然数から生成される elim と comp 規則を与える項を用いた形に変換していると思える。
elim は次のようになっている。
$$ 
  \dfrac
  {
    \Gamma, x: \mathbb{N} \vdash T: s,
    \Gamma \vdash x_Z: T[x := 0],
    \Gamma \vdash x_S: T[x := n] -> T[x := S n],
  }  {
    \Gamma \vdash \text{elim}_\mathbb{N} (x_Z, x_S, n): T[x := n],
  }
$$
elim の変換は次のように書ける。
- $\text{elim}_\mathbb{N} (x_Z, x_S, 0) -> x_Z$
- $\text{elim}_\mathbb{N} (x_Z, x_S, S n) -> x_S (\text{elim}_\mathbb{N} (x_Z, x_S, n))$

add の場合は、 `add = n |-> m |-> elim (m, x |-> S x, n)` と書けて、例えば次のように遷移が進む。
- $\text{add} S(Z) m = \text{elim} (m, x \mapsto S x, S(Z))$
- $(x \mapsto S(x)) @ (\text{elim}(m, x \mapsto S(x), Z))$
- $S (\text{elim}(m, x \mapsto S(x), Z))$
- $S m$

だから、 fix というよりは、実際にはこういう項に変換されているようなものだと思える。

## 定理証明で書こうとすると
ユークリッド互除法に戻る。
$x = (n, m)$ みたいに書いておく。
```
rec f n m = \
    if n \leq m  then f m n else \
      let n' := n div m
      if n' == 0 then m else f m n' \
```
これは単純には帰納法をやっているわけではないので、受け入れることができる形をしていない。
しかし、停止するはずなので、この項自体は定理証明にいれても大丈夫なはず。

これがなぜ停止するのかというと、直感的には、
- $n \leq m$ の場合は $n > m$ に帰着させる。
- $n > m$ の場合は、 $f$ の呼び出しごとに $n + m$ が小さくなるので、停止する。
からになる。

### 方法1
$n > m$ に限ってまず $n + m$ に関する帰納法が使えるような形にしたい。
直感的には、次のような形で定義する。
（ coq で通るわけではないが。）

```
fix euc'1: (n: N) -> (m: N) -> (p1: n > m) -> (l: N) -> (p2: n + m \leq l) -> \mathbb{N} :=
  match l with
  | Z => Z // n = m = 0 なのでよい。
  | S l' =>
    let n': \mathbb{N} := n div m in
    if n' == 0 then m else
      let p1': m > n' := ... // n div m と m の大きさについての命題から証明項ができる。
      let p2': m + n' \leq l' := ... // n + m < m + (n' = n div m) より証明項ができる。
      euc' m n' p1' l' p2'

let euc'2: (n: N) -> (m: N) -> (p: n > m) -> N := euc'1 n m p (n + m) (refl_(N, n + m))

let euc: (n: N) -> (m: N) -> N :=
  match n ? m with
  | (p: n \leq m) =>
    let p': m > n := ... // p からつくる
    euc'2 m n p'
  | (p: n > m) =>
    euc'2 n m p
```
本質的には `l` についての帰納法になっている。

### 方法2
この構成以外にも、 well-founded に対応するような型を定義して、そっちの帰納法でまわすのもできる。
```
// 計算が停止できる引数の定義
inductive A: (x: \mathbb{N} times \mathbb{N}) -> Type :=
  | A1: (n: N) -> (m: N) -> (n \leq m) -> A m n -> A n m
  | A2: (n: N) -> (m: N) -> (n > m) -> (n div m == 0) -> A n m
  | A3: (n: N) -> (m: N) -> (n > m) -> (n div m != 0) -> A m (n div m) -> A n m

// 計算が停止する証拠に関する帰納法
let euc' = fix euc: (n: N) -> (m: N) -> (p: A n m) -> N :=
  match p with
  | A1 _ _ (_: n \leq m) (t: A m n) => euc m n t
  | A2 _ _ (_: n > m) _ => m
  | A3 _ _ (_: n > m) _ (t: A m (n div m)) => euc m (n div m) t 

// 全ての引数で停止する証明
let totality: (n: N) -> (m: N) -> A n m := ...
  // ここで結局 n + m \leq l を使って l に関しての帰納法で定義する

let euc: (n: N) -> (m: N) -> N := euc' n m (totality n m)
```

### 問題
coq ではこういうのは微妙にまずくて、
`Prop` に入っている型は、それの帰納法を使って計算ができない。
なので、 `Type` につくって代わりにするなどが必要（だったはず）。

あと、ともに `euc` 自体は関数の外延性が成り立つが、そのなかで定義している補助的な関数では外延性が成り立たない。

### こっちの体系では...
ある意味では、それに依存しないという意味で、 `n + m \leq l` を使うのは take の仕様の目的に合致している気がする。
問題は、 take では reduction がやれないこと。
（無理にやろうとすると多分大変な気がする。）
こっちの体系で書こうとするとこんな感じ？
（ただし、 `a: {x: T | P}` を書くのがめんどくさいと適当に s.t. を使う。）
```
// 結局 l' をとらないと euc' は書けない！（停止性の証明）
rec euc' (n: N) (m: N s.t. n > m) (l: N s.t. n + m \leq l) :=
  match l with
  | Z => Z
  | S l' =>
    let n' := n div m
    if n' == 0 then m else euc' m n' l'

// ここは"本質的に l によらない"だけを示しているようなもの
let euc: (n: N) -> (m: N) -> N := take (l: N s.t. n + m \leq l). euc' n m l
```

## アイディア
計算と記述をわけることで、
「記述の側で take や構造帰納法などを使って停止することが証明できるなら、それに対応する計算側の項を認めてよい。」
とすることができそうだ。
この場合、記述の方では構造帰納法以外の recursion を認めないほうが、多分うまくいきそう。

この場合、 sort を増やして Prop, Set, Comp のようにわける。

- $\mathcal{S} = \{*^p, *^s, *^c, \square\}$
- $\mathcal{A}= {(*^p: \square), (*^s, \square)}$
- $\mathcal{R} =$
  - ${(*^p, *^p), (*^p, \square), (\square, *^p), (\square, \square)}$
  - ${(*^s, *^s), (*^s, \square), (*^s, *^p)}$

この上で、 $*^c$ から $*^s$ への reflection を行う。
具体的には、
項を $::= .. | \text{Rf}(t)$ のように拡張し、
$\text{Rf}(t)$ の変換を次のように行う
- $\text{Rf}(*^c) \to *^s$
- $\text{Rf}(\lambda x:T. t) \to \lambda x: (\text{Rf} T). (\text{Rf} t)$
- $\Pi$ や app なども同じ
- $\text{Rf}(m) \to^\beta \text{Rf}(m')$ if $m \to^\beta m'$

また、帰納的な型として $*^c$ 側に定義されたものは、
その reflection に対応する型を自動的に $*^s$ につくり、 $\text{Rf}$ といい感じになるようにつくる。
例えば自然数の場合、
- type form ... $\mathbb{N}$: $*^c$ ::=
  - type intro Z ... $Z$: $\mathbb{N}$
  - type intro S ... $S$: $\mathbb{N} \to \mathbb{N}$
と書くと
- elim rule ... $\text{elim}_\mathbb{N}$
- computation rule ...

が勝手に出てくるが、
これにさらに $*^s$ 側で対応する $\hat{\mathbb{N}}, \hat{Z}, \hat{S}, \hat{\text{elim}_\mathbb{N}}$ を導入する。
そして、 $\text{Rf}(\mathbb{N}) = \hat{\mathbb{N}}$ などのように変換規則を拡張する。

"rec" 付きの項を "Rf" で "rec" のない世界 $*^s$ 側で表現できているのであれば、
"rec" が付いていても止まりそう（な気がする）。

$$
  \dfrac{
    \Gamma \vdash \Pi x: (\text{Rf} T). ((\text{Rf} (\text{rec $f$ $x$ = $M$}) x) =_T t x)
  }
  {
    .... \quad
    \Gamma \vdash (\text{rec $f$ $x$ = $M$}): \Pi x: T. M',
  }
$$

とりあえず考えただけなので、整合性があるかは不明。

あとで帰納型を含めてちゃんと考える。

## McCarthy 91 function
$$ M(n) = \begin{cases}
 n - 10 & n > 100
 M(M(n)) & \text{otherwise}
\end{cases} $$

これも項として存在できるならうれしい。
