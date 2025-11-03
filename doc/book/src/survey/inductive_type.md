# 帰納型について
mutualy でない帰納型を定義することを考える。
（Frank Pfenning Christine Paulin-Mohring より）

型の定義の宣言は次のようになる。
$$\begin{align*}
\textbf{inductive} \quad & a: (z_1: Q_1) \to \cdots \to (z_n: Q_n) \to s \textbf{ with } \\
& c_1: (x_1: P_{1, 1}) \to \cdots \to (x_(k_1): P_{1, l_1}) \to a M_{1, 1} \cdots M_{1, n} \\
& \vdots \\
& c_k: (x_1: P_{k, 1}) \to \cdots \to (x_(k_1): P_{k, l_1}) \to a M_{k, 1} \cdots M_{k, n}
\end{align*}$$

例として、自然数の定義は次のようになる。
$$\begin{align*}
\textbf{inductive} \quad & \mathbb{N}: *_s \textbf{ with } \\
& \text{Zero}: \mathbb{N} \\
& \text{Succ}: (\_: \mathbb{N}) \to \mathbb{N} 
\end{align*}$$

こういう形をしていること自体は全然良い。
気を付ける必要があるのが次のもの。
- どうやって computation rule を定めるか
- Coq とかである strictly positivity の条件について

$c_1$ とかの名前はあまり関係なくて、 $a$ を変数とみると inductive な型を定めるなら、
- type を定める ... これは $(z_1: Q_1) \to ...$ の部分でよい。
- constructor を定める ... $a$: 変数に対しての $(x_1: P_1) \to \cdots \to (x_k: P_k) \to a M_1 \cdots M_n$ をとる。

があればよい。
**型の名前を変数とみることが重要**

## 定義
~Coquand と Paulin-Mohring の inductively defined types とか、Coq の reference を参考にする。~
Timany, Jacobs のほうがわかりやすかったので、それを参考にする。

帰納型の型の取ることのできる parameter を arity というが、これは簡単に定義できて、 $(x_0: A_0) \to \cdots \to (x_n: A_n) \to s$ の形をしたものを $s$ の arity という。

帰納型のコンストラクタの定義は制限がある：コンストラクタの引数に現れる $P$ は無制限にはできない。
（矛盾するから。）
変数 $X$ に対して、 $P$ は strictly positive に現れる必要がある。

1. $P$ に $X$ が現れない
2. $P = X m_1 ... m_k$ かつ $m_i$ は $X$ を含まない
3. $P = (x: K) \to \Phi$ で $K$ は $X$ なし、 $\Phi$ は $X$ に対して strictly positive

変数 $X$ に対して、 constructor としての適格性の条件は次のいずれかをみたすとき
- $\Theta = X m_1 \cdots m_k$ で $m_i$ は $X$ を含まない
- $\Theta = (X: P) \to \Theta_0$ で
  - $P$ は $X$ に対して strictly positive
  - $\Theta_0$ は $X$ に対する constructor

strictly positive の形を見ると再帰的な定義になっているがそれが終了するのは (1) か (2) である。
(2) と (3) だけまとめて考えると、これで得られる項は $(x_1: K_1) \to ... (x_n: K_n) \to X m_1 ... m_k$ の形をしている。（ただし、 $K_i$ は $X$ を含まない）
(1) と (3) だけまとめて考えると、これでえられる項は $X$ を含むことがない。
Timany と Jacobs のではこれをわけて前者を strictly positive と呼んでる。

帰納型の指定は、次の4つでよい。
- $X$: 変数
- $s$: sort
- $A$: arity of $s$ 
- $\{C_i\}$: constructor of $X$

## 帰納型受け入れの条件
帰納型の宣言が与えられたときに、それを受け入れてよい条件について。
注意点として、帰納型の定義自体には free variable が含まれうる。
だから、外側のコンテキストにある変数に応じて定義されていることがある。
例えば polymorphic list の場合：
$\Gamma = A: *$ のもとで考えるなら、
$$\begin{align*}
\textbf{inductive} \quad & \textit{list}: * \textbf{ with } \\
& \textit{nil}: \textit{list} \\
& \textit{cons}: A \to \textit{list} \to \textit{list}
\end{align*}$$
という、 $A$ 自体が $\text{list}$ の宣言の中で縛られていないような宣言もしてよい。
これがあるので、宣言の parameter と index が分かれている？
（例えば Coq の polymorphic list は parameter の位置に `A: Set` が来るのは許すが、 index の位置に `A: Set` が来るのは許さない。
`A: Set` という自由変数のもとで考えるのが parameter で、 arity の位置に来ているのが index になっているっぽい。）

次の宣言が与えられたとする。
- $X$: 変数
- $s$: sort
- $A$: arity of $s$ 
- $\{C_i\}$: constructor of $X$

このときの受け入れの条件は、
- $\Gamma \vdash A: s'$ ... これは $s$ とは異なっていていい。
- $\Gamma, X: A \vdash C_i: s$ ... これは sort $s$ を使う。

注意点として、これは Coq 用の定義なのでそのまま流用できるかは怪しい。
ただ、定義自体には cumulative とかも表れていないので、そのまま一般の PTS に対して適用できる。

## eliminator と recursor
よくある pattern match と primitive recursion をどうやって判定したらよいかについて。
なんでもかんでも受け入れることはできないのはわかっている。
Coq ではパターンマッチと fix の引数の減少を指定するようだが、ここでは、 recursor を計算する方法を使う。
例えば自然数だと、eliminator は次のような型になっていたはずだが、これを自動的に導出したい。

$$\begin{align*}
&(P: (n: N) \to T) \\
&\to (a_\text{Zero}: P @ \text{Zero}) \\
&\to (a_{\textop{Succ}}: (n: N) \to P @ n \to P @ (\textop{Succ} n)) \\
&\to (n: N) \to P @ n
\end{align*}$$

eliminator には eliminator に入れる項以外に、return する項の情報も入れておきたい。
Coq や Lean の elim だと書かなくても推測されるが、複雑な場合には書く。
coq の match だと return で、 lean だと motive と呼ばれているやつ。

$\text{elim}(c, Q)(f_1, ... f_n)$ が eliminator の形で、 $c$ は分解する項、 $Q$ は帰ってくる型、 $f_i$ は constructor それぞれに対応する場合分けの計算とする。

- 帰納型の定義にある arity of $s$ は当然型が付かないといけない。
- 帰納型の定義にある constructor of $X$ ($C_i$) は、 $\Gamma :: X: \text{arity} \vdash C_i: s$ でなければいけない。

各 constructor に対する型はこんな感じ。
- elim_type(THIS a[], q, c, THIS) = q a[] c
  - `THIS` のところには型名が来る想定
- simple case: elim_type((x: t) -> n, q, c, THIS)
  - = (x: t) -> elim_type(n, q, c x, THIS)
- strpos case: elim_type(((x[]: t[]) -> THIS m[]) -> n, q, c, THIS)
  - = (p: (x[]: t[]) -> THIS m[]) // `THIS` のところには型（ parameter が与えられている）が来る想定
  - -> (_: (x[]: t[]) -> q m[] (p x[]))
  - -> elim_type(n, (c p), THIS)

各 constructor に対する recursor はこんな感じ。
- recursor(THIS a[], q, f, THIS) = f
- simple case: recursor((x: t) -> n, q, f, THIS)
  - = (x: t) => recursor(n, q, (f x), THIS)
- strpos case: recursor(((x[]: t[]) -> THIS m[]) -> n, q, f, THIS)
  - = (p: (x[]: t[]) -> THIS m[])
  - => recursor(n, q, (f p ((x[]: t[]) -> q m[] (p x[]))), THIS)

recursor に対する動作について。
型は index = (x[]: a[]) -> s となっているとする。
- Elim((i-th Cst of Type I) m[], q, f[])
- => recursor(ff, f[i], C[i]) m[]
- where ff = (x[]: a[]) => (c: (Type x[])) => Elim(Type, c, q, f[])

型はこんな感じ。(s は sort)
- THIS = { arity: (x[]: t[]) -> s, constructors: C[] }
- Elim(c, q, s', f[]): q a[] c
  - c: THIS a[]
  - a[]: t[]
  - q: (x[]: t[]) -> THIS x[] -> s'
  - f[i]: elim_type(C[i], q, c, THIS)

## parameter と index について

Set が impredicative であることを考えると、次のような polymorphic なリストは定義できない。
```Coq
Inductive List: forall a: Set, Set :=
  | Nil: forall a: Set, List a
  | Cons: forall (a: Set), a -> List a -> List a
.
```
エラーの理由は、 `Large non-propositional inductive types must be in Type` になる。
理由は、 Nil の型について、 $\text{List}: (A: \text{Set}) \to \text{Set} \vdash ((A: \text{Set}) \to \text{List} A): \text{Set}$ でないから、
これには $(\text{Type}, \text{Set}) \in \mathcal{R}$ が必要になる（$\Rightarrow$ Set が impredicative である必要がある）。

一方で、次のような、 parametrized な場合は大丈夫。
```Coq
Inductive List (a: Set): Set :=
  | Nil: List a
  | Cons: a -> List a -> List a
.
```

これは、各 `A: Set` ごとに Set の元として `List A` を定義しているから。
このとき、 `List` は `Set -> Set` になる。
これについては、 Lean でも注意があって、
[https://leanprover.github.io/functional_programming_in_lean/dependent-types/indices-parameters-universes.html] というところで書かれている。

Inductive type の定義でいうと、context にそのまま入っていると思える部分になる。
型の宣言とコンストラクタへの引数として一体化していると考えたほうがいい？

## Identity type について
parameter と index の話を踏まえると、 Identity type は `A: Set` と `a: A` は parameter で、 `b: A` が index となる。

# W-type について
- [ ] TODO
