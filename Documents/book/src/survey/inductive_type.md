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
(2) と (3) だけまとめて考えると、これで得られる項は $(x_1: K_1) -> ... (x_n: K_n) -> X m_1 ... m_k$ の形をしている。（ただし、 $K_i$ は $X$ を含まない）
(1) と (3) だけまとめて考えると、これでえられる項は $X$ を含むことがない。
Timany と Jacobs のではこれをわけて前者を strictly positive と呼んでる。

帰納型の指定は、次の4つでよい。
- $X$: 変数
- $s$: sort
- $A$: arity of $s$ 
- $\{C_i\}$: constructor of $X$

## eliminator と recursor
よくある pattern match と primitive recursion をどうやって判定したらよいかについて。
なんでもかんでも受け入れることはできないのはわかっている。
Coq ではパターンマッチと fix の引数の減少を指定するようだが、ここでは、 recursor を計算する方法を使う。
例えば自然数だと、eliminator は次のような型になっていたはずだが、これを自動的に導出したい。


