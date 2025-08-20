ZFC をちゃんと思い出す。
(Wikipedia 見ればいいと思う。)
一回述語論理で $=$ と $\in$ があって、 $=$ が $\in$ で定義づけられている。
また、変数以外はすべて論理式である。

## 項と式の定義
- term $t$ ::=
  - variable $x$
- atomic formula $p$ ::=
  - set-in $t \in t$
- formula $\phi$ ::=
  - atomic formula $p$
  - negative $\neg \phi$
  - and $\phi \wedge \phi$
  - or $\phi \vee \phi$
  - implies $\phi \to \phi$
  - forall $\forall x. \phi$
  - exists $\exists x. \phi$

$\phi[x := t]$ が定義されていることに注意。
もし注目している論理式 $P$ がさらに自由変数 $x$ を持っていてこれに注目して議論する場合には $P(x)$ と書く。
また、 $P(y)$ は $P[x := y]$ とする。
（まあこういうのは使わないほうがいい。）

次の略記を導入する。
- $\phi_1 \leftrightarrow \phi_2$ ... $(\phi_1 \to \phi_2) \wedge (\phi_2 \to \phi_1)$
- $t_1 \notin t_2$ ... $\neg (t_1 \in t_2)$
- $t_1 = t_2$ ... $\forall x. t_1 \in x \leftrightarrow t_2 \in x$
- $t_1 \not = t_2$ ... $\neg (t_1 = t_2)$
- $t_1 \subset t_2$ ... $\forall x. x \in t_1 \to x \in t_2$
- $\forall x \in A. \phi$ ... $\forall x. x \in A \to \phi$
- $\exists x \in A. \phi$ ... $\exists x. x \in A \to \phi$
- $\exists ! x. \phi$ ... $(\exists x. \phi) \wedge \forall y. \phi[x := y] \to x = y$

（ **代入は$\phi[x := \phi']$ のような形ではできない。** 変数しか項がないので、空集合を代入するとかの場合、ちょっとめんどくさい。 ）

## 集合の代入について
例えば、空集合とは $\phi = \forall x. \neg (x \in y)$ を満たす **$y$のこと**。
もちろん、 $y$ という変数でなければいけないというわけではないが、論理式ではなく変数であることは重要。
$\phi \in x$ は書けないので、代わりに $(\forall x. \neg (x \in y)) \to (y \in x)$ のように書く必要がある。
（前提部分は、 「$y$ を空集合として ... 」みたいに読める。）

これを一般の場合に発展させると、「メタ集合 $X$ を、 論理式 $\phi$ と変数 $y$ により、**一意に定まる** 集合とする」状態では、
$x \in X$ や $X \in x$ を $\phi \to (x \in y)$ や $\phi \to (y \in x)$ と解釈すること。
読み方としては、 $x \in \emptyset$ を 「$\text{y を空集合の条件を満たす集合とするとき} x \in y$」 みたいに読む感じ。

一意に定まるので、 $\forall x_1. \forall x_2. (x_1 \in X) \to (X \in x_2)$ のような状況でも、（多分）どちらでもよくなるはず。
- $\forall x_1. \forall x_2. (\phi \to x_1 \in y) \to (\phi \to y \in x_2)$
- $\phi \to (\forall x_1. \forall x_2. (x_1 \in y) \to (y \in x_2))$

これだと後者の方が"正当"に見えて、前者だと $\to$ の前後で $y$ の意味合いが変わっているように見えるが、
$\phi$ を満たす"集合"が一意に定まっている状況を考えているので、問題ない。

- [ ] 形式論理で全然形式的な議論をできていないのは変な気がする。ここら辺は多分、ちゃんと厳密にやろうとしている教科書なら乗っているはずだから、調べておくこと。

## 一回述語論理の導出木（シーケント計算とかでいい）
sequent $\Gamma$ := List of formula

- (I) $[\phi] \vdash [\phi]$
- (Cut) $\Gamma_1 :: \Gamma_2 \vdash \Gamma_3 :: \Gamma_3$ if $\Gamma_1 \vdash \Gamma_3::\phi, \phi::\Gamma_2 \vdash \Gamma_4$
- ...

まあどれを使ってもできることは同じ。

## ZFC の理論
$T$: sets of formula := union of
- equality: $\forall x. \forall y. ((\forall z. (z \in x \leftrightarrow z \in y)) \to x = y)$
- regularity: $\forall x. ((\exists a. a \in x) \to \exists y. (y \in x \to \neg (\exists z. z \in y \wedge z \in x)))$
- restricted comprehension: $\forall z. \exists y. \forall x. x \in y \leftrightarrow x \in z \wedge \phi$ の全称閉包
  - $y \notin \text{FV}(\phi)$
- empty set: $\exists y. \forall x. x \notin y$
- pairing: $\forall x. \forall y. \exists z. (x \in z \wedge y \in z)$
- union: $\forall z. \exists a. \forall x \in a. \wedge a \in z \to x \in z$
- replacement: $\forall A. ((\forall x \in A. \to \exists ! y. \phi) \to \exists B. \forall x \in A. \exists y \in B. \phi)$ の全称閉包
  - $y \notin \text{FV}(\phi)$
- powerset: $\forall x. \exists y. \forall z. z \subset x \to z \in y$
