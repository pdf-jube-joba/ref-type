体系の judgement が 4 つあって相互再帰的に定義されているから、大体の命題も、相互再帰的に定義するしかない。

#### free variable について
- $\text{WF}(x_1: A_1:: \cdots :: x_n: A_n)$ なら $x_i$ はすべて異なり、 $\text{FV}(A_i) \subset \{x_1, \ldots, x_{i-1}\}$
- $\Gamma \vdash t: T$ なら $\text{FV}(t), \text{FV}(T) \subset \Gamma$
- $\Gamma \vDash P$ なら $\text{FV}(P) \subset \Gamma$
- $\Gamma \vdash X_1 \leq X_2$ なら $\text{FV}(X_1), \text{FV}(X_2) \subset \Gamma$

証明は、導出木に関する帰納法を用いる。

#### substitution lemma
$\Gamma \vdash t: T$ とする。
- $\text{WF}(\Gamma:: x: T::\Gamma')$ なら $\text{WF}(\Gamma::(\Gamma'[x := t]))$
- $\Gamma:: x: T::\Gamma' \vdash M: N$ なら $\Gamma::(\Gamma'[x := t]) \vdash M[x := t]: N[x := t]$
- $\Gamma:: x: T::\Gamma' \vDash P$ なら $\Gamma::(\Gamma'[x := t]) \vDash P[x := t]$
- $\Gamma:: x: T::\Gamma' \vdash X_1 \leq X_2$ なら $\Gamma::(\Gamma'[x := t]) \vdash X_1[x := t] \leq X_2[x := t]$

Note:
$\vdash M: N$ のときの $\Gamma' = \emptyset$ でその導出が var のときが base case である。
$\Gamma :: x: t \vdash x: t$ if $\text{WF}(\Gamma)$ なので、この場合、 $\Gamma \vdash x[x := t]: T[x := t]$ を示すが、これは前提の $\Gamma \vdash t: T$ である。

証明：
$\Delta = \Gamma :: x: T :: \Gamma'$, $\Delta^* = \Gamma:: \Gamma'[x := t]$ とする。

各結論の前提（ 「hoge なら huga」 の hoge の部分）の導出木に関する帰納法を用いる。
- empty, axiom の場合 ... 明らか。
- start の場合 ... $\Delta = \Delta':: x': T'$ によって $\text{WF}(\Delta'::x': T')$ if $\Delta' \vdash T': s'$ が成り立っている。
  帰納法の仮定から、
