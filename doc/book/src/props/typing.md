体系の judgement が 4 つあって相互再帰的に定義されているから、大体の命題も、相互再帰的に定義するしかない。

## free variable について
> - $\text{WF}(x_1: A_1:: \cdots :: x_n: A_n)$ なら $x_i$ はすべて異なり、 $\text{FV}(A_i) \subset \{x_1, \ldots, x_{i-1}\}$
> - $\Gamma \vdash^s t: T$ なら $\text{FV}(t), \text{FV}(T) \subset \Gamma$
> - $\Gamma \vdash t: s$ なら $\text{FV}(t) \subset \Gamma$
> - $\Gamma \vDash P$ なら $\text{FV}(P) \subset \Gamma$
- 証明は、導出木に関する帰納法を用いる。

## variable の導出
> $\text{WF}(\Gamma)$ かつ $(x: T) \in \Gamma$ なら $\Gamma \vdash x: T$

証明：
$\text{WF}(\Gamma)$ は empty と start のみから導出されているので、
$\Gamma = \Gamma_1 :: (x: T) :: \Gamma_2$ に対して $\text{WF}(\Gamma)$ の導出木を分析すれば、
$\Gamma_1 \vdash T: s, x \notin \Gamma \implies \text{WF}(\Gamma_1::(x:T))$ の部分があるはず。
ここから、 $\Gamma_1 :: x: T \vdash x: T$ が示せて、あとは weak を $\Gamma_2$ に合わせて広げていくだけ。

## substitution lemma
> $\Gamma \vdash t: T$ とする。
> - $\text{WF}(\Gamma:: x: T::\Gamma')$ なら $\text{WF}(\Gamma::(\Gamma'[x := t]))$
> - $\Gamma:: x: T::\Gamma' \vdash^s M: N$ なら $\Gamma::(\Gamma'[x := t]) \vdash^s M[x := t]: N[x := t]$
> - $\Gamma:: x: T::\Gamma' \vdash M: s$ なら $\Gamma::(\Gamma'[x := t]) \vdash M: s$
> - $\Gamma:: x: T::\Gamma' \vDash P$ なら $\Gamma::(\Gamma'[x := t]) \vDash P[x := t]$

Note:
$\vdash M: N$ のときの $\Gamma' = \emptyset$ でその導出が var のときが base case である。
$\Gamma :: x: t \vdash x: t$ if $\text{WF}(\Gamma)$ なので、この場合、 $\Gamma \vdash x[x := t]: T[x := t]$ を示すが、これは前提の $\Gamma \vdash t: T$ である。

証明：
$\Delta = \Gamma :: x: T :: \Gamma'$, $\Delta^* = \Gamma:: \Gamma'[x := t]$ とする。

各結論の前提（ 「hoge なら huga」 の hoge の部分）の導出木に関する帰納法を用いる。
この議論はちょっとわかりにくいので補足する。
$\Gamma, t, T, x$ は固定する。
context $\Gamma'$ についての命題が「 $\Gamma::x: T::\Gamma'$ についてのそれぞれの命題の導出木 $D$ （相互再帰がここで入る）」
をもとに $P(\Gamma') = \forall D. Q(\Gamma', D)$ として得られていると思えば、この導出木に関する帰納法が使えるということ。
（導出木の長さに関する帰納法を用いていると思ってもいいかも）

- empty, axiom の場合 ... 明らか。
- start の場合 ... $\Delta = \Delta':: x': T'$ によって $\text{WF}(\Delta'::x': T')$ if $\Delta' \vdash T': s'$, $x \notin \Gamma$ が成り立っている。
  - もし $\Delta' = \Gamma$ なら（つまり $\Gamma' = \emptyset$）：これはまさに Note で書いた base case である。
  - そうじゃないなら、帰納法の仮定から、 $\forall D'. P(\Delta', D')$ が帰納法の仮定から得られているので、
    $\Gamma::\Delta'[x := t] \vdash T'[x := t]: s$ がわかっている。
    ここの仮定から $\text{WF}(\Gamma::\Delta'[x := t]::x': T'[x := t])$ が得られるから、示すべきことが示されている。
- weak の場合 ... (start と同じようなもの) $\Delta = \Delta':: x': T'$ によって $\Delta'::x': T' \vdash M: N$ if $\Delta' \vdash M: N, \text{WF}(\Delta'::x':T')$ が成り立っている。
  - もし $\Delta' = \Gamma$ なら （つまり $\Gamma' = \emptyset$）： $\Gamma \vdash M: N, \text{WF}(\Gamma \vdash x: T)$ から
    $\Gamma ::x: T \vdash M: N$ を導出している。
    示すのは $\Gamma \vdash M[x := t]: N[x := t]$ であるが、 $x \notin \text{FV}(M), \text{FV}(N)$ がわかるから、これは $\Gamma \vdash M: N$ になり、示されている。
  - そうじゃないなら、帰納法の仮定から、 $\Gamma ::\Delta'[x := t] \vdash M[x := t]: N[x := t]$ と $\text{WF}(\Gamma ::\Delta'[x := t]::x': T'[x := t])$ が得られているから、そのまま $\Gamma::\Delta'[x := t]::x': T'[x := t] \vdash M[x := t]: N[x := t]$ の導出木にできる。
- conversion の場合 ... premises に現れる context が減ってないので、帰納法の仮定から得られるものをそのまま適用すればいい。
  これがわかりやすいので、ちゃんと書いてみる。
  $\Gamma:: x: t :: \Gamma' \vdash t': T_2$ if $\Gamma::x:t::\Gamma' \vdash t': T_1, \Gamma::x:t::\Gamma' \vdash T_2: s, T_1 \equiv T_2$ と導出されていて、
  帰納法の仮定から $\Gamma::\Gamma'[x:=t] \vdash t'[x:=t]: T_2[x:=t]$ と $\Gamma::\Gamma'[x:=t] \vdash T_2[x:=t]:(s[x:=t] \equiv s)$ が得られている。
  これをそのまま導出木にしてしまえばいい。チェックするのは、 $T_1[x:=t] \equiv T_2[x:=t]$ だがこれは成り立つ。 
- variable, dep.form, dep.intro, provable list, power-sub list, set-rel list, identity list の全部、 exists intro exist form では上と同じ議論が使える。
- dep.elim の場合：
  $\Delta \vdash f @ a: T[x' := a]$ if $\Delta \vdash f: (x': t'. a), \Delta \vdash a: t'$ としておく。
  示すのは $\Delta^* \vdash (f @ a)[x := t]: T[x' := a][x := t]$ だが、
  これは代入順序の補題を用いれば $\Delta^* \vdash (f[x := t] @ a [x := t]): T[x := t][x' := a[x := t]]$ と同じなので、
  帰納法の仮定の $\Gamma' \vdash f[]: ()[], \Delta \vdash a[]: t'[]$ から導出できる。
- take.intro. の場合：
  $\Delta \vdash (\Take x': T'. m): M$ if $\Delta \vdash T': *^s, \Delta \vdash M: *^s, \Delta ::x': T' \vdash m: M, \Gamma \vDash \exists T', \Gamma \vDash (y_1: T') \to (y_2 : T') \to m[x := y_1] =_M m[x := y_2]$ からきているとする。
  （ $x'$ は $t$ に出現しないような変数。）
  示すのは $\Delta \vdash (\Take x': (T'[x := t]).(m[x := t])): M[x := t]$ なので、
  まずは帰納法の仮定から得られる、 premise それぞれに $[x := t]$ を付けたものを考える。
  そこから自然に得られる導出木はほとんど気にしなくてよくて、 $\Gamma \vdash (y_1: T'[]) \to (y_2 : T'[]) \to m[x' := y_1][x := t] =_M m[x' := y_2][x := t]$ だけ気にしないといけない。
  ただこれは、代入順序の補題から、 $\Gamma \vdash \cdots m[x := t][x' := y_1] =_M m[x := t][x' := y_2]$ とできるからよい。
- take.elim （ bind あり）の場合：
  これも気にするのは、 $ \cdot =_M m[x' := e]$ の代入の順番であるが、 $m[x' := e][x := t] = m[x := t][x' := e[x := t]]$ よりよい。

## generation lemma (inversion)
### sort まわり
> - $\Gamma \not \vdash \square:  s$
> - $\Gamma \vdash *^p: s$ なら $s = \square$
> - $\Gamma \vdash *^s_i: s$ なら $s = *^s_{i+1}$
- 証明は普通に木を見ればいい。

> - $\Gamma \not \vdash^s \square: T$ 
> - $\Gamma \not \vdash^s *^p: T$
- これも同じ。 type.elem では上の命題から。

> $\Gamma \vdash^s *^s_i: T$ なら $s = *^s_{i+2}$
