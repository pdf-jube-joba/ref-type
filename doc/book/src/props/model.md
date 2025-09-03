示したいのは、 Consistency で、「ZFC + いい感じの仮定」のもとでのモデルを作ることで、
$\vdash \forall P. P$ が示せないことを示す。
これには、 $\lvert \Vdash (P: *^p) \to P \rvert = \emptyset$ であることを示せばよい。

the not so simple model CoC を参考にする。
次のように定義しておく。
- prop 用
  - $0 = \bullet = \emptyset$ ... これは、 unique な元として、後述する $\mathbb{B}$ が Bool っぽくなるようにしている。
  - $1 = \{ \bullet \}$
  - $\mathbb{B} = \{ \bullet, \{\bullet \} \} = \{0, 1\}$
- $V_i$: set であって、 inaccessible とかいうやつだが、必要なのは、
  - べき集合で閉じること
  - dependent prod に対応するもので閉じること。
- $U$: $\mathbb{B}$ を含む、 inaccessible みたいなやつ。

普通のラムダ部分は論文に習えばいい。
ただし、 proof-term かどうかとか、 well-sorted ness を考える必要がある。
（それで定義を分岐するから。）

sort が $(s_1, s_2, s_2) \in \mathcal{R}$ の形なので、 sort-elem function は簡単に定義できる。
ふつうのラムダ以外は決め打ちできるはず。
- $e(s) = A(A(s))$
- $e(x^s) = s$
- $e((x: A) \to B) = e(\lambda x: A. B) = e(B a) = e(B)$
- $e(\Power A) = \square$
- $e(\{A \mid P\}) = *^s$
- $e(\Pred(A, B)) = \square$
- $e(\Ty(A, B)) = \square$
- $e(a = b) = \square$
- $e(\exists t) = \square$
- $e(\Take f) = *^s$

解釈は任意の $\Gamma$ と $t$ に対して $\lvert \Gamma \Vdash t \rvert$ は次。
- PTS っぽいところ
  - $\lvert \Gamma \Vdash *^p \rvert = \mathbb{B}$
  - $\lvert \Gamma \Vdash *^s_i \rvert = V_i$
  - $\lvert \Gamma \Vdash \square \rvert = U$
  - $\lvert \Gamma \Vdash p \rvert = \bullet$
    - $\Uparrow$ if $e(p) = *^p$
  - $\lvert \Gamma \Vdash x^\square \rvert _\gamma = \pi_i \gamma$ if $x^\square$ is $i$-th
  - $\lvert \Gamma \Vdash \lambda x: A. t \rvert _\gamma = \alpha \in \lvert \Gamma \Vdash A \rvert \mapsto \lvert \Gamma; x: A \Vdash t \rvert _{(\gamma, \alpha)}$
  - $\lvert \Gamma \Vdash f @ a  \rvert _\gamma = \lvert \Gamma \Vdash f \rvert _\gamma (\lvert \Gamma \Vdash a \rvert _\gamma)$
  - $\lvert \Gamma \Vdash (x: A) \to B \rvert = \{f \in \{ \bullet \} \mid \forall \alpha \in \lvert \Gamma \Vdash A \rvert _\gamma , f \in \lvert \Gamma; x: A \Vdash B \rvert _{(\gamma, \alpha)} \}$
    - $\Uparrow$ if $e(B) = \square$
  - $\lvert \Gamma \Vdash (x: A) \to B \rvert = \Pi_{\alpha \in \lvert \Gamma \Vdash A \rvert _\gamma} \lvert \Gamma; x: A \Vdash B \rvert _{(\gamma, \alpha)}$
- ここ以降がちゃんと定義しないといけない部分
  - $\lvert \Gamma \Vdash \Proof p \rvert _\gamma = \bullet$
  - $\lvert \Gamma \Vdash \Power (A) \rvert _\gamma = \mathcal{P}(\lvert \Gamma \Vdash A \rvert _\gamma)$
  - $\lvert \Gamma \Vdash \{A \mid P\} \rvert _\gamma = \{x \in \lvert \Gamma \Vdash A \rvert _\gamma \mid \bullet \in \lvert \Gamma \Vdash P \rvert _\gamma (x) \}$
  - $\lvert \Gamma \Vdash \Ty(A, B) \rvert _\gamma = \{x \in \lvert \Gamma \Vdash A _\gamma \rvert \mid x \in \lvert \Gamma \Vdash B \rvert _\gamma\}$
  - $\lvert \Gamma \Vdash \Pred(A, B, t) \rvert _\gamma = \{a \in \{\bullet\} \mid \lvert \Gamma \vdash t \rvert _\gamma \in \lvert \Gamma \vdash B \rvert \}$
  - $\lvert \Gamma \Vdash a = b \rvert _\gamma = \{\bullet \mid \lvert \Gamma \Vdash a \rvert _\gamma = \lvert \Gamma \Vdash b \rvert _\gamma\}$
  - $\lvert \Gamma \Vdash \exists t \rvert _\gamma = \{ \bullet \mid \lvert \Gamma \vdash t \rvert _\gamma \not = \emptyset \} $
  - $\lvert \Gamma \Vdash \Take f \rvert _\gamma = y \mathrel{\text{s.t.}} \exists x, (x, y) \in \lvert \Gamma \vdash f \rvert _\gamma$
    <br> これの型が $X \to Y$ なら $f \subset X \times Y$ なのでこう書けるはず。
    $\text{s.t}$ の意味が不明瞭に見えるけれど、そもそも集合自体、自由変数で導入した後に論理式で定義を用いるのでよい。
    （ $z \in \{y \in x \mid \phi(y, x)\}$ が $(k \in l \leftrightarrow \phi(y, k)) \rightarrow z \in l$  になるのと同じ。）

subst は大丈夫だと思うので飛ばす。
reduction に対してどうふるまうかがみたい。
congruent な部分はだいたい大丈夫なはずで、問題は reduction のあるところ。
ラムダの話は 『not so simple ..』 にのってる。
- $M = (\lambda x^s: A. t) @ u \to t[x := u]$ の場合：
  - $e(M) = *^p$ の場合には、 $s = *^p$ のはずで、 $\lvert A[x^{*^p} := u] \rvert = \lvert \Gamma; x: t \vdash A \rvert _{(\gamma, \lvert u \rvert)}$ が subst からわかる。
  - $e(t) = *^p$ だが $e(M) \not = *^p$ なら、これも同様の議論
  - どちらでもない場合には、これは function になっている。
- $M = \Pred(A, \{x: B \mid P\}, t) \to_\beta (\lambda x: B. P) @ t$ の場合：
  - $\lvert \Pred(A, \{x: B \mid P\}, t) \rvert$
    - ... $\{a \in \{\bullet\} \mid \lvert \Gamma \vdash t \rvert \in \lvert \Gamma \vdash \{x: B \mid P\} \rvert\}$
    - ... $\{a \in \{\bullet\} \mid \lvert t \rvert \in \lvert B \rvert \wedge \bullet \in \lvert \Gamma; x: B \vdash P \rvert _{(\gamma, \lvert t \rvert)}\}$
  - $\lvert \Gamma \vdash (\lambda x: B. P) @ t \rvert$
    - ... $(\alpha \in \lvert B \rvert \mapsto \lvert \Gamma; x: B \vdash P \rvert _{(\gamma, \alpha)}) (\lvert t \rvert)$
    - ... $\lvert \Gamma; x: B \vdash P \rvert _{(\gamma, \lvert t \rvert)}$
  - $\lvert \Gamma; x: B \vdash P \rvert _{(\gamma, \lvert t \rvert)}$ が定義されている時点で、
    $\lvert t \rvert \in \lvert B \rvert$ になっているはずなので、
    これを踏まえると、 $\{\bullet\} \cap$ が後者につけれれば、集合として同じになる。

well-sorted の定義の時点で $\Pred(A,B,t)$ には条件を付けてしまえば、次のような**感じ**の定理が証明できると思われる。
> $t \to t'$ かつ $t$ は well-sorted とする。
> このとき、 $t'$ も well-sorted であり、 $s(t) = s(t') =: s$ が成り立つ。
> また、 $\lvert \Gamma \Vdash t \rvert \cap \lvert s \rvert = \lvert \Gamma \Vdash t' \rvert \cap \lvert s \rvert$ が成り立つ。
