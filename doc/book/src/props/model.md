示したいのは、 Consistency で、「ZFC + いい感じの仮定」のもとでのモデルを作ることで、
$\vdash \forall P. P$ が示せないことを示す。
これには、 $\lvert \Vdash (P: *^p) \to P \rvert = \emptyset$ であることを示せばよい。

the not so simple model CoC を参考にする。
次のように定義しておく。
- $0 = \bullet = \emptyset$ ... これは、 unique な元として、後述する $\mathbb{B}$ が Bool っぽくなるようにしている。
- $1 = \{ \bullet \}$
- $\mathbb{B} = \{ \bullet, \{\bullet \} \} = \{0, 1\}$

- $S$: set であって、 inaccessible とかいうやつだが、必要なのは、
  - べき集合で閉じること
  - dependent prod に対応するもので閉じること。
- $U$: $U \in S$ であって、 inaccessible みたいなやつ。

普通のラムダ部分は論文に習えばいい。
ただし、 proof-term かどうかとか、 well-sorted ness を考える必要がある。
（それで定義を分岐するから。）

sort が $(s_1, s_2, s_2) \in \mathcal{R}$ の形なので、 sort-elem function は簡単に定義できる。
ふつうのラムダ以外は決め打ちできるはず。
- $e(s) = \text{None}$
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
- $\lvert \Gamma \Vdash *^p \rvert = \mathbb{B}$
- $\lvert \Gamma \Vdash *^s \rvert = S$
- $\lvert \Gamma \Vdash \square \rvert = U$
- $\lvert \Gamma \Vdash p \rvert = \cdot$
  - $\Uparrow$ if $s(p) = *^p$
- $\lvert \Gamma \Vdash x^\square \rvert _\gamma = \pi_i \gamma$ if $x^\square$ is $i$-th
- $\lvert \Gamma \Vdash \lambda x: A. t \rvert _\gamma = \alpha \in \lvert \Gamma \Vdash A \rvert \mapsto \lvert \Gamma \Vdash t \rvert _{(\gamma, \alpha)}$
- $\lvert \Gamma \Vdash f @ a  \rvert _\gamma = \lvert \Gamma \Vdash f \rvert _\gamma (\lvert \Gamma \Vdash a \rvert _\gamma)$
- $\lvert \Gamma \Vdash (x: A) \to B \rvert = \{f \in \{ \bullet \} \mid \forall \alpha \in \lvert \Gamma \Vdash A \rvert _\gamma , f \in \lvert \Gamma; x: A \Vdash B \rvert _{(\gamma, \alpha)} \}$
  - $\Uparrow$ if $s(B) = \square$
- $\lvert \Gamma \Vdash (x: A) \to B \rvert = \Pi_{\alpha \in \lvert \Gamma \Vdash A \rvert _\gamma} \lvert \Gamma; x: A \Vdash B \rvert _{(\gamma, \alpha)}$
- ここ以降がちゃんと定義しないといけない部分
- $\lvert \Gamma \Vdash \Proof p \rvert _\gamma = \bullet$
- $\lvert \Gamma \Vdash \Power (A) \rvert _\gamma = \mathcal{P}(\lvert \Gamma \Vdash A \rvert _\gamma)$
- $\lvert \Gamma \Vdash \{A \mid P\} \rvert _\gamma = \{x \in \lvert \Gamma \Vdash A \rvert _\gamma \mid \bullet \in \lvert \Gamma \Vdash P \rvert _\gamma (x) \}$
- $\lvert \Gamma \Vdash \Ty(A, B) \rvert _\gamma = \{x \in \lvert \Gamma \Vdash A _\gamma \rvert \mid x \in \lvert \Gamma \Vdash B \rvert _\gamma\}$
- $\lvert \Gamma \Vdash \Pred(A, B) \rvert _\gamma =
  \\ \{(x, 1) \in \lvert \Gamma \Vdash A \rvert _\gamma \times \mathbb{B} \mid x \in \lvert \Gamma \Vdash B \rvert _\gamma\} \\
  \cup \{(x, 0) \in \lvert \Gamma \Vdash A \rvert _\gamma \times \mathbb{B} \mid x \notin \lvert \Gamma \Vdash B \rvert _\gamma\}$
  <br> これの型は $A \to *^p$ なので、 $\lvert A \rvert \to \mathbb{B}$ になる。 $x \in \lvert B \rvert$ かどうかで分ければいい。
- $\lvert \Gamma \Vdash a = b \rvert _\gamma = \{\bullet \mid \lvert \Gamma \Vdash a \rvert _\gamma = \lvert \Gamma \Vdash b \rvert _\gamma\}$
- $\lvert \Gamma \Vdash \exists t \rvert _\gamma = \{ \bullet \mid \lvert \Gamma \vdash t \rvert _\gamma \not = \emptyset \} $
- $\lvert \Gamma \Vdash \Take f \rvert _\gamma = y \mathrel{\text{s.t.}} \exists x, (x, y) \in \lvert \Gamma \vdash f \rvert _\gamma$
  <br> これの型が $X \to Y$ なら $f \subset X \times Y$ なのでこう書けるはず。
  $\text{s.t}$ の意味が不明瞭に見えるけれど、そもそも集合自体、自由変数で導入した後に論理式で定義を用いるのでよい。
  （ $z \in \{y \in x \mid \phi(y, x)\}$ が $(k \in l \leftrightarrow \phi(y, k)) \rightarrow z \in l$  になるのと同じ。）

reduction に対してどうふるまうかがみたい。
substitutivility は大丈夫だと思うので飛ばす。
（ $\Pred(A, \{B \mid P\}) \to_\beta P$ は reduction の話なので、subst に関係することはないから。）
$\lvert \Gamma \vDash \Pred(A, \{B \mid P \}) \rvert _\gamma = \lvert \Gamma \Vdash P \rvert _\gamma$ になるか？
- $\lvert \Gamma \vDash \Pred(A, \{B \mid P \}) \rvert _\gamma$
- $ = \{(x, 1) \in \lvert \Gamma \Vdash A \rvert _\gamma \times \mathbb{B} \mid x \in \lvert \Gamma \Vdash \{B \mid P\} \rvert _\gamma\} \\
  \cup \{(x, 0) \in \lvert \Gamma \Vdash A \rvert _\gamma \times \mathbb{B} \mid x \notin \lvert \Gamma \Vdash \{B \mid P\} \rvert _\gamma\}$
- $ = \{(x, 1) \in \lvert \Gamma \Vdash A \rvert _\gamma \times \mathbb{B} \mid x \in \{x \in \lvert \Gamma \Vdash B \rvert _\gamma \mid \bullet \in \lvert \Gamma \Vdash P \rvert _\gamma (x) \}\} \\
  \cup \{(x, 0) \in \lvert \Gamma \Vdash A \rvert _\gamma \times \mathbb{B} \mid x \notin \{x \in \lvert \Gamma \Vdash B \rvert _\gamma \mid \bullet \in \lvert \Gamma \Vdash P \rvert _\gamma (x) \}\} $
- $ = \{(x, 1) \in \lvert \Gamma \Vdash A \rvert _\gamma \times \mathbb{B} \mid x \in \lvert \Gamma \Vdash B \rvert _\gamma \wedge \bullet \in \lvert \Gamma \Vdash P \rvert _\gamma (x) \} \\
  \cup \{(x, 0) \in \lvert \Gamma \Vdash A \rvert _\gamma \times \mathbb{B} \mid x \notin \lvert \Gamma \Vdash B \rvert _\gamma \vee \bullet \notin \lvert \Gamma \Vdash P \rvert _\gamma (x) \} $

同じにならない。


