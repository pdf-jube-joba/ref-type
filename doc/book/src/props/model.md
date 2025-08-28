示したいのは、 Consistency で、「ZFC + いい感じの仮定」のもとでのモデルを作ることで、
$\vdash \forall P. P$ が示せないことを示す。
これには、 $\lvert \vdash (P: *^p) \to P \rvert = \emptyset$ であることを示せばよい。

the not so simple model CoC を参考にする。
次のように定義しておく。
- $\cdot = \emptyset$ ... これは、 unique な元として、後述する $\mathbb{B}$ が Bool っぽくなるようにしている。
- $\mathbb{B} = \{ \cdot, \{\cdot \} \}$
- $S$: set であって、 inaccessible とかいうやつだが、必要なのは、
  - べき集合で閉じること
  - dependent prod に対応するもので閉じること。
- $U$: $U \in S$ であって、 inaccessible みたいなやつ。

解釈は次のもの。
- $\lvert \Gamma \vdash \Power (A) \rvert (\gamma) = \Power (\lvert \Gamma \vdash A \rvert)$
- $\lvert \Gamma \vdash a =_A b \rvert (\gamma)$
