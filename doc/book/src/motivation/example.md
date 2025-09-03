ここでは次を考える。
- 考えている体系で何がどう記述できるか

## 自然数と倍数の例
「自然数の部分集合であって、 $n$ の倍数しか含まない集合」は次のように書ける。
$$ \{x: \Power \mathbb{N} \mid \forall y: \Ty(\mathbb{N}, x), y \mathrel{\text{div}} n = 0\} =: A$$
ここからどんなことができるか？
"直感的には" $m: M: A$ に対して $m \mathrel{\text{div}} n = 0$ が示せてほしい。
ただ、階層を合わせるためにちょっと複雑になっている。
階層としてはこんな感じ。
（ $\mathbb{N}, \Power \mathbb{N}, \Power \Power \mathbb{N}$ は全部 type ）
| term | type |
| --- | --- |
| $A = \{x: \textcolor{blue}{\Power \mathbb{N}} \mid \ldots \}$ | $\Power \textcolor{blue}{\Power \mathbb{N}}$ |
| $M$ | $\Ty(\Power \mathbb{N}, A)$, $\Power \mathbb{N}$ |
| $m$ | $\Ty(\mathbb{N}, M)$ |

- $M: \Ty(\Power \mathbb{N}, A = \{\})$ より $\vDash \Pred (\Power \mathbb{N}, A = \{\cdots\}, M)$
- $\to (\lambda x: \Power \mathbb{N}, \cdots) @ M \to \forall y: \Ty(\mathbb{N}, M), y \mathrel{\text{div}} n = 0$
- よって、 $\vDash \forall y: \Ty(\mathbb{N}, M), y \mathrel{\text{div}} n = 0$
- $m: \Ty(\mathbb{N}, M)$ より $\vDash m \mathrel{\text{div}} n = 0$

## 商集合の普遍性の写像
- $A: *^s$ と $R: A \to A \to *^p$ があるときに、 $A / R$ からの写像の構成を書きたい。
- $Y: *^s$ と $f: A \to Y$ があって $\forall x_1: A, \forall x_2: R, R x_1 x_2 \to f(x_1) = f(x_2)$ が示せるとする。
- $\tilde{f}([y]) = f(y)$ は $A / R \to Y$ になってほしい。
  - $y$ は $A$ の部分集合で、 $x: y$ の取り出しにより $x: A$ がとれている。
  - この $x: y$ の取り方によらずに、 $f(x) : Y$ が定まっている。

これをちゃんと書く。
- 定義：$[a]: \Power A := \{x: A \mid R x a\}$ for $a: A$
- 定義：$A/R: \Power \Power A := \{X : \Power A \mid \exists \{a: A \mid X = [a] \}\}$
- 定義：$\tilde{f}: \Ty(\Power A, A/R) \to Y = \lambda y: \Ty(\Power A, A/R). \Take \Ty(Y, \{i: Y \mid \exists x: \Ty(A, y), i = f(x)\})$
  - これには $y: \Ty(\Power A, A/R) \vdash \Take \Ty(Y, \{i: Y \mid \exists x: \Ty(A, y), i = f(x)\}): \Ty(Y, \cdots)$ が示せれば、 $\cdots \vdash \Take (): Y$ と dep.intro でよい。
  - $\vdash \exists \Ty(Y, \{i: Y \mid \exists x: \Ty(A, y), i = f(x)\})$
  - $\vdash \forall y_1: \Ty (\cdots), \forall y_2: \Ty(\cdots), y_1 = y_2$

## 位相空間
べきと部分集合と述語があれば位相空間ができる。
ただし、 $\vdash t: B$ と $\vDash \Pred (A, B, t)$ の違いに注意する。
- $O_1, O_1: \Power X$ に対して、 $O_1 \cap O_2 := \{x: X \mid \Pred_X O_1 x \wedge \Pred_X O_2 x\}$ と書ける。
- $\Lambda: *^s$ により $f: \Lambda \to \Power X$ があるなら $\bigcup_{\lambda \in \Lambda} f(\lambda) := \{x: X \mid \exists \lambda. \Pred_X f(\lambda) x\}$

これで頑張れば、 $\mathop{\text{is-topology}} (X: *^s) (O: \Power \Power X): *^p$ が作れる。
ただし、 topological space を帰納型というか record 型というかそんな感じのやつにしたいなら、
それは $*^s$ ではなくて $\square$ に住むことになる。
そのため、「 hoge を満たす位相空間 」を記述したい場合には、 $\square$ を predicative な形で階層を付ける必要がある。
（ sum 型が predicative になるために制限があるような感じ）

この場合には、 propositional equality では $t_1, t_2: {x: A | P}$ に対して $t_1 =_A t_2 => t_1 =_{x: A | P} t_2$ ができていたものを、
再び $\square$ のレベルで似たような equality が示せないと使いにくい。
具体的には、位相空間の compactness が定義されていたとき、 $2$ つの位相空間の等しさの判定時に、 compactness の証明まで要求されるようになってしまう。
だけど、構造の $=$ を要求することは少ないはずで、どちらかといえば同型が登場するので良い。
また compactness などの"構造に対する性質"については、 topology の定義を "expand" して、prop を与えることでも得られる。
こういうのをうまくやる仕組みがあればいい？