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
- 定義：$\tilde{f}: \Ty(\Power A, A/R) \to Y = \lambda X: \Ty(\Power A, A/R). \Take (\lambda x: \Ty(A, X). f @ x)$
  - $X: \Ty(\Power A, A/R) \vdash \Take (\lambda x: \Ty(A, X). f @ x): Y$ を示せばいい。
  - $\vDash \forall x_1: \Ty(A, X), \forall x_2: \Ty(A, X), (\lambda x: \Ty(). f @ x) @ x_1 = (\lambda x: \Ty(). f @ x) @ x_1$ については、
    $x_1: \Ty(A, X); x_2: \Ty(A, X) \vDash f @ x_1 = f @ x_2$ が示せるのでよい。

難しいの：$\Gamma; X: \Ty(\Power A, A/ R) \vDash \exists \Ty(A, X)$

補題：次が成り立つ。
$A: *^s; X, Y: \Power A, p: X = Y, a: \Ty(A, X) \vdash a: \Ty(A, Y)$ が示せる。
$P := (\lambda Z: \Power A. \Pred(A, Z, a))$ とすると、
- $\Gamma \vdash a: \Ty(A, X)$ より $\Gamma \vDash \Pred(A, Z, a) = P @ a$
- $\Gamma \vDash X = Y$ と合わせて $\Gamma \vDash \Pred(A, Y, a)$
- $\Gamma \vdash a: \Ty(A, Y)$ になる。

ここからはちょっと考えることが多い。
- $\Gamma; X: \Ty(\Power A, A/R); a: \Ty(A, \{x: A \mid X = [a]\}) \vdash a: \Ty(A, X)$ になる。
  - $\vdash X = [a]$
  - $\vdash a: \Ty(A, [a])$ ... これを示すのには、 $R$ の refl ($R a a$) が必要。
  - これと上の補題から、わかる。
- また、 $\Gamma; X: \Ty(\Power A, A/R) \vdash \exists \Ty(A, \{x: A \mid X = [a]\})$ は $\Pred(\Power A, A/R, X)$ からわかる。

なので状況としては、 $\Gamma; a: A \vdash b: B$ と $\Gamma \vDash \exists A$ から $\Gamma \vDash \exists B$ がほしい。

## 位相空間
べきと部分集合と述語があれば位相空間ができる。
（ただし、 Set の階層が上がることに注意する。）
