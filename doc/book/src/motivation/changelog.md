ほしい機能が先にある一方で、体系の無矛盾性を示す必要がある。
そのため、証明をしたり考察をしたりする中で考えている体系自体をたくさん変更することになった。
ここではその変更をまとめる。

## sort を分ける。
これからいろいろ追加する中で、（多分）命題の部分と集合の部分を分けたほうがいい気がした。
そのため、新たに sort $*^s$ を "Set" として導入する。
- $*^s: \square$
- $(*^s, *^s), (*^s, \square) \in \mathcal{R}$

PTS っぽくそのまま拡張できる。
もし必要な場合には次のものを入れてもいい。
- $\square^s$ と $\square^p$ をわける。
  - $\lambda_{\text{HOL}}$ ではないほうの、 higher order logic としての $\lambda_{\text{PRED} \omega}$ が参考になる。
- $\square_{i}: \square_{i+1}$ のような無限の階層を導入する。
  - K 群とコボルディズムはこれがないと辛そう。

## refinement type とか predicate subtyping の導入
ざっくり、 $t: A$ で $\vDash P(t)$ が証明できれば $t: \{x: A | P(x)\}$ と"型付け"できる体系にする。
- Proposition というよりも Set に対する操作なので、 $A$ は $*^s$ とする。
- $t: A \wedge P(t) \Leftrightarrow t: \{x: A \mid P(x)\}$ である。

| category | conclusion | premises |
| --- | --- | --- |
| 部分型付けの form | $\Gamma \vdash \{x: A \mid P\}: *^s$ | $\Gamma \vdash A:*^s, \Gamma :: x: A \vdash P: *^p$ |
| 部分型付けの導入 | $\Gamma \vdash t: \{x: A \mid P\}$ | $\Gamma \vdash \{x: A \mid P\} : *^s, \\ \Gamma \vdash t: A, \Gamma \vDash P[x := t]$ |
| 型を弱める | $\Gamma \vdash t: A$ | $\Gamma \vdash t: \{x: A \mid P\}$ |
| 命題を取り出す | $\Gamma \vDash P[x := t]$ | $\Gamma \vdash t: \{x: A \mid P \}$ |

もしかしたら、 $P$ は $P(x)$ のような自由変数付きの述語よりも関数として扱った方がいいかもしれない。
その場合、 $\{A \mid P\}$ と書いて $P[x := t]$ は $P @ t$ にすればいい。

## 元の選択によらない記述
$x: A. t$ のような記述であって、 $t$ が $x$ の"取り方によらず"、一意に元を定めるような場合がある。
これを $\Take x: A.t$ と書き、 $t: B$ に対する **$B$ の元として**（ $A \to B$ ではなく）認めることにする。

例：商空間からの写像は $\lambda x: Q/A. \Take y: x. f(y)$ のように書けて、 $Q/A \to Y$ （ただし $f: Q \to Y$ ）である。

これを正当化するためには、元が取り方によらないことを定義するために equality が必要になる。

### equality の導入について
equality は扱いが主に2つある。
1. Leibniz equality を考える場合
  - $A: *^s, a_0: A, a_1: A$ に対して、 $a_0 =_A a_1$ を $\Pi (P: A \to *^p). P @ a_0 \to P @ a_1$ とする。
2. inductive な型として項の定義を拡張してしまう。
  - 項は $t =_t t$ と $\text{refl}_t t$ で拡張
  - elimination のために match に対応するような項も入れる。
  - なんか、 type family らしい（つまり、 index の位置が異なる）
    - $\Gamma :: A: *^s :: a: *^s$ という Context の下で帰納型として $I: A \to *^p$ とその元 $\text{refl}_a: I @ a$ がある、という設定でやること。

#### ほしい性質
- 反射律、対称律、推移律
- Leibniz equality: $a_0, a_1: A$ と $P: A \to s$ に対して、 $a_0 =_A a_1 \to P @ a_0 \to P @ a_1$
- $B: \Power A$ に対して、 $a =_A b$ と $a =_B b$ が同値
  - これのためには、 $a,b: A$ のとき、 $a:b:B$ と型付けできる理由が必要。
- $A: *^s$ を課す方がいいのか
- Leibniz equality は $s = *^p$ の方がいいのか
  - $x: A$ で添え字づけられた集合 $B(x)$ があるとき、 $x =_A y \to B(x) \to B(y)$ があると便利。
- Leibniz equality の場合、 $A$ 上の述語を $B$ に制限するのは楽だが、 $B$ 上の述語を $A$ に拡張するのは楽ではない ... 公理として入れる必要がある。

証明項の等しさを項の等しさに入れたくない点がある。
つまり、 $a_0 =_{\{x: A \mid P\}} a_1$ と $a_0 =_A a_1$ が同値であってほしい。
$\{x: A \mid P\}$ 上でのみ定義された述語が出てきたりしてややこしいので注意。

### take 演算子の定義
$\Take x:A. t$ が書ける要件は簡単
- $e: A$ なる項があること
- $e_1: A$ と $e_2: A$ に対して $t[e_1] = t[e_2]$ が成り立つこと（これは自由変数で示せればいい）

| category | conclusion | premises |
| --- | --- | --- |
| take の導入 | $\Gamma \vdash (\Take x: A. t): B$  | $\Gamma A: *^s, \Gamma :: x: A \vdash t: B \\ \Gamma \vdash e: A, \\ \Gamma \vDash \Pi x: A. \Pi y: A. (t =_B t[x := y])$ |
| take の equality | $\Gamma \vdash (\Take x: A. t) =_B t[x := e]$ | $\Gamma \vdash (\Take x: A. t): B, \Gamma \vdash e: A$ |

reduction として take の equality が judgemental equality になるように定義するのは、あまりにも強いと思ったので入れてない。
Take を入れると canonical な form はなくなりそうだが、 normalization が成り立ったり、 $=$ の同値類の中で canonical form があればうれしい。

変数と代入を使わない選択肢として、
$f$: $X \to Y$ なら $\Take f$: $Y$ とかにして、 $y_1: X, y_2: X \vdash f @ y_1 = f @ y_2$ を課せば、変な議論がいらなくなりそう。

## power type の導入
$\Gamma A: *^s$ なら $A$ のべき集合 $\Power P$を入れたい。
**ただし、 Power type を矛盾なく入れるのは難しいかも**
例えば、 $A \to *^p$ を $\in *^p$ にすると矛盾するらしい。

- sort はさておき、 $A \to *^p$ や Boolean $\mathbb{B}$ を用いて $A \to \mathbb{B}$ のように定義することができる。
- なら気を付ければ拡張しても大丈夫だろう。

| category | conclusion | premises |
| --- | --- | --- |
| power type の導入 | $\Gamma \vdash \Power A: *^s$ | $\Gamma \vdash A: *^s$|
| subset を含む | $\Gamma \vdash \{x: A \mid P\}: \Power A$ | $\Gamma \vdash \{x: A \mid P\}: *^s$ |
| subset は set | $\Gamma \vdash B: *^s$ | $\Gamma \vdash B: \Power A$ |
| subset から weak | $\Gamma \vdash x: A$ | $\Gamma \vdash x: B, \Gamma \vdash B: \Power A$ |

## 述語の取り出し
### 商集合がまだ扱えない。
$A: *^s$ と $R$: $A$ 上の同値関係があるとする。
$A / R$ をどう定義するかが難しい。
$a: A$ に対して、 $[a] := \{x: A \mid R@a@x\}$ とする。
いずれにせよ **exists** がほしい。
（ $\exists x: A$ が $A$ の元の存在とすれば、 $\exists x: A. P$ は $\exists x: \{x: A \mid P\}$ と書けるので、 $A: *^s$ に対する $\exists A$ のみ書ければよい。）

1. $\exists$ を用いれば、 $A / R := \{B: \Power A \mid \exists a: \{a: A \mid B =_{\Power A} [a]\}\}$ と書ける： **exists を使用**
    - $f: A \to Y$ が $R$ を保つなら、 $\tilde(f)$ は $\lambda B: A / R. \Take x: B. f(x)$ と書けるはず。
    - ただこの記述の正しさは示せない ... $\vDash \exists a: A. B = [a]$ がわかっていたとしても、 $e: B$ となる項がない。（ $B$ は抽象的だから）
        - $e: [a]$ でも $e: B$ とは限らないところから。
    - また、 $f(x_0) = f(x_1)$ を示すには、 $x_0, x_1: B$ で $B = [e_0], B = [e_1]$ から $\vDash R @ x_0 @ x_1$ を示す必要がある。
2. $B$ を同値類の性質を満たす集合として定義することができるか？
    - $x \in B$ や $x \notin B$ が表現できないといけない。 
    1. 空でない ... $\exists b: B$ ... **exists を使用**
    2. $R$ で閉じる ... $\Pi x: B. \Pi y: B. R x y$
    3. 同値を含む ... $\Pi x: B. \Pi y: A. R x y \to y \in B$
    4. 同値じゃないものは含まない ... $\Pi x: B. \Pi y: A. \neg R x y \to y \notin B$

ともかく、"真の"商集合が欲しい場合には、 $\exists$ や $x \in B$ やそれ以上のものが欲しいことになる。

これに対して、述語の取り出しを記述できるようにする。

### 定義
$\Pred_A B$ を $A$ の部分集合 $B$ に対して、 $B$ に含まれる条件 $A \to *^p$ を表すとする。
$t: B$ に入る条件を、 $\vDash (\Pred_A B)@t$ とし、 reduction として $\Pred_A \{x: A' \mid P\} \to \lambda x: A'. P$ を許すことにする。
- reduction を考えれば $t: {x: A \mid P}$ の話を一般の $B: \Power A$ でできる。
- $\Pred$ 自体は $\Pi (A: *^s). \Pi (B: \Power A). B \to *^p$ のようになっていて大きい。
- $\vdash t: A$ と $\vdash B: \Power A$ に対して、 $\vdash t: B$ と $\vDash \Pred_A B @ t$ が行き来できる。

### $\exists t$ について
$\Sigma$ 型のことを考えると、 $\Sigma _{x: A}. \top$ が $\exists$ に対応しているが、
これを $A: *^s$ なのに $(\Sigma _{x: A}. \top): *^p$ と型付けしているわけなので、気を付けたほうがいいよ。
$\pi_1$ 自体はいれても大丈夫だったと思うが、これが proof-term として中身を reveal しないようにした方がいい。
large elimination みたいになる。
一方で、 $\exists t: *^p$ にすることで、 $\Gamma:: (l: \exists t)$ とかができるのと、
$\{y: A \mid \exists x. y = f(x)\}$ が書けていい。（後ろ部分が $*^p$ の方が"らしい"から。）

## set の中での推移律
（ cumulativity という言葉を使っていたが、不適だった。
cumulative は宇宙用の言葉らしい。
https://ncatlab.org/nlab/show/type+universe#:~:text=A%20tower%20of%20universes%20is%20cumulative）

集合のことを考えると、 $A \to B \subset B' \to B'$ に関する推移律が欲しい。
$\lambda x: A. x$ は $A \to A$ と infer されるが、 $A \subset B$ のときに $(\lambda x: A .x): (A \to B)$ を check するのがつらい。
型付け上は確かにできるのだが（$x: A \vdash x: B$ より）、 check と infer をする上では、ちょっと工夫が必要
というのも、 $t: A \to A$ でも $t: A \to B$ とは限らないため。
（ $t$ がラムダ抽象の場合にはよい。）
ただ今回の場合は、 cast を間に挟むことで解決できる。
つまり、 $"cast":= (x: B) \to x$ を入れてやると、 $lambda x: A. ("cast" x)$ が通るようになる。
（ここらへんは type check の実装の話っぽい）
$\eta$ を入れれば一部は改善する： $\Gamma \vdash t: (x: A) \to B$ なら $t \equiv \lambda x: A. t x$

これと似たような動機で出てくる Coq の $\leq$ を考えて、似たような定義をすればいい。
（これは Luo の ECC での話に出てくる。こっちは judgemental じゃない定義かもしれない。覚えてない。）
すなわち、 $\Gamma \vdash t_1 \leq t_2$ という新たな judgement を入れる。

- 反射律と推移律
- $(x: A) \to X_1 \leq (x: A) \to X_2$ if $X_1 \leq X_2$

## equality について
型理論からの類推から、 equality は $a =_A b$ として導入してきた。
ただ、 $a =_A b \Leftrightarrow a =_B b$ などが欲しいことを考えると、 $a = b$ の形にしてしまってもいい気がする。
$a = b$ が示せるなら当然 $P @ a \implies P @ b$ が欲しいので、型付け部分の一致については指定したうえで、これを導入する。
これがあれば、 $=$ に必要なものは全部証明できたはず。

## $\Pred(A, B)$ の型について
$\Pred(A, \{\{B \mid P\} \mid Q\})$ を考えると、 $\{\{B \mid P\} \mid Q\} \leq \{A \mid P\} \leq A$ が成り立つ。
ここで、 $\Pred(A, B)$ if $B \leq A$ とすると、次のように reduction で型がおかしくなる。
- $\Pred(A, \{\{\} \mid Q\})$: $A \to *^p$
- $\Pred(A, \{\{\} \mid Q\}) \to Q$: $\{B \mid P\} \to *^p$

なので、 $B: \Power A$ とした方がいい。
