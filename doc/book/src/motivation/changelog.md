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

## $\Power A$ と $*^s$ の階層について
現状では $*^s$ には項と型のような分け方ができないようになっている。
理由は、 $A: *^s, x: A \vdash x: A: *^s$ と $\Gamma \vdash x: \{A \mid P\} : \Power A : *^s$ ができるから。
$A: \Power (A)$ はないものの、 $\{A \mid P \}: \Power A: *^s$ という "element" レベルのものが型としてふるまうことができているので、
これがちょっと扱いにくい原因も知れない。

なので、項のレベルを型のレベルに引き上げる操作があればいい？
- $\textop{Wop} A$ を新たに syntax に加える。
- $\Gamma \vdash \Power A: *^s$ if $\Gamma \vdash A: *^s$ はよい
- $\Gamma \vdash \textop{Wop} B: *^s$ if $\Gamma \vdash B: \Power A$...これは、 $\Power A$ の項ごとに対応する型があるということ
- $\Gamma \vdash t: \textop{Wop}(B)$ if $\Gamma \vdash t: A, \Gamma \vdash B: \Power A, \Gamma \vDash \Pred(A, B) @ t$


これで element と type を分けることができるようになるはず。
この場合、 $X_1 \leq X_2$ は $\Power A$ の中の $\leq$ として処理したほうがいい？
これは、 $\lambda x: A. t$ との兼ね合いになるから、後でやる。
当面は set rel なし。

$\text{Wop}$ じゃなくて、 $\text{Ty}$ にした。

## inversion が subset.intro のせいで示せない
sort に対する inversion も示せないので、方法を変える。
項の stratification も考えたが、 dependent type 云々で結構大変な気がした。
そのため、
- variable に sort を与える
- judgement を stratified にする（ Kind, Type, term をわけたような感じ。）
- 一度、 set rel なしで考える。

以下、 judgement を stratified にした場合を考えてみる。
- $\Gamma \vdash t: s$ のような、 $s$-type を判断する部分
- $\Gamma \vdash^s t: T$ のような、 $s$-element を判断する部分

このとき、 $\Gamma \vdash^s t: T$ なら $\Gamma \vdash T: s$ が成り立っていれば、かなり楽。
あと、 context 内でも sort を持ちまわすこと。

## sort の階層について
集合としては $*^s_{i}$ の階層があった方がいい。
（ $X$ 上の空間を集めてくる必要があるから、閉じている必要はないがこれが作れないといけない。）
この場合、 $\{*^s _i \mid i \in \mathbb{N}\}$ という predicative な階層と、 Proposition 用の sort にわけてもいい。
- $S = \{*^s_{i} \mid i \in \mathbb{N}\} \cup \{*^p, \square\}$
- $A = \{(*^s_{i}, *^s_{i+1}) \mid i \in \mathbb{N}\} \cup \{(*^p, \square)\}$
- $R= \{(*^s_{i}, *^s_{j}, *^s_{\max(i,j)}) \mid i, j \in \mathbb{N}\} \cup \{(*^p, *^p), (\square, *^p), (\square, \square)\} \cup \{(*^s_{i}, *p), (*^s, \square) \mid i \in \mathbb{N}\}$
  - $\{(*^s_i, *^s_j, *^s_j) \mid i \leq j\}$ をしばらくは考えてもいい。理由は、 $s_1, s_3$ から $s_2$ が決まるので、 $s$-elem と $s$-type の計算がしやすい。

PTS としてはこれは無矛盾。
（ 『structural theory of PTS』 の $\forall \mathcal{P}. Q$ を参照。）

## モデルを考えるうえで...
- inversion は必ずしも必須じゃない？
- $\Ty B$ はそのままだと ZFC で Valid にできない。
   $\Ty (B, A)$ のようにすることで、 $\{ x \in \lvert \Gamma \vdash A \rvert \mid x \in \lvert \Gamma \vdash B \rvert\}$ のように書けて大丈夫になる。
- $\Gamma \vdash t$ に対して  $t \to_\beta t'$ が （well-sorted ぐらいを課して） $\Gamma \vdash t'$ と一致するほうが望ましい。
  - conv を入れるため。

この場合、 $\Pred (A, \{B \mid P\}) \to_\beta P$ が難しい。

1. $\Pred (A, B, t)$ のようにする。
2. $\{ x: B \mid P\}$ を使って $\Pred (A, \{x: B \mid P\}, t) \to (\lambda x: B. P) @ t$ と考える。
3. $\lvert \Gamma \vdash \{x: A \mid P\} \rvert _\gamma = \{\alpha \in \lvert A \rvert \mid \bullet \in \lvert \Gamma; x: A \vdash P \rvert _{(\gamma, \alpha)}\}$
4. $\lvert \Gamma \vdash \Pred (A, B, t) \rvert = \{a \in \{\bullet\} \mid \lvert \Gamma \vdash t \rvert \in \lvert \Gamma \vdash B \rvert\}$

このとき、次のように惜しいところまで行く。
- $\lvert \Gamma \vdash \Pred (A, \{x: B \mid P\}, t) \rvert$
- ... $\{a \in \{\bullet\} \mid \lvert \Gamma \vdash t \rvert \in \lvert \Gamma \vdash \{x: B \mid P\} \rvert\}$
- ... $\{a \in \{\bullet\} \mid \lvert t \rvert \in \lvert B \rvert \wedge \bullet \in \lvert \Gamma; x: B \vdash P \rvert _{(\gamma, \lvert t \rvert)}\}$
- $\lvert \Gamma \vdash (\lambda x: B. P) @ t \rvert$
- ... $(\alpha \in \lvert B \rvert \mapsto \lvert \Gamma; x: B \vdash P \rvert _{(\gamma, \alpha)}) (\lvert t \rvert)$
- ... $\lvert \Gamma; x: B \vdash P \rvert _{(\gamma, \lvert t \rvert)}$

$\lvert \Gamma; x: B \vdash P \rvert _{(\gamma, \lvert t \rvert)}$ が定義されている時点で、 $\lvert t \rvert \in \lvert B \rvert$ になっているはずなので、
これを踏まえると、 $\{\bullet\} \cap$ が後者につけれれば、集合として同じになる。
なので、 $\lvert \Gamma \vdash^s t \rvert = \lvert s \rvert \cap \lvert \Gamma \vdash t \rvert$ とすればいい？
これなら、 $t \to t'$ に対して $\lvert \Gamma \vdash^s t \rvert = \lvert \Gamma \vdash^s t' \rvert$ を示すことになるのでよさそう。
また、 $\Gamma \vdash^s t: T$ なら $\lvert \Gamma \vdash^s t \rvert \in \lvert \Gamma \vdash^s T \rvert$ となるので、もうちょっと示しやすい。

## take について
Prop と Set(i) を分けたりしていたので、気が付いたら、 $\text{Take}$ がもっと楽にできることに気が付いた。
coersion ができるので、 $\{y: Y \mid \exists x. f(x) = y\} \subset Y$ に忘れることで楽ができる。
- definite/indefinite decsription っぽく、型から元を取り出す方式
- contractible や singleton とかの公理じゃない形での定義
- choice とかの、関数の取り出し系

使いやすいのはこんな感じ？
- $\Gamma \vdash \Take T: T$ if $\Gamma \vDash \exists T, \Gamma \vDash \forall x_1: T, \forall x_2, x_1 = x_2$
- $\Gamma \vDash \Take T = t$ if $\Gamma \vdash \Take T: T, \Gamma \vdash t: T$

今扱っている $=$ は型の情報を忘れているので、その点で扱いが難しくなることはありそうだが、それは元から。
