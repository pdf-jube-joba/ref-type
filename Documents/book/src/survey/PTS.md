# PTS の定義
次のものが与えられているとする。
- Set of Sort $\mathcal{S}: \text{Set}$
- Set of Axiom $\mathcal{A}: \text{SubSet of } \mathcal{S} \times \mathcal{S}$
- Set of Relation $\mathcal{R}: \text{SubSet of } \mathcal{S} \times \mathcal{S} \times \mathcal{S}$

注意点として、次のようにかいたりする。
- $(a, b) \in \mathcal{A}$ であることを $a: b$ と書く。
- $a, b \in \mathcal{S}$ が $(a, b, b) \in \mathcal{R}$ を満たしていたら、単に $(a, b) \in \mathcal{R}$ とも書く。
また、変数を定義するため、変数の集合 $\mathcal{V}$ を固定しておく。

また、 $\beta$ reduction は省略する。

PTS の定義は複数あり、 well-formed context を含むかどうかの違いとかがある。
wiki とか nlab とかにのってる（ well-formed のない）バージョンを載せる。

term の定義 $t$ :=
| category | definition |
| --- | --- |
| kind | $s \in \mathcal{S}$ |
| variable | $x$ |
| lambda abstraction | $\lambda x: t. t$ |
| dependent product type | $\Pi x: t. t$ |
| application | $t @ t$ |

judgement は $\Gamma \vdash t: t$ のみ。

derivation は
| category | conclusion | premises |
| --- | --- | --- |
| axiom | $\emptyset \vdash s_1: s_2$ | $(s_1, s_2) \in \mathcal{R}$ |
| variable| $\Gamma:: x: A \vdash x: A$ | $\Gamma \vdash A: s, x \notin \Gamma$ |
| weak | $\Gamma:: x: A \vdash M: N$ | $\Gamma \vdash M: N, \Gamma \vdash A: s, x \notin \Gamma$ |
| conv | $\Gamma \vdash t: T_2$ | $\Gamma \vdash t: T_1, \Gamma \vdash T_2: s, T_1 \equiv^\beta T_2$ |
| dep form | $\Gamma \vdash (\Pi x: t. T): s_3$ | $\Gamma \vdash t: s_1, \Gamma:: x: t \vdash T: s_2, \\ (s_1, s_2, s_3) \in \mathcal{R}$ |
| dep intro | $\Gamma \vdash (\lambda x: t. m): (\Pi x:t. M)$ | $\Gamma \vdash (\Pi x: t. M): s, \Gamma:: x:t \vdash m: M$ |
| dep elim | $\Gamma \vdash f @ a: T[x := a]$ | $\Gamma \vdash f: (\Pi x: t. T), \Gamma \vdash a: t$ | 

# CoC について
Calculus of Constructions はその導入は Coquand らしいが、
その元論文での定義はあまり使われていなくて、
arendregt による PTS を使った lambda cube の一頂点として導入するのが一般的みたい。
元論文の方では、項や judgement は stratified に定義されている。
つまり、 term や type に対応するものが別の syntax の中で定義されている。 BNF で書いたら分かれているような感じ。
- term := ...
- type := ...

ATTaPL でも syntax はわかれていて、 Proof を使って2つのレベルの行き来を行う。

でも、探してみても元論文の定義との同値性のような話はあまりされていなかった。
system F でもそうだけど、 stratified な定義と PTS （ syntax がつぶれている）との行き来をちゃんと述べている文献は少ない？

## stratified な定義
ATTaPL を参考に、項の定義と型の定義をわける。
（ATTaPL では logical framework をもとに導入しているので、syntaxがわかれている。）
term 用の変数の集合 $\mathcal{V}_0$ と type 用の変数の集合 $\mathcal{V}_1$ を別に用意しておくこともできるが、一緒にして $\mathcal{V}$ にする。

- term $t$ :=
  | category | definition |
  | --- | --- |
  | variable | $\mathcal{V}$ |
  | lambda abstraction | $\lambda \mathcal{V}: T. t$ |
  | application | $t @ t$ |
  | universal quantification | $\textop{all} \mathcal{V}: T. t$ |
- type $T$ :=
  | category | definition |
  | --- | --- |
  | type variable | $\mathcal{V}$ |
  | dependent product | $\Pi \mathcal{V}: T. T$ |
  | type family application | $T @ t$ |
  | universal quantification | $\textop{All} \mathcal{V}: T. t$ |
  | propositions | $\text{Prop}$ |
  | family of proofs | $\textop{Proof}$ |
- kinds $K$ :=
  | category | definition |
  | --- | --- |
  | kind of proper type | $*$ |
  | kind of type family | $\Pi \mathcal{V}: T. K$ |

コンテキストもちょっとややこしい
- context fragment $\gamma$ :=
  | category | definition |
  | --- | --- |
  | type declare | $\mathcal{V}: T$ |
  | kind declare | $\mathcal{V}: K$ |
- context $\Gamma$ := $\emptyset \mid \Gamma:: \gamma$

conversion として次のものを入れる。
$\textop{Proof} (\textop{all} x: T. t) \to \Pi x:T. \textop{Proof} t$

judgement は次のように定義される。
| category | definition |
| --- | --- |
| well-formed kind | $\Gamma \vdash_{\text{wf-kind}} K$ |
| kind | $\Gamma \vdash_{\text{kind}} T: K$ |
| type | $\Gamma \vdash_{\text{type}} t: T$ |

derivation の関係は次のようになる。
| category | conclusion | premises |
| --- | --- | --- |
| axiom | $\Gamma \vdash_{\text{wf-kind}} * $ | |
| pi | $\Gamma \vdash_{\text{wf-kind}} \Pi x: T. K$ | $\Gamma \vdash_{\text{kind}} T: K'$ |
| var(kind) | $\Gamma \vdash_{\text{kind}} X: K$ | $\Gamma \vdash_{\text{wf-kind}} K, (X: K) \in \Gamma$ |
| pi(kind) | $\Gamma \vdash_{\text{kind}} (\Pi x: T_1. T_2): *$ | $\Gamma \vdash_{\text{kind}} T_1: *, \Gamma:: x: T_1 \vdash_{\text{kind}} T_2: *$ |
| app(kind) | $\Gamma \vdash_{\text{kind}} S @ t: K[x := t]$ | $\Gamma \vdash_{\text{kind}} S: (\Pi x: T. K), \Gamma \vdash_{\vdash_{\text{type}}} t: T$ |
| conv(kind) | $Gamma \vdash_{\text{kind}} T: K'$ | $\Gamma \vdash_{\text{kind}} K, K \equiv K'$ |
| prop | $\Gamma \vdash_{\text{kind}} \text{Prop}: *$ | |
| proof | $\Gamma \vdash_{\text{kind}} \textop{Proof}: (\Pi x: \text{Prop}. *)$ |
| var(type) | $\Gamma \vdash_{\text{type}} t: T$ | $\Gamma \vdash_{\text{kind}} T: *, (x: T) \in \Gamma$ |
| abs(type) | $\Gamma \vdash_{\text{type}} (\lambda x: S. t): (\Pi x: S. T)$ | $\Gamma \vdash_{\text{kind}} S: *, \Gamma:: x: S \vdash_{\text{type}} t: T$ |
| app(type) | $\Gamma \vdash_{\text{type}} t_1 t_2: T[x := t_2]$ | $\Gamma \vdash_{\text{type}} t_1: (\Pi x: S. T), \Gamma \vdash_{\text{type}} t_2: S$ |
| conv(type) | $\Gamma \vdash_{\text{type}} t: T'$ | $\Gamma \vdash_{\text{type}} t: T, T \equiv T'$ |

## PTS としての CoC について
PTS において次のようにしたものが CoC になっている。
- $\mathcal{S} = \{*, \square\}$
- $\mathcal{A} = \{(*, \square)\}$
- $\mathcal{R} = \mathcal{S} \times \mathcal{S}$

論理側で見たときには $\mathcal{S}$ のうち **$*$の元が命題に対応する。**

### stratified な場合との対応
PTS においての階層を考える。
$\Gamma$ を well-formed な Context とする。
この $\Gamma$ の下で項の階層を考えると、それが stratified な場合と対応している。
- $\square$
- $K$ s.t. $\Gamma \vdash K: \square$ ... kind
- $T$ s.t. $\Gamma \vdash T: K: \square$ ... type (constructors)
  - このうち、 $T$ s.t. $\Gamma \vdash T: *$ ... の場合が type
- $t$ s.t. $\Gamma \vdash t: T: *$ ... term

## $\mathcal{R}$ との対応
$\mathcal{R} = \{(*, *), (*, \square), (\square, *), (\square, \square)\}$
のそれぞれについて何が許されるかを見てみる。
### $(*, *)$
単純型付きラムダ計算や命題論理に対応する。
- $A: *, B: *$ に対して $A \to B: *$

### $(\square, *)$
高階な論理を記述できる：「任意の命題 $P$ に対して $P \to P$ 」とか。
- $\vdash ((P: *) \to P \to P): * = s_3$
  - $\vdash *: \square = s_1$
  - $P: * \vdash (P \to P): * = s_2$

### $(*, \square)$
述語論理や依存型に対応する。
「$A: *$ は命題」というだけでなく、集合としてみる？
その場合、 $P: A -> *$ は $A$ という集合上の述語として考えられる。
これがちゃんと context に入るために、 $(*, square)$ が必要である。
- $A: * \vdash (A \to *): \square = s_3$
  - $A: * \vdash A: * = s_1$
  - $A: *:: _: A \vdash *: \square = s_2$

これがないと、 context に $A: *, P: A -> *$ を入れることができないことに注意する。
あとは「任意の $a in A$ について $P a$ = $forall a: A. P a$ 」という命題は次に対応するので、次のように書ける。
（これは $(*, *) \in \mathcal{R}$ から）。
- $A: *:: P: A \to * \vdash ((a: A) \to P @ a): *$
  - $A: *:: P: A \to * \vdash A: *$
  - $A: *:: P: A \to * :: a: A \vdash P a: *$

### $(\square, \square)$
正直これはよくわかっていない。
これは type constructor のようなものの記述になっている。
$A: * \to *$ とかをコンテキストに入れるときに必要になる。
例えば、 $\vdash ((A: *) \mapsto A): ((A: *) \to *)$ について考える。
$(A: *) \mapsto A$ は型 $A$ を入れると型 $A$ が返ってくるので、 type constructor であり、その kind は $(A: *) \to *$ である。
$(A: *) \to *$ の kind をちゃんと見るためには、次のように $(\square, \square)$ が必要になる。
- $\vdash ((A: *) \to *): \square = s_3$
  - $\vdash *: \square = s_1$
  - $A: * \vdash *: \square = s_2$

# CoC の性質
## impredicativity
この体系では、「任意の命題 $P$ について、 $P \to P$」という命題が記述できて、これ自身も命題である。
命題の上で量子化をとって、それ自体が命題になっているが、こういった現象が起こる体系（PTSや型システムに限らず、証明とかの文脈で出てくる体系）を impredicative という。
（"こういった"ね。これ以外も impredicative と呼ばれるものがある。）
Russel の paradox では、 ${x | x in.not x}$ という集合を考えたが、これも impredicative の一種であり、
impredicative な体系は変なことをすると矛盾しやすいらしい。

## consistency
CoC を証明体系としてみると、 $Gamma tack t: T$ は $T$ という命題が証明できて、それの証拠が $t$ である、と思える。
証明体系としてみたときに、何も仮定がないのに矛盾が示せてしまうとおかしい。
矛盾を爆発律をもとに考えると、 CoC での対応物は $(\Pi P:*.P)$ になる。
これは全ての"命題"が成り立つということに対応する。
なので、 CoC が"意味のある"証明体系になっているためには、
これを証明するような項が存在してはいけない。

> 項 $t$ であって、次をみたすものは存在しない
> $ \vdash t: (\Pi P:*. P) $

CoC のよい性質としては strong normalization が成り立つことがあるが、一番（証明体系としてみたときに）重要なのはこれだと思う。

# hierarchy と cumulative

## Coq っぽい sort の増やし方 (hierarchy)
CoC は Context に $X: \square$ を入れることができない。
理由は単純に、 $\square: s$ となる $s in \mathcal{S}$ がないから。
これができるように、無限に階層をあげることを考えるとよい。
またほかにも、 Prop をそのまま集合とか型として解釈したりするより、それ用の sort があった方がよい。
こういう動機で出てきたのかはわからないが、
Coq ではこんな感じでいろいろな sort が登場する。
- $\mathcal{S} = \{*^s, *^p, \square_(i \in \mathbb{N})\}$
- $\mathcal{A} = \{(*^s, \square_0), (*^p, \square_0), (\square_i, \square_(i+1))\}$
$*^s$ が集合で、$*^p$ が命題である。
$\mathcal{R}$ はもうちょっと複雑で、次の合併として定義される。
- $\{(s, *^p) | s \in \mathcal{S} \}$
- $\{(s, *^s) | s = {*^s, *^p} \}$
- $\{(\square_i, \square_j, \square_{\text{max}(i,j)}) \}$
- cumulativity から本当は来てるやつ
  - ${(*^p, \square_j), (*^s, \square_j)}$

## set と predicativity
$\mathcal{S} = \{*, \square\}$ だけのときに、高階論理を使うために $(\square, *) in \mathcal{R}$ が必要だとわかっていた。
これが使えると $\vdash (\Pi P:*.P -> P): *$ のようなこと（ $*^p$ を impredicative にすること ）ができるが、
これを $*^s$ でも使えるようにはしないのか
つまり、Set を impredicative にしないのだろうか。

しないらしい。
理由は多分、強すぎるからだと思われる。
（なにか公理を加えると inconsistent になりやすい。）

例として、帰納的な型の定義時の話を見てみる。

```coq
Record group: Type := mkGrp
{ X: Set }.

Fail Record group: Set := mkGrp {X: Set}.
(* is not definable because it should type Type *)

Inductive group2: forall (X: Set), Type :=
  test: forall (X: Set), group2 X.

Fail Inductive group2: forall(X: Set), Set :=
  test: forall (X: Set), group2 X.
 (* is not definable because it shouls type Type *)
```
こういうのは許されない

## cumulativity
Luo の ECC で提案されているように、
hierarchy を入れるならある種の lifting ができるとうれしい。
つまり、 $t: \square_i$ という元を $t: \square_{i+1}$ に格上げできるとよい。
この規則をそのまま突っ込むよりも、もうちょっと扱いやすいように、
universe とか kinding に対して $A \leq B$ のような関係を定義して、
$t: A$ なら $t: B$ とするとよい。
これは Coq の subtyping rule として入っている。
- $t \equiv t' => t \leq t'$
- $\square_i \leq \square_j$ if $i \leq j$
- $*_p \leq *_s$
- $*_s \leq \square_i$
- $\Pi x: T. T' \leq \Pi x: U. U'$ if $T \equiv T'$ $U \leq U'$
これを用いて conversion rule が次のように変形されている。
$$ \dfrac{\Gamma \vdash t: T \quad \Gamma \vdash U: s \quad T \leq U}{\Gamma \vdash t: U} $$

Universe のレベルで、 $x: \square_i$ なら $x: \square_{i + 1}$ のように、小さい宇宙の object を大きい宇宙がすべて含んでいると、 cumulative という。
