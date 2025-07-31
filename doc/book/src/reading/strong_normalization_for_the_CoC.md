https://arxiv.org/abs/2210.11240

# Introduction
strong normalization の証明は次のようなものがある。

1. Original: Geuvers と Nederhof -> Simplification: Barendregt による、 CC を $F_\omega$ に埋め込むやり方
  これは reduction を保つようにしている。
2. Geuvers による、 CC の type を expression の集合に解釈するやり方
  Saturated な方法に近い。
3. Melli'es と Werner による realizability semantics
  PTS の広いクラスで定義している。

# PTS
これは省略

# simple metatheory
次が成り立つ。
- Confluence: $a \to a_1$, $a \to a_2$ なら $a_1 \to b \leftarrow a_2$ がある
- preservation: $\Gamma \vdash a: T$, $a \to a'$ なら $\Gamma \vdash a'* T$

次が重要で、項の階層を与えている。
- classification: $\Gamma \vdash A: B$ なら次のどれか1つのみが成り立つ
  - $B = \square$ ... $A$ は kind
  - $\Gamma \vdash B: \square$ ... $A$ は constructor
  - $\Gamma \vdash B: *$ ... $A$ は term

ここで、 **kind は Context によらない** らしい。
- [ ] 後で調べる // TODO

constructor と term を証明の中で見通しよく扱うために、 variable の階層を分けるのもよい。
（memo: あるいは、 $x^s$ のように、 variable と sort をメモしておくのも見かけた。コンテキストの中でも、 $x::A::s$ のように sort をメモしておく方がよいという話もある。）
基本的には、この階層に基づいて、 interpretation を行う。

# structure of proofs
基本的には、 interpretation として、 type interpretation $\llbracket \cdot \rrbracket$ と term interpretation $\lbrack \cdot \rbrack$ の 2 つを導入する。
context は type interpretation で考えて、 term $\in$ type となるようにする： soundness という。

# CC の $F_\omega$ への埋め込み
## Intuition
CC は $F_\omega$ に依存型 $(*, \square)$ を足している。
なので、 $(x: A) \to B$ で $A: *, B: \square$ という関数（ 典型的には $B=*$ で term から type を作る）を $F_\omega$ にどのように埋め込むかが問題。
ざっくりと、 $A: *$ なら無視してしまえばいい。
ただし、項の reduction に対する preservation を考える必要が、 term interpretation のときに出てくる。

今、 $0: *$ という変数を fix して context の interpretation に入れておく。
（議論の中でかぶらないようにとる。）

ここで、 sort と kind の mapping は、 $\square \mapsto *$, $* \mapsto *$ になる。 **階層がずれる。**
また、 type ごとに canonical inhabitant を作る。

$A: *$ のときには、 $A \to *$ は $\llbracket A \to * \rrbracket = \llbracket A \rrbracket \to 0$ とする。
また redex を保つために、 $\lbrack (\lambda x: A. B) @ a \rbrack = (\lambda y: 0. \lambda x. \llbracket A \rrbracket. B) \lbrack A \rbrack \lbrack a \rbrack$ のようにする。

## def

- $V: \{\text{sorts or kinds}\} F_\omega$
  - $$V(\square) = V(*) = *$$
  - $$V((x: A) \to B) = \begin{cases}
    V(A) \to V(B) & \text{if $A$ is a kind} \\
    V(B) & \text{otherwise}
    \end{cases}$$
- $\llbracket \cdot \rrbracket_{\Gamma}: \{\Gamma\text{-constructor}\} \to F_\omega$
  - $\llbracket \square \rrbracket = \llbracket * \rrbracket = 0$
  - $\llbracket x \rrbracket = x$
  - $\llbracket (x: A) \to B \rrbracket = \begin{cases}
    (x: V(A)) \to \llbracket A \rrbracket \to \llbracket B \rrbracket_{\Gamma::x: A} & \text{if }A\text{ is a kind} \\
    (x: \llbracket A \rrbracket) \to \llbracket B \rrbracket_{\Gamma:: x: A} & \text{otherwise} = \text{if }A\text{ is a }\Gamma\text{-Type}
    \end{cases}$
  - $\llbracket \lambda x: A. b \rrbracket = \begin{cases}
    \lambda x: V(A). \llbracket B \rrbracket_{\Gamma:: x: A} & \text{if }A\text{ is a kind} \\
    \llbracket B \rrbracket & \text{if }A\text{ is a }\Gamma\text{-Type}
    \end{cases}$
  - $\vdots$
- $\llbracket \emptyset \rrbracket = 0:* :: z: (x: * \to *)$
- $\llbracket \Gamma::x: A \rrbracket = \llbracket \Gamma \rrbracket :: x: \llbracket A \rrbracket, w^x: x$ if $A$ is $\Gamma$-kind other wise $w^x: x$ is ommited.

この interpretation はうまくいって、 soundness of sort, kind として $\Gamma \vdash A: B$ なら $\llbracket \Gamma \rrbracket \vdash \llbracket A \rrbracket: V(B)$ が成り立つ。

各 $B$ に対して、 type としての $B$ に canonical inhabitant を作る。
- $c^B$ :=
  - $z B$ ... $B$ が type
  - $0$ ... $B = *$
  - $(x: A) \to B$ ... $\lambda x: A. c^B$
- $\lbrack \cdot \rbrack$ :=
  - $\lbrack * \rbrack = c^0$
  - $\lbrack x \rbrack = w^x \text{if }x\text{ is a}\Gamma\text{-type otherwise } x$
  - $\vdots$

$a \to a'$ なら $\lbrack a \rbrack \to^+ \lbrack a' \rbrack$
これでちゃんと redex がちゃんと残るので、 $F_\omega$ 側で $\lbrack a_0 \rbrack \to^+ \cdots$ という無限列の存在が議論できるようになる。
なので strong normalization が成り立つ。

# saturated sets を使う。
Girard-Tait による、 saturated sets の方法を拡張したような方法。
なるべく reduction を避けたとして、それでも入ってくる redex のみを考えればいい。
$x @ a_1 \cdots a_n$ は $x$ が変数なので $a_i$ の reduction をせずに止める、 $(\lambda x: A. b) @ a$ は $A, b, a$ の reduction をせずにもう簡約するなど。 

- $\textbf{BASE}$ := $\{x@a_1 @ \cdots @ a_n \mid\}$
- partial function of exp to exp $A \mapsto \text{key-redex}(A)$ :=
  - $(\lambda x: A. b) @ a \mapsto (\lambda x: A. b) @ a$
  - $A @ B \mapsto \text{key-redex}(A)$ 
- partial function exp to exp $A \to \text{red}(A)$ := $A$ の key-redex の簡約
- $S$ が saturated とは （ $S \in \textbf{SAT}$ :=）
  - $\textbf{SN} \cap \textbf{BASE} \subset S \subset \textbf{SN}$
  - $A \in \textbf{SN}$, $\text{red}(A) \in S$ なら $A \in S$
- 普通の subset of exp $S_1, S_2$ に対して、
  - $\Pi(S_1, S_2) := \{a \mid \forall b \in S_1, a@b \in S_2\}$

このとき次が成り立つ。
- $a \to \text{red}(a)$
- $a$ が key-redex を持ち $a \to b$ が key-redex の簡約じゃないなら $b$ は key-redex を持ち $\text{red}(a) \to^* \text{red}(b)$
- $a, b, \text{red}(a @ b)$ が SN なら $a @ b$ も SN
- $\bigcap S\text{ is saturated set}$ は saturated set
- $S_1, S_2 \in \textbf{SAT}$ なら $\Pi(S_1, S_2) \in \textbf{SAT}$

こうすると、 kind や sort の interpretation は次のようになる。
（ \{f \mid f: V(A) \to V(B)\} は set-theoretic function のこと。）
- $V(\square) = V(*) = \textbf{SAT}$
- $V((x: A) \to B) = \begin{cases}
  \{f \mid f: V(A) \to V(B) \} & \text{when }A\text{ is a kind} \\
  V(B) & \text{otherwise} \end{cases}$

次は variable に sets を割り当てる environment を定義する。
constructor と term それぞれに environment を割り当てるが、 term の方は constructor envinronment に依存する必要がある。

- constructor environment $\sigma$ for context $\Gamma$ は、 type variable to set のこと
- $(x: A) \in \Gamma$ で $A$: kind なら $\sigma(x) \in V(A)$ を満たすとき、 $\sigma \vDash \Gamma$ と書く。
- term environment は variable to set のこと
- $(x: A) \in \Gamma$ なら $\rho(x) \in \llbracket A \rrbracket_{\sigma}$ を満たす term env. $\rho$ を $\sigma \rho: \Gamma$ と書く。

これで interpretation が定義できる。

- $\llbracket \cdot \rrbracket_\sigma$ :=
  - $\llbracket \square \rrbracket = \llbracket * \rrbracket = \textbf{SN}$
  - $\llbracket x \rrbracket = \sigma(x)$
  - $\llbracket (x: A) \to B \rrbracket = \begin{cases}
    \Pi(\llbracket A \rrbracket, \cap_{S \in V(A)} \llbracket B \rrbracket_{\sigma[x \mapsto S]}) & \text{when }A\text{ is a kind} \\
    \Pi(\llbracket A \rrbracket, \llbracket B \rrbracket) & \text{otheraise}
    \end{cases}$
  - $\llbracket \lambda x: A. b \rrbracket = \begin{cases}
    S \in V(A) \mapsto \llbracket B \rrbracket_{\sigma[x \mapsto S]} & \text{when }A\text{ is a kind} \\
    \llbracket b \rrbracket & \text{otherwise}
    \end{cases}$
  - $\llbracket a @ b \rrbracket = \begin{cases}
    \llbracket a \rrbracket \llbracket b \rrbracket & \text{if }b\text{ is a }\Gamma\text{-constructor} \\
    \llbracket a \rrbracket & \text{otherwise}
    \end{cases}$
