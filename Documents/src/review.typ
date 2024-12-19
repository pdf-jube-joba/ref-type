#import "@preview/ctheorems:1.1.2": *
#import "@preview/simplebnf:0.1.1": *
#import "@preview/curryst:0.3.0": rule, proof-tree

#set heading(numbering: "1.1.")

#let definition = thmbox("definition", "Definition", fill: rgb("#eeffee"))
#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#set math.equation(numbering: "1.")

#show: thmrules.with(qed-symbol: $square$)

= 目的
ここでは、 Coq や Lean で使われている型システムの話として次についてメモをとっておく。
- Calculus of Constructions
- Cumulative universe / hierarchy
- Inductive type
- predicative
目的としては、「何をやると型システムがだめになるのか」を抑えるためである。

= 資料
== 一般
- Types and Programming Languages
- Advanced Topics in Types and Programming Languages
- https://inria.hal.science/inria-00076024/document
  - Coquand, Thierry, and Gérard Huet. The calculus of constructions. Diss. INRIA, 1986.
- https://homepages.inf.ed.ac.uk/wadler/papers/barendregt/pure-type-systems.pdf
  - introduction to generalized type systems, Henk Barendregt, 1991.

- https://home.ttic.edu/~dreyer/course/papers/barendregt.pdf
  - lambda calculi with types, Henk Barendregt, 1992.
- https://florisvandoorn.com/papers/struct_pts.pdf
  - The Structural Theory of Pure Type Systems, Cody Roux and Floris van Doorn, 2014.
- https://mimuw.edu.pl/media/uploads/doctorates/thesis-agnieszka-kozubek.pdf
  - formalization of the naive type theory
- https://era.ed.ac.uk/bitstream/handle/1842/12487/Luo1990.Pdf
  - Extended Calculus of Constructions
- https://www.lix.polytechnique.fr/Labo/Benjamin.Werner/publis/lmcs.pdf
  - ON THE STRENGTH OF PROOF-IRRELEVANT TYPE THEORIES

== 帰納型
- http://cl-informatik.uibk.ac.at/teaching/ss19/itp/slides_vo/09.pdf
  - Calculus of Inductive Constructions, 2008, MariaJo˜aoFrade
- https://www.cs.cmu.edu/~fp/papers/mfps89.pdf
 - Inductively Defined Types in the Calculus of Constructions
- https://link.springer.com/chapter/10.1007/BFb0037116
  - Inductive definitions in the system Coq rules and properties

== strong normalization や type check について
- https://arxiv.org/pdf/2102.06513
  - Complete Bidirectional Typing for the Calculus of Inductive Constructions
- https://www.cambridge.org/core/services/aop-cambridge-core/content/view/348B6914C707F5282ED91E08AE47BDB8/S0956796800020037a.pdf/modular-proof-of-strong-normalization-for-the-calculus-of-constructions.pdf
  - Modular proof of strong normalization for the calculus of constructions. Geuvers, Herman, and Mark-Jan Nederhof. 1991.
- https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=23af5ccb0b9d053741aeea62e4c8ac911da52327
  - Constructions Inductive Types and Strong Normalization
- https://pure.tue.nl/ws/portalfiles/portal/1688613/9314435.pdf
  - A typechecker for bijective pure type systems
  - context に type とその sort をいれた体系にして type check をいい感じにする

== inconsistency について
- https://alexandria.tue.nl/openaccess/Metis211677.pdf
  - (In)consistency of Extensions of Higher Order Logic and Type Theory, Herman Geuvers, 2006.
- https://arxiv.org/pdf/1911.08174
  - failure of normalization in impredicative type theory with proof-irrelevant propositional equality, ANDREAS ABEL, THIERRY COQUAND, 2020
- https://arxiv.org/pdf/2308.16726
  - A variation of Reynolds-Hurkens Paradox
- https://www.cs.ru.nl/~herman/PUBS/newnote.pdf
  - Inconsistency of classical logic in type theory
- https://www.cs.ru.nl/~herman/PUBS/InconsAutSetTh.pdf
  - Inconsistency of “Automath powersets” in impredicative type theory

= Pure Type System
== definition
次のものが与えられているとする。
- Set of Sort $cal(S)... "Set"$
- Set of Axiom $cal(A)... "SubSet of" cal(S) times cal(S)$
- Set of Relation $cal(R)... "SubSet of" cal(S) times cal(S) times cal(S)$
注意点として、次のようにかいたりする。
- $(a, b) in cal(A)$ であることを $a: b$ と書く。
- $a, b in cal(S)$ が $(a, b, b) in cal(R)$ を満たしていたら、単に $(a, b) in cal(R)$ とも書く。
また、変数を定義するため、変数の集合 $cal(V)$ を固定しておく。

また、 $beta$ reduction は省略する。

#definition("項とコンテキスト")[
#bnf(
  Prod(
    annot: "Term",
    $t$,
    {
      Or[$s in cal(S)$][_kind_]
      Or[$cal(V)$][_variable_]
      Or[$lambda cal(V): t. t$][_lambda abstraction_]
      Or[$Pi cal(V): t. t$][_dependent product type_]
      Or[$t$ $t$][_application_]
    },
  ),
)
#bnf(
  Prod(
    annot: "Context fragment",
    $gamma$,
    {
      Or[$cal(V): t$][_declare_]
    }
  )
)
#bnf(
  Prod(
    annot: "Context",
    $Gamma$,
    {
      Or[$emptyset$][_empty context_]
      Or[$Gamma :: gamma$][_concat_]
    }
  )
)
]

#definition("judgement 一覧")[
- well found context... $Gamma: "Context"$ に対して、 
  $ tack Gamma $
- type judgement... $Gamma: "Context"$, $e_i: "Term"$ に対して、
  $ Gamma tack e_1: e_2 $
]

#definition("judgement の関係")[
- empty context の well found:
  $ #proof-tree($tack emptyset$) $
- context をのばす:
  $ #proof-tree(rule(
    $tack Gamma :: (x: t)$,
    $tack Gamma$,
    $Gamma tack t: s$,
    $x in.not Gamma$,
    $s in cal(S)$,
  )) $
- variable を使う
  $ #proof-tree(rule(
    $Gamma tack x: t$,
    $tack Gamma$,
    $(x: t) in Gamma$,
  )) $
- axiom
 $ #proof-tree(rule(
  $Gamma tack s_1: s_2$,
  $tack Gamma$,
  $(s_1, s_2) in cal(A)$,
 )) $
- dependent product の formation
  $ #proof-tree(rule(
    $Gamma tack (Pi x: t. T): s_3$,
    $Gamma tack t: s_1$,
    $Gamma:: x: t tack T: s_2$,
    $(s_1, s_2, s_3) in cal(R)$,
  )) $
- dependent product の introduction
  $ #proof-tree(rule(
    $Gamma tack (lambda x: t. m): (Pi x:t. M)$,
    $Gamma tack (Pi x:t. M): s$,
    $Gamma ::x: t tack m: M$,
    $s in cal(S)$,
  )) $
- application 
  $ #proof-tree(rule(
    $Gamma tack f a: T[x := a]$,
    $Gamma tack f: (Pi x:t. T)$,
    $Gamma tack a: t$,
  )) $
- conversion rule
  $ #proof-tree(rule(
    $Gamma tack t: T_2$,
    $Gamma tack t: T_1$,
    $Gamma tack T_2: s$,
    $T_1 equiv^beta T_2$,
  )) $
] 

= Calculus of Constructions と lambda cube
Calculus of Constructions はその導入は Coquand らしいが、
その元論文での定義はあまり使われていなくて、
arendregt による PTS を使った lambda cube の一頂点として導入するのが一般的みたい。
でも、探してみても元論文の定義との同値性のような話はあまりされていなかった。

== calculus of constructions
PTS において、 $cal(S) = {*, square}$, $cal(A) = {(*, square)}$, $cal(R) = {(*, *), (*, square), (square, square), (square, *)}$ としたものが Calculus of Constructions である。

*$*$ の元が命題に対応する*

== ATTaPL の定義について
型システムを定義するときはだいたい、型の層と項の層はわかれていることが多い。
stratified という？
ATTaPL では logical framework をもとに CoC を導入しているので、
stratified な形で定義されている。
でも、「これが元の定義と同値か」とか「PTSの定義と同値か」といった話は全然証明もなかった。

#definition("項とコンテキスト")[
#bnf(
  Prod(
    annot: "Term",
    $t$,
    {
      Or[$cal(V)$][_variable_]
      Or[$lambda cal(V): T. t$][_lambda abstraction_]
      Or[$t$ $t$][_application_]
      Or[$text("all") x: T. t$][_universal quantification_]
    },
  ),
)
#bnf(
  Prod(
    annot: "Type",
    $T$,
    {
      Or[$cal(V)$][_type variable_]
      Or[$Pi cal(V): T. T$][_dependent product_]
      Or[$T$ $t$][_type family application_]
      Or[$text("all") cal(V): T. t$][_universal quantification_]
      Or[$text("Prop")$][_Propositions_]
      Or[$text("Proof")$][_family of proofs_]
    },
  ),
)
#bnf(
  Prod(
    annot: "Kinds",
    $K$,
    {
      Or[$*$][_kind of proper type_]
      Or[$Pi cal(V):T. K$][_kind of type family_]
    }
  )
)
#bnf(
  Prod(
    annot: "Context fragment",
    $gamma$,
    {
      Or[$cal(V): T$][_type declare_]
      Or[$cal(V): K$][_kind declare_]
    }
  )
)
#bnf(
  Prod(
    annot: "Context",
    $Gamma$,
    {
      Or[$emptyset$][_empty context_]
      Or[$Gamma :: gamma$][_concat_]
    }
  )
)
]

conversion として次のものを入れる...
$"Proof" ("all" x: T. t) -> Pi x: T. "Proof" t$

#definition("judgement")[
$ #proof-tree(rule(
  label: "axiom",
  $Gamma tack_("wf-kind") *$
)) $
$ #proof-tree(rule(
  label: "pi",
  $Gamma tack_("wf-kind") Pi x: T. K$
)) $
$ #proof-tree(rule(
  label: "var",
  $Gamma tack_("kind") X: K$,
  $Gamma tack_("wf-kind") K$,
  $(X: K) in Gamma$,
)) $
$ #proof-tree(rule(
  label: "pi",
  $Gamma tack_("kind") (Pi x: T_1. T_2): *$,
  $Gamma tack_("kind") T_1: *$,
  $Gamma, x: T_1 tack_("kind") T_2: *$,
)) $
$ #proof-tree(rule(
  label: "app",
  $Gamma tack_("kind") S t: K[x := t]$,
  $Gamma tack_("kind") S: (Pi x: T. K)$,
  $Gamma tack_("type") t: T$,
)) $
$ #proof-tree(rule(
  label: "conv",
  $Gamma tack_("kind") T: K$,
  $Gamma tack_("kind") T: K'$,
  $K equiv K'$,
)) $
$ #proof-tree(rule(
  label: "prop",
  $Gamma tack_("kind") "Prop": *$,
)) $
$ #proof-tree(rule(
  label: "proof",
  $Gamma tack_("kind") "Proof":  (Pi x: "Prop". *)$,
)) $
$ #proof-tree(rule(
  label: "var",
  $Gamma tack_("type") x: T$,
  $Gamma tack_("kind") T: *$,
  $(x: T) in Gamma$,
)) $
$ #proof-tree(rule(
  label: "abs",
  $Gamma tack_("type") (lambda x: S. t):  (Pi x: S. T)$,
  $Gamma tack_("kind") S: *$,
  $Gamma, x: S tack_("type") t: T$,
)) $
$ #proof-tree(rule(
  label: "app",
  $Gamma tack_("type") t_1 t_2:  T[x := t_2]$,
  $Gamma tack_("type") t_1: (Pi x: S. T)$,
  $Gamma tack_("type") t_2: S$,
)) $
$ #proof-tree(rule(
  label: "conv",
  $Gamma tack_("type") t:  T'$,
  $Gamma tack_("type") t: T$,
  $T equiv T'$,
)) $
]

== 性質について
=== 階層構造と straitification
$Gamma$ を (well-formed な) Context とする。
ここらへんは、 lambda calculi with types が詳しい。
この $Gamma$ の下で項の階層を考えることができる。
- $square$
- $Gamma tack t: square$ な項 $t$ ... kind
- $Gamma tack t: A: square$ な項 $t$ ... type
- $Gamma tack t: A: *$ な項 $t$ ... term
この階層がちょうど ATTaPL での stratified な項の定義に対応しているはずだ。

=== $cal(R)$ によって何が許されるか
$cal(R) = {(*, *), (*, square), (square, *), (square, square)}$ と $4$ つあるルールについて、これがあると何ができるようになるかをみたい。
以下では、 $A -> B$ を、 $B$ に入っていない変数 $x$ をとってきて $Pi : A. B$ の略記とする。

==== $(*, *)$
単純型付きラムダ計算や、命題論理に対応するらしい。
$A: *$ な項 $A$ が命題で、 $a: A$ が $A$ であることの証明項。
例えば $A, B$ が命題のとき、 $A -> B$ という項も命題である。
次が書けるようになる。
$
#proof-tree(rule(
  $A: *, B: * tack (A -> B = Pi x. A. B): *$,
  $A: *, B: * tack A: *$,
  $A: *, B: *, x: A tack B: *$,
))
$

==== $(square, *)$
高階な論理を許すことができる。
例えば、命題でいうと、「任意の命題 $P$ について、 $P -> P$」 である、という命題が記述できるようになる。
$
#proof-tree(rule(
  $tack (Pi P: *. P -> P): *$,
  $tack *: square$,
  $P: * tack (P -> P): *$
)
)
$

==== $(*, square)$
述語論理や依存型を許すことができる。
ただし、述語論理との対応させ方は注意する。
「$A: *$ は命題」というだけでなく、集合としてみる？
その場合、 $P: A -> *$ は $A$ という集合上の述語として考えられる。
これがちゃんと context に入るために、 $(*, square)$ が必要である。

$
#proof-tree(rule(
  $A: * tack (A -> * = Pi x: A. *): square$,
  $A: * tack A: *$,
  $A: *, x: A tack *: square$,
))
$

これがないと、 context に $A: *, P: A -> *$ を入れることができないことに注意する。
あとは「任意の $a in A$ について $P a$ = $forall a: A. P a$ 」という命題は次に対応するので、次のように書ける。
$
#proof-tree(rule(
  $A: *, P: A -> * tack (Pi a: A. P a): *$,
  $A: *, P: A -> * tack A: *$,
  $A: *, P: A -> *, a: A tack P a: *$
))
$

==== $(square, square)$
正直これはよくわかってない。
$A: * -> *$ などをコンテキストに入れたりするのに必要になる。

=== impredicativity
$(square, *)$ で見たように、この体系では 「任意の命題 $P$ について、 $P -> P$」という命題が記述できて、これ自体も命題である。
命題の上で量子化をとって、それ自体が命題になっているが、こういった現象が起こる体系（PTSや型システムに限らず、証明とかの文脈で出てくる体系）を impredicative という。
Russel の paradox では、 ${x | x in.not x}$ という集合を考えたが、これも impredicative の一種であり、
impredicative な体系は変なことをすると矛盾しやすいらしい。

=== consistency
CoC を証明体系としてみると、 $Gamma tack t: T$ は $T$ という命題が証明できて、それの証拠が $t$ である、と思える。
証明体系としてみたときに、何も仮定がないのに矛盾が示せてしまうとおかしい。
矛盾を爆発律をもとに考えると、 CoC での対応物は $(Pi P:*.P)$ になる。
これは全ての"命題"が成り立つということに対応する。
なので、 CoC が"意味のある"証明体系になっているためには、
次が成り立たないといけない。

#theorem("consistency")[
  項 $t$ であって、次をみたすものは存在しない
  $ tack t: (Pi P:*. P) $
]

CoC のよい性質としては strong normalization が成り立つことがあるが、一番（証明体系としてみたときに）重要なのはこれだと思う。

= hierarchy と cumulative

== Coq っぽい sort の増やし方 (hierarchy)
CoC は Context に $X: square$ を入れることができない。
理由は単純に、 $square: s$ となる $s in cal(S)$ がないから。
これができるように、無限に階層をあげることを考えるとよい。
またほかにも、 Prop をそのまま集合とか型として解釈したりするより、それ用の sort があった方がよい。
こういう動機で出てきたのかはわからないが、
Coq ではこんな感じでいろいろな sort が登場する。
- $cal(S) = {*_s, *_p, square_(i in NN)}$
- $cal(A) = {(*_s, square_0), (*_p, square_0), (square_i, square_(i+1))}$
$*_s$ が集合で、$*_p$ が命題である。
$cal(R)$ はもうちょっと複雑で、次の合併として定義される。
- ${(s, *_p) | s in cal(S) }$
- ${(s, *_s) | s = {*_s, *_p}}$
- ${(square_i, square_j, square_(max(i,j)))}$
- cumulativity から本当は来てるやつ
  - ${(*_p, square_j), (*_s, square_j)}$

=== どんなことができるか

- $(*_s, square)$ より、 $A: *_s$ 上の述語 $A -> *_p$ が作れる
  - $#proof-tree(rule(
    $A: *_s tack (A -> *_p = Pi x: A. *_p): square$,
    $A: *_s tack A: *_s$,
    $A: *_s, x: A tack *_p: square$,
  ))$

=== Set の impredicativity について
$cal(S) = {*, square}$ だけのときに、高階論理を使うために $(square, *) in cal(R)$ が必要だとわかっていた。
これが使えると $tack (Pi P:*.P -> P): *$ のようなこと（ $*_p$ を impredicative にすること ）ができるが、
これを $*_s$ でも使えるようにはしないのか
... Set を impredicative にしないのだろうか。

しないらしい。
理由は多分、強すぎるからだと思われる。
（なにか公理を加えると inconsistent になりやすい。）

== cumulativity
Luo の ECC で提案されているように、
hierarchy を入れるならある種の lifting ができるとうれしい。
つまり、 $t: square_i$ という元を $t: square_(i+1)$ に格上げできるとよい。
この規則をそのまま突っ込むよりも、もうちょっと扱いやすいように、
universe とか kinding に対して $A <= B$ のような関係を定義して、
$t: A$ なら $t: B$ とするとよい。
これは Coq の subtyping rule として入っている。
- $t equiv t' => t <= t'$
- $square_i <= square_j$ if $i <= j$
- $*_p <= *_s$
- $*_s <= square_i$
- $Pi x: T. T' <= Pi x: U. U'$ if $T equiv T'$ $U <= U'$
これを用いて conversion rule が次のように変形されている。
$
#proof-tree(rule(
  $Gamma tack t: U$,
  $Gamma tack t: T$,
  $Gamma tack U: s$,
  $T <= U$,
))
$

= 帰納的な型



= inconsistency がいつ起こるか
ここでの inconsistency とは次のことをいう。
#theorem("inconsistency")[
  どんな型 $tack T: s$ に対しても、 $tack t: T$ を満たす項 $t$ が存在する。
]
ただ、 $forall P: "proposition". P$ がエンコードできるような体系なら、 inconsistency はだいたい、この型が項を持たないことに帰着する。

== type in type と impredicative
=== type in type
有名な話として、 PTS で $s in cal(S)$ であって $(s: s) in cal(A)$, $(s, s) in cal(R)$ となるものがあると矛盾する。
MLTT の一番最初のものはこれでだめだとわかったらしい。
（Girard's paradox）

=== system U
次に、 System $U$ と $U^-$ もあり、どっちも inconsistent
System $U$ は PTS で次のように定義する。
- $cal(S) = {*, square, triangle}$
- $cal(A) = *: square, square: triangle$
- $cal(R) = {(*, *), (*, square), (square, *), (triangle, *), (triangle, square)}$
System $U^-$ はここから $(triangle, *)$ を抜く。

=== impredicative sort
PTS として、なにかしら $s_1: s_2$ のようになっているとき、
$(s_2, s_1)$ なら $(Pi x: s_1. s_1 -> s_1): s_1$ となるから $s_1$ は impredicative な sort である。
このような sort は hierarchy の一番下でなければいけない。
つまり、 $(exists s_0): s_1$ になっているだけでだめ？
（folklore っぽい）
これは system $U^-$ の失敗と同じ。
system $U^-$ だけみると、 $(exists s_0): s_1$ だけでは矛盾するとは限らなそうだが。
ただ、ほかのと合わせ技で辛そう。

== dependent sum
$A times B$ の拡張として、 $x: A$ に依存して決まる $B(x)$ があるときに $x: A$ と $y: B(x)$ の組をペアにすることができそうだ。
これが依存和になる。

=== strong dependent sum と weak dependent sum
==== strong dependent sum
dependent sum はその除去に対応する項の作り方がいくつかある。
strong dependent sum は次のような感じ
#bnf(
  Prod(
    annot: "Term",
    $t$,
    {
      Or[$...$][]
      Or[$Sigma cal(V):t. t$][_dependent sum form_]
      Or[$(t, t)$][_dependent sum intro_]
      Or[$pi_1 t$][_projection 1_]
      Or[$pi_2 t$][_projection 2_]
    }
  )
)
$pi_1 (x, y) -> x$ と $pi_2 (x, y) -> y$ が計算になる。

$ #proof-tree(rule(
  $Gamma tack (Sigma x: T. T'): s_3$,
  $Gamma tack T: s_1$,
  $Gamma, x: T tack T': s_2$,
)) $
$ #proof-tree(rule(
  $Gamma tack (t_1, t_2): (Sigma x: T. T')$,
  $Gamma tack (Sigma x: T. T'): s$,
  $Gamma tack t_1: T$,
  $Gamma tack t_2: T'[x := t_1]$,
)) $
$ #proof-tree(rule(
  $Gamma tack pi_1 t: T$,
  $Gamma tack t: (Sigma x: T. T')$,
)) $
$ #proof-tree(rule(
  $Gamma tack pi_2 t: T'[x := pi_1 t]$,
  $Gamma tack t: (Sigma x: T. T')$,
)) $
ここの $(s_1, s_2, s_3)$ でなにを許すかが問題になる。
Luo の ECC で述べられているところによると、
1. $(s_1, s_2, s_3) = (square, *, *)$ をやると矛盾する。
2. $(s_1, s_2, s_3) = (*, *, *)$ は矛盾しない。
3. $(s_1, s_2, s_3) = (square_i, square_j, square_(max(i,j)))$ みたいなものは矛盾しない。
結局ここでも、 impredicativity が問題になっているようだ。

==== weak dependent sum
dependent sum を dependent sum なしの体系で再現しようとすると、 $pi_2$ はうまく作れない。
逆に言うと、 dependent sum を $pi_2$ だけ除いたようなやつは適当にやっても矛盾しなさそう。
$Sigma x: T. T' := Pi R: *_p. (Pi X: T. T' -> R) -> R$ みたいな感じでやる。

つまり、 $pi_2 (e)$ を用いて $pi_1 (e)$ が $B$ を満たすことを証明できるような状況になっていると多分矛盾する？
$(s_1, s_2, s_3) = (square, *, square)$ なら矛盾はしないと思うが。
== retract について
大きい universe を小さい universe に埋め込もうとすると変になる。
特に、 $*_p$ と $"bool"$ を同一視するとか、べき集合を $A -> square$ で表して $Pi A: square. (A -> square)$ のようなべき操作をとるとか、
=== classical logic + bool <=> Prop
bool は単に帰納的な型として $*_s$ に定義されている。

== large elimination
== propositional irrelevance
