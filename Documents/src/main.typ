#import "@preview/ctheorems:1.1.2": *
#import "@preview/simplebnf:0.1.1": *
#import "@preview/curryst:0.3.0": rule, proof-tree

#set heading(numbering: "1.1.")

#let definition = thmbox("definition", "Definition", fill: rgb("#eeffee"))
#set math.equation(numbering: "1.")

#show: thmrules.with(qed-symbol: $square$)

= 動機
次のような性質を持つ型理論が欲しい。
- より自然に property に関する subtyping が使える
  - $2$ が自然数でもあり偶数でもある。
    - Coq の場合は $2$ と $2$ が偶数であることの証明の組が偶数として型付けされる。
  - 部分集合が本当に部分集合になり、キャストが簡単（書かなくていい）
  - 結果として型付けの一意性はないと思うけど、それでもいい
- 証明項を真に区別する必要がない or 証明項を扱うことができない
  - 群が等しいとは群の演算が等しいこと、証明項まで等しいこととみなしたくない
  - 証明項を構成することもできるが、それの存在を覚えておくだけぐらいでいい
  - あと関数の外延性などの axiom をいい感じにしたい
- 構造に関する部分型（？）も使えると楽
  - 環は群の部分型とみなしたい（キャストを明示的に書きたくない）
  - これをやると部分空間の扱いが絶対にめんどくさい
  - 公称型みたいな感じで扱った方がいいかも
- 等式をもっと簡単に扱いたい、 well-definedness をもっと簡単に
  - 例として、商群からの写像の扱いが Coq ではめんどくさい
  - （部分集合系が扱えると良いなあ）

結局、証明項みたいなものを排除する体系なので、 proof-term omitted と呼ぶことにする。
（ refinement 以外もいろいろ入りすぎている。）

= notation
変数に使う集合は $cal(V)$ とかにしておく。
= 資料
- https://theses.hal.science/tel-02058937/document Extending higher-order logic with predicate subtyping : application to PVS
- https://era.ed.ac.uk/bitstream/handle/1842/12487/Luo1990.Pdf Extended Calculus of Constructions
- https://www.cs.cmu.edu/~kw/scans/hurkens95tlca.pdf A simplification of Girard's paradox
- https://ceur-ws.org/Vol-1525/paper-14.pdf Two set-based implementations of Quotient in type theory 
- https://home.ttic.edu/~dreyer/course/papers/barendregt.pdf lambda calculi with types 
- 他 scrapbox にあるやつ

= calculus of construction の復習
== pure type system を使う
pure type system の形で次のように書ける。
- $S = {PP, TT}$
- $A = {(PP, TT)}$
- $R = {(PP, PP), (PP, TT), (TT, PP), (TT, TT)}$
とする。
#definition("項とコンテキスト")[
  #bnf(
    Prod(
      annot: "Term",
      $t$,
      {
        Or[$s in S$][_kind_]
        Or[$x$][$x in cal(V)$, _variable_]
        Or[$lambda x: t. t$][$x in cal(V)$, _lambda abstraction_]
        Or[$Pi x: t. t$][$x in cal(V)$, _dependent product type_]
        Or[$t$ $t$][_application_]
      },
    ),
  )
  #bnf(
    Prod(
      annot: "Context snippet",
      $gamma$,
      {
        Or[$x: t$][$x in cal(V)$, $t: "Term"$, _declare_]
      }
    )
  )
  #bnf(
    Prod(
      annot: "Context",
      $Gamma$,
      {
        Or[$emptyset$][_empty context_]
        Or[$Gamma :: gamma$][$gamma$: Context snippet, _concat_]
      }
    )
  )
]

#definition("judgement 一覧")[
- well found context: $Gamma: "Context"$ に対して、 
  $ tack Gamma $
- type judgement: $Gamma: "Context"$, $e_i: "Term"$ に対して、
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
    $s in S$,
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
  $(s_1, s_2) in A$,
 )) $
- dependent product type の導入
  $ #proof-tree(rule(
    $Gamma tack Pi x: t. T: s_2$,
    $Gamma tack t: s_1$,
    $Gamma:: x: t tack T: s_2$,
    $(s_1, s_2) in R$,
  )) $
- dependent product の intro
  $ #proof-tree(rule(
    $Gamma tack (lambda x: t. m): (Pi x:t. M)$,
    $Gamma tack (Pi x:t. M): s$,
    $Gamma ::x: t tack m: M$,
    $s in S$,
  )) $
- application 
  $ #proof-tree(rule(
    $Gamma tack f a: T[x := a]$,
    $Gamma tack f: Pi x:t. T$,
    $Gamma tack a: t$,
  )) $
- $beta$ reduction について
  $ #proof-tree(rule(
    $Gamma tack t: T_2$,
    $Gamma tack t: T_1$,
    $Gamma tack T_2: s$,
    $T_1 equiv^beta T_2$,
  )) $
]

ただし、ここでは proposition と program を同一視している体系になっている。
Coq などでは、 Calculus of constructions とは違う形の $S$ を用いているので、
それに合わせたほうがいいかもしれない。

== stratified な場合
項を一気に定義するのではなく、
証明項、命題、型、などを階層化して定義することができるようだが。

たとえば、 $lambda_("LF")$ は pure type system としての形式化以外のやり方がある。

== 矛盾しないようにするために注意すること
以下はやらないようにする。
- type: type みたいなこと
  - 普通に sort として $s: s$ があるとだめっぽい？
  - pure type system として Prop ($*$) 以外に sort $s in S$ であって impredicative ($(s, s) in cal(R)$) となるものがあれば、矛盾するらしい。
    - これは理解を間違えている気がする。多分、 $(square, s) in cal(R)$ があるとまずい。
  - system $U$ や $U^-$ など（ Girard's paradox を参照）
    - これは循環な体系ではない（ $lambda_("HOL")$ の拡張になっている）がだめらしい。
- strong dependent sum っぽいことができるとまずい
  - $Gamma ::x: A tack B: PP$ から $Gamma tack (sum x:A. B): PP$ のようなものを付け加えると、 $pi_1$, $pi_2$ とその規則を付け加えることで矛盾する。
  - ただし、 $A: PP$ を仮定したり、 $A: TT_i$ のときに $Gamma tack (sum x:A. B): TT_i$ のようにするのであれば矛盾しない。 [ECC 2.4 節]
  - （ Extended calculus of constructions (Zhaohui Luo) を参照）
  - でも weak dependent sum はいいらしい（これがどういうものかはよくわからない。
  - ECC の 8.4 を読むと、weak sum （logical existential quantifier） は CC で再現できる
    - $exists x in A, P$ は $Pi R: PP. (Pi X: A. P -> R) -> R$ とする （ [ECC 6.1.3] ）
    - この場合、 $e: sum x:A. B$ に対して $pi_1 (e)$ が $B$ を満たすことが示せないぐらい弱い。
    - つまり、 $pi_2 (e)$ を用いて $pi_1 (e)$ が $B$ を満たすことを証明できるような状況になっていると多分矛盾する？
- large elimination
  - large elimination が単体でダメなのではなく、 excluded middle と impredicative な prop と合わせると矛盾するらしい。
  - singleton elimination はやってよいと coq では扱われているらしい。

= 証明と証明項を抽象化する
#definition[
  #bnf(
    Prod(
      annot: "Term",
      $t$,
      {
        Or[$s in S$][_kind_]
        Or[$x$][$x in cal(V)$, _variable_]
        Or[$lambda x: t. t$][$x in cal(V)$, _lambda abstraction_]
        Or[$Pi x: t. t$][$x in cal(V)$, _dependent product type_]
        Or[$t$ $t$][_application_]
        Or[$"Proof" t$][_proof of t_]
      },
    ),
  )
  #bnf(
    Prod(
      annot: "Context snippet",
      $gamma$,
      {
        Or[$x: t$][$x in cal(V)$, $t: "Term"$, _declare_]
        Or[$"Hold" t$][$t: "Term"$ _assumption_]
      }
    )
  )
  #bnf(
    Prod(
      annot: "Context",
      $Gamma$,
      {
        Or[$emptyset$][_empty context_]
        Or[$Gamma :: gamma$][$gamma$: Context snippet, _concat_]
      }
    )
  )
]

$a equiv^beta b$ なら $"Proof" a equiv^beta "Proof" b$ みたいに拡張しておく。

#definition("judgement 一覧")[
- well found context: $Gamma: "Context"$ に対して、 
  $ tack Gamma $
- type judgement: $Gamma: "Context"$, $e_i: "Term"$ に対して、
  $ Gamma tack e_1: e_2 $
- proposition: $t: "Term"$ に対して、 （ $t: PP$ と思って）コンテキストから証明可能を意味する。
  $ Gamma tack.double t $
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
    $s in S$,
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
  $(s_1, s_2) in A$,
 )) $
- dependent product type の導入
  $ #proof-tree(rule(
    $Gamma tack Pi x: t. T: s_2$,
    $Gamma tack t: s_1$,
    $Gamma:: x: t tack T: s_2$,
    $(s_1, s_2) in R$,
  )) $
- dependent product の intro
  $ #proof-tree(rule(
    $Gamma tack (lambda x: t. m): (Pi x:t. M)$,
    $Gamma tack (Pi x:t. M): s$,
    $Gamma ::x: t tack m: M$,
    $s in S$,
  )) $
- application 
  $ #proof-tree(rule(
    $Gamma tack f a: T[x := a]$,
    $Gamma tack f: Pi x:t. T$,
    $Gamma tack a: t$,
  )) $
- $beta$ reduction について
  $ #proof-tree(rule(
    $Gamma tack t: T_2$,
    $Gamma tack t: T_1$,
    $Gamma tack T_2: s$,
    $T_1 equiv^beta T_2$,
  )) $
- assumption の追加
  $ #proof-tree(rule(
    $tack Gamma :: "Hold" t$,
    $tack Gamma$,
    $Gamma tack t: PP$,
  )) $
- assumption の使用
  $ #proof-tree(rule(
    $Gamma tack.double t$,
    $"Hold" t in Gamma$,
  )) $
- 項の使用
   $ #proof-tree(rule(
    $Gamma tack.double t$,
    $Gamma tack p: t$,
    $Gamma tack t: PP$,
   )) $
- 証明項を作る
  $ #proof-tree(rule(
    $Gamma tack "Proof" t: t$,
    $Gamma tack.double t$
  )) $
]

= refinement type とか predicate subtyping と呼ばれているものの導入。
ざっくり、 $t: A$ かつ $P(t)$ が成り立てば、 $t: {x: A | P(x)}$ に型付けできる体系になる。
注意： $S = {*^p, *^s, square}$ にして、 Prop 用の sort と Set として解釈できるものを分けたほうがよいかも。
その場合は矛盾を避けつつ coq みたいな感じにする。
（でも cumulative はよくわからんのでやめておきたい。）
- $cal(A)= {(*^p: square), (*^s, square)}$
- $cal(R) =$
  - ${(*^p, *^p), (*^p, square), (square, *^p), (square, square)}$
  - ${(*^s, *^s), (*^s, square), (*^s, *^p)}$
なんかこれだめかも。

#definition[
  #bnf(
    Prod(
      annot: "Term",
      $t$,
      {
        Or[$s in S$][_kind_]
        Or[$x$][$x in cal(V)$, _variable_]
        Or[$lambda x: t. t$][$x in cal(V)$, _lambda abstraction_]
        Or[$Pi x: t. t$][$x in cal(V)$, _dependent product type_]
        Or[$t$ $t$][_application_]
        Or[$"Proof" t$][_proof of t_]
        Or[${x: t | t}$][_refinement type_]
      },
    ),
  )
  #bnf(
    Prod(
      annot: "Context snippet",
      $gamma$,
      {
        Or[$x: t$][$x in cal(V)$, $t: "Term"$, _declare_]
        Or[$"Hold" t$][$t: "Term"$ _assumption_]
      }
    )
  )
  #bnf(
    Prod(
      annot: "Context",
      $Gamma$,
      {
        Or[$emptyset$][_empty context_]
        Or[$Gamma :: gamma$][$gamma$: Context snippet, _concat_]
      }
    )
  )
]

- $a equiv^beta b$ なら $"Proof" a equiv^beta "Proof" b$
- $A equiv^beta A', P equiv^beta P'$ なら ${x: A | P} equiv^beta {x: A' | P'}$

#definition("judgement 一覧")[
- well found context: $Gamma: "Context"$ に対して、 
  $ tack Gamma $
- type judgement: $Gamma: "Context"$, $e_i: "Term"$ に対して、
  $ Gamma tack e_1: e_2 $
- proposition: $t: "Term"$ に対して、 （ $t: PP$ と思って）コンテキストから証明可能を意味する。
  $ Gamma tack.double t $
]

もとのに加えて次のようにする。

#definition[
- 部分型付けの導入
  $ #proof-tree(rule(
    $Gamma tack t: {x: A | P}$,
    $Gamma tack t: A$,
    $Gamma :: x: A tack P: PP$,
    $Gamma tack.double P t$,
  )) $
- 部分型付けから weak に型を取り出す。
  $ #proof-tree(rule(
    $Gamma tack t: A$,
    $Gamma tack t: {x: A | P}$,
  )) $
- 部分型付けから命題を取り出す。
   $ #proof-tree(rule(
    $Gamma tack.double P t$,
    $Gamma tack t: {x: A | P}$
   )) $
]

= equality の導入について
equality はなんか扱いがめんどくさいが主に 2 つあって、
- Leibniz equality を考える場合
  - $A: TT, a: A, b: B$ に対して $a =^A b := Pi (P: A -> PP). P a -> P b$
- inductive な型のように項の定義を広げる場合
  - term := $ ... | "Id"_t (t, t) | "refl"_(t, t)$
    - $a =^A b$ は $"Id"_A (a, b)$ のことになる。
  - conversion ...
  - judgement
    - form $ #proof-tree(rule(
      $Gamma tack "Id"_A (a, b): PP$,
      $Gamma tack A: PP$,
      $Gamma tack a: A$,
      $Gamma tack b: A$,
    )) $
    - intro $ #proof-tree(rule(
      $Gamma tack "refl"_(A, a): "Id"_A (a, a)$,
      $Gamma tack "Id"_A (a, a): PP$,
    )) $
    - elim $ #proof-tree(rule(
      $Gamma $
    )) $

ところで、ほしい性質として、構造の等しさの証明に、性質（の証明）の等しさを要求しないというものがある。
これは $a, b: {x: A | P}$ に対して、 $a =^A b$ なら $a =^{x: A | P} b$ を与えることになっているはず。
なので、次を導入したい。
$ #proof-tree(rule(
  $Gamma tack.double a=^{x: A | P} b$,
  $Gamma tack a: {x: A | P}$,
  $Gamma tack b: {x: A | P}$,
  $Gamma tack.double a=^A b$,
)) $

inductive type みたいなものを全然知らないけど、 refl が $"refl"_A a$ ではなく $"refl" a$ として考えれるような場合はおかしい？

= 元の選択によらずに定まる項をつくる。
$"take" x: T. t$ という項として $x$ によらずに $t$ を定める項を導入する。
具体的には、 $t: A$ のとき
- $exists x: T$
- 任意の $t_1: T, t_2: T$ に対して $t[x := t_1] = t[x := t_2]$
が示せるなら、 $A$ の項として扱う。 
  - 任意の、ということについては自由な変数のもとで示せればよい。
$exists$ については具体的な項の存在を要求すればいいが、
$m[x := t_1] = m[x := t_2]$ を必要とする以上、equality が定義されている必要がある。

#definition[
  #bnf(
    Prod(
      annot: "Term",
      $t$,
      {
        Or[$s in S$][_kind_]
        Or[$x$][$x in cal(V)$, _variable_]
        Or[$lambda x: t. t$][$x in cal(V)$, _lambda abstraction_]
        Or[$Pi x: t. t$][$x in cal(V)$, _dependent product type_]
        Or[$t$ $t$][_application_]
        Or[$"Proof" t$][_proof of t_]
        Or[$"take" x:t. t$][$x in cal(V)$, _choice_]
      },
    ),
  )
]

judgement は変えない。
reduction として $"take" x: T. m -> m[x := y]$ がほしいように思ったけど、
証明が複雑になりそうなので、 $=$ で対応している。
strong normalization は壊れそうだけど、 $=$ のもとで normal form があればうれしい。

#definition[
- take の導入
  $ #proof-tree(rule(
    $Gamma tack ("take" x:T. m): M$,
    $Gamma tack T: s$,
    $Gamma :: x: T tack m: M$,
    $Gamma tack e: T$,
    $Gamma tack.double Pi x:T. Pi y: T. m =_M m[x := y]$
  )) $
- take を使わない形に
  $ #proof-tree(rule(
    $Gamma tack ("take" x: T. m) = m[x := t]$,
    $Gamma tack ("take" x: T. m): M$,
    $Gamma tack t: M$,
  )) $
]

= power type を導入する。
*いろいろ読んでたら、 Power Set は鬼門の気がしてきた。*

$A: TT$ に対してべき集合 $cal(P)(A): TT$ を導入する。
これで ${A': cal(P)(A) | ... }$ とかが書けるようになって商集合を扱えそう。
当然、 ${x: A | P}: cal(P)(A)$ である。
#definition[
  #bnf(
    Prod(
      annot: "Term",
      $t$,
      {
        Or[$s in S$][_kind_]
        Or[$x$][$x in cal(V)$, _variable_]
        Or[$lambda x: t. t$][$x in cal(V)$, _lambda abstraction_]
        Or[$Pi x: t. t$][$x in cal(V)$, _dependent product type_]
        Or[$t$ $t$][_application_]
        Or[$"Proof" t$][_proof of t_]
        Or[$"take" x:t. t$][$x in cal(V)$, _choice_]
        Or[$cal(P)(t)$][_power type_]
      },
    ),
  )
]

#definition[
  - power type の導入
    $ #proof-tree(rule(
      $Gamma tack cal(P) (A): TT$,
      $Gamma tack A: TT$,
    )) $
  - subset を含むようにする1
    $ #proof-tree(rule(
      $Gamma tack A: cal(P) (A)$,
      $Gamma tack A: TT$,
    )) $
  - subset を含むようにする2
    $ #proof-tree(rule(
      $Gamma tack {x: A | P} : cal(P) (A)$,
      $Gamma tack {x: A | P}: TT$,
    )) $
]

これで型付けの一意性がまた壊れた。
よくないがまあ仕方ない。
今思ったんだけど、 $Gamma:: x: A tack.double P$ なら $P$ は常に true になっているので、 $A = {x: A | P}$ としてもいい気がする。

== 商集合が扱えないという話。
$A: TT$ と $R: A -> A -> PP$ があって、 $R$ が同値関係を与えているとする。
$a: A$ に対して $[a]_(A \/ R) := {x: A | x R a}$ とする。
これは $a$ の同値類全体になる。
ただ、ここから素直に商集合を記述できないことがわかった。

== 問題
よく考えたら、 $exists a: A. P$ 自体は $exists a: {a: A. P}$ として書ける。
なので、 $exists a: A$ のようなものだけ書ければいい。
（でも $exists$ はよくわからないがやばいらしい。）

1. なんらかの方法で $exists$ を使う場合、 ${B: cal(P)(A) | exists a: {a: A, B = [a]_(A \/ R)} }$ と書けるが、これは $exists$ をつかっているので気を付けないとやばい。
  - $f: A -> Y$ が $R$ を保つとき、 $tilde(f)$ が次のようにして記述できそうに思える。
  - $tilde(f) = lambda B: {B: cal(P)(A) | exists a: {a: A | B = [a]_(A \/ R)} }. "take" x: {x: A | B = [x]_(A \/ R)}. f x$
  - でもこの記述は示せない。
    - take ができる具体的な項はない ... つまり、 $A: ?, R: ?, f:?, B:?} tack e: {x: A | B = [x]_(A \/ R)}$ となる項 $e$ がない。
      - ただし、 $exists$ を $tack.double$ とするならいい。
    - $x_0, x_1: {x: A | B = [x]_(A \/ R)}$ のとき $R x_0 x_1$ を示す必要があるが、 $[x_0]_(A \/ R) = [x_1]_(A \/ R)$ が言えてもそこから $R x_0 x_1$ が言えない。
  - 問題点としては、次のものがある
    - $exists a: A$ を使うことになる
    - $a: B, B = {x: A | P}$ でも $P(a)$ が言えない
2. $B: cal(P)(A)$ に対して、次の性質を考える。
  - 性質 ($P$):
    - $B$ が $R$ で閉じる... $Pi x: B. Pi y: B. R x y$
    - $B$ が空でない... $exists b: B$
    - $B$ が同値なものを全部含む ... $\"y in B\"$ が表現できたとして $Pi x: B. Pi y: A. Pi p: R x y. \"y in B\"$
  - これなら ${B: cal(P)(A) | P(B)}$ が商集合になっている。
  - $tilde(f) = lambda B: {B: cal(P)(A) | P(B)}. "take" a: B. f a$
    - $B$ が空でないを使う。
    - $R$ で閉じることから well-def になる
    - 同値なものを全部含むが使えないように思えるけど、 $[a]_(A \/ R): {B: cal(P)(A) | P(B)}$ を示すのに使いそう。
      - TODO これを確かめる。
  - 問題点としては、次のものがある
    - 結局 $exists$ を使う
    - $\"y in B\"$ を表現する必要がある。

考えたこと
- subset から型を作る？
  $ #proof-tree(rule(
    $Gamma tack x: A$,
    $Gamma tack x: B$,
    $Gamma tack B: cal(P)(A)$,
  )) $<think1>
- subset の equal から predicate を取り出す？（ extensional な体系と似てる）
  $ #proof-tree(rule(
    $Gamma tack.double P[x := a]$,
    $Gamma tack a: B$,
    $Gamma tack.double B =^(cal(P)(A)) {x: A | P}$,
  )) $
- $exists$ を導入して、 take も変える。
  $ #proof-tree(rule(
    $Gamma tack.double exists x: T$,
    $Gamma tack t: T$,
  )) $
  $ #proof-tree(rule(
    $Gamma tack ("take" x: T. m): M$,
    $Gamma tack M: s$,
    $Gamma, x: T tack m: M$,
    $Gamma tack.double exists x: T$,
    $Gamma tack.double Pi y: T. Pi z: T. m[x := y] =^M m[x := z]$,
  )) $

これで商集合が記述できた。

= non structural recursion を楽に記述する
division を計算するのに euclidean algorithm（ユークリッド互除法）があるが、
これは coq では楽に書けない。
まあ、停止性を証明しないといけないのはそうだけど、
証明項とかの帰納法を回す必要があってめんどくさい。

== rec について
型をあまり考えずにやってみる。
#definition[
  #bnf(
    Prod(
      annot: "Term",
      $t$,
      {
        Or[$...$][]
        Or[$"rec" x x = M$][_recursion_]
      },
    ),
  )
]

rec の reduction は単に次のようになる。
$
  "rec" f x = M ->^beta lambda x. (M[f := ("rec" f x = M)])
$
これを用いると、ユークリッド互除法は次のように書ける。
ただし、 $NN$ や $"bool"$ という型や、 $<=$: $NN times NN -> "bool"$ はいいとする。
$
  "rec" f (x: NN times NN) = \
    &"if" x.0 <= x.1  "then" f (x.1, x.0) "else" \
    &"if" x.0 div x.1 == 0 "then" x.1 "else" f (x.1, x.0 div x.1) \
$

型付きとして簡単にやるなら次のようになる。
$
#proof-tree(rule(
  $Gamma tack "rec" f x = M: T -> T'$,
  $Gamma, f: T -> T', x: T tack M: T'$
))
$

== このままだとまずい理由
定理証明系としては、consistency が保たれている（ $Gamma tack t: (forall P: PP. P)$ となる項 $t$ がない）必要があるが、
これを使うと $t$ ができてしまうのでだめ。
全ての rec がまずいのではなくて、無制限の rec がまずい。
呼び出されるごとに引数が減ることがわかっていたり、構造帰納法の形になるなら大丈夫。

例えば自然数を考える。
足し算の定義は次のように書ける。
```
rec add ((n, m): NN times NN) =
  match n with
  | Z => m
  | S n' => add n' (S m)
```
これを受け入れていいのは、実はこれは自然数の帰納法に似ているから。
つまり、
- `P = N -> (N -> N)` とする
- `P 0` の元として `m |-> m` がある。
- `P n -> P S n` の元として `m |-> S m` がある。
- 2 つを組み合わせれば `P n` が任意のところでできる。

この場合、実は fix を生で使っているというより、自然数から生成される elim と comp 規則を与える項を用いた形に変換していると思える。
elim は次のようになっている。
$ #proof-tree(rule(
  $Gamma tack "elim"_NN (x_Z, x_S, n): T[x := n]$,
  $Gamma, x: NN tack T: "Type"$,
  $Gamma tack x_Z: T[x := 0]$,
  $Gamma tack x_S: T[x := n] -> T[x := S n]$,
)) $
elim の変換は次のように書ける。
$
  &"elim"_NN (x_Z, x_S, 0) -> x_Z \
  &"elim"_NN (x_Z, x_S, S n) -> x_S ("elim"_NN (x_Z, x_S, n))
$

add の場合は、 `add = n |-> m |-> elim (m, x |-> S x, n)` と書けて、例えば次のように遷移が進む。
$
&"add" S(Z) m = "elim" (m, x |-> S x, S(Z)) \
&-> (x |-> S(x)) @ ("elim"(m, x |-> S(x), Z)) \
&-> S ("elim"(m, x |-> S(x), Z)) \
&-> S m 
$

だから、 fix というよりは、実際にはこういう項に変換されているようなものだと思える。

== 定理証明で書こうとすると
ユークリッド互除法に戻る。
$x = (n, m)$ みたいに書いておく。
```
rec f n m = \
    if n <= m  then f m n else \
      let n' := n div m
      if n' == 0 then m else f m n' \
```
これは単純には帰納法をやっているわけではないので、受け入れることができる形をしていない。
しかし、停止するはずなので、この項自体は定理証明にいれても大丈夫なはず。

これがなぜ停止するのかというと、直感的には、
- $n <= m$ の場合は $n > m$ に帰着させる。
- $n > m$ の場合は、 $f$ の呼び出しごとに $n + m$ が小さくなるので、停止する。
からになる。

=== 方法1
$n > m$ に限ってまず $n + m$ に関する帰納法が使えるような形にしたい。
直感的には、次のような形で定義する。
（ coq で通るわけではないが。）

```
fix euc'1: (n: N) -> (m: N) -> (p1: n > m) -> (l: N) -> (p2: n + m <= l) -> NN :=
  match l with
  | Z => Z // n = m = 0 なのでよい。
  | S l' =>
    let n': NN := n div m in
    if n' == 0 then m else
      let p1': m > n' := ... // n div m と m の大きさについての命題から証明項ができる。
      let p2': m + n' <= l' := ... // n + m < m + (n' = n div m) より証明項ができる。
      euc' m n' p1' l' p2'

let euc'2: (n: N) -> (m: N) -> (p: n > m) -> N := euc'1 n m p (n + m) (refl_(N, n + m))

let euc: (n: N) -> (m: N) -> N :=
  match n ? m with
  | (p: n <= m) =>
    let p': m > n := ... // p からつくる
    euc'2 m n p'
  | (p: n > m) =>
    euc'2 n m p
```
本質的には `l` についての帰納法になっている。

=== 方法2
この構成以外にも、 well-founded に対応するような型を定義して、そっちの帰納法でまわすのもできる。
```
// 計算が停止できる引数の定義
inductive A: (x: NN times NN) -> Type :=
  | A1: (n: N) -> (m: N) -> (n <= m) -> A m n -> A n m
  | A2: (n: N) -> (m: N) -> (n > m) -> (n div m == 0) -> A n m
  | A3: (n: N) -> (m: N) -> (n > m) -> (n div m != 0) -> A m (n div m) -> A n m

// 計算が停止する証拠に関する帰納法
let euc' = fix euc: (n: N) -> (m: N) -> (p: A n m) -> N :=
  match p with
  | A1 _ _ (_: n <= m) (t: A m n) => euc m n t
  | A2 _ _ (_: n > m) _ => m
  | A3 _ _ (_: n > m) _ (t: A m (n div m)) => euc m (n div m) t 

// 全ての引数で停止する証明
let totality: (n: N) -> (m: N) -> A n m := ...
  // ここで結局 n + m <= l を使って l に関しての帰納法で定義する

let euc: (n: N) -> (m: N) -> N := euc' n m (totality n m)
```

=== 問題
coq ではこういうのは微妙にまずくて、
`Prop` に入っている型は、それの帰納法を使って計算ができない。
なので、 `Type` につくって代わりにするなどが必要（だったはず）。

あと、ともに `euc` 自体は関数の外延性が成り立つが、そのなかで定義している補助的な関数では外延性が成り立たない。

=== こっちの体系では...
ある意味では、それに依存しないという意味で、 `n + m <= l` を使うのは take の仕様の目的に合致している気がする。
問題は、 take では reduction がやれないこと。
（無理にやろうとすると多分大変な気がする。）
こっちの体系で書こうとするとこんな感じ？
（ただし、 `a: {x: T | P}` を書くのがめんどくさいと適当に s.t. を使う。）
```
// 結局 l' をとらないと euc' は書けない！（停止性の証明）
rec euc' (n: N) (m: N s.t. n > m) (l: N s.t. n + m <= l) :=
  match l with
  | Z => Z
  | S l' =>
    let n' := n div m
    if n' == 0 then m else euc' m n' l'

// ここは"本質的に l によらない"だけを示しているようなもの
let euc: (n: N) -> (m: N) -> N := take (l: N s.t. n + m <= l). euc' n m l
```

== アイディア
計算と記述をわけることで、
「記述の側で take や構造帰納法などを使って停止することが証明できるなら、それに対応する計算側の項を認めてよい。」
とすることができそうだ。
この場合、記述の方では構造帰納法以外の recursion を認めないほうが、多分うまくいきそう。

この場合、 sort を増やして Prop, Set, Comp のようにわける。

- $cal(S) = \{*^p, *^s, *^c, square\}$
- $cal(A)= {(*^p: square), (*^s, square)}$
- $cal(R) =$
  - ${(*^p, *^p), (*^p, square), (square, *^p), (square, square)}$
  - ${(*^s, *^s), (*^s, square), (*^s, *^p)}$

この上で、 $*^c$ から $*^s$ への reflection を行う。
具体的には、
項を $::= .. | "Rf" t$ のように拡張し、
$"Rf" t$ の変換を次のように行う
- $"Rf" *^c -> *^s$
- $"Rf" (lambda x:T. t) -> lambda x: ("Rf" T). ("Rf" t)$
- $Pi$ や app なども同じ
- $"Rf" m ->^beta "Rf" m'$ if $m ->^beta m'$

また、帰納的な型として $*^c$ 側に定義されたものは、
その reflection に対応する型を自動的に $*^s$ につくり、 $"Rf"$ といい感じになるようにつくる。
例えば自然数の場合、
- type form ... $NN$: $*^c$ ::=
  - type intro Z ... $Z$: $NN$
  - type intro S ... $S$: $NN -> NN$
と書くと
- elim rule ... $"elim"_NN$
- computation rule ...
が勝手に出てくるが、

これにさらに $*^s$ 側で対応する $hat(NN), hat(Z), hat(S), hat("elim"_NN)$ を導入する。
そして、 $"Rf" NN = hat(NN)$ などのように変換規則を拡張する。

"rec" 付きの項を "Rf" で "rec" のない世界 $*^s$ 側で表現できているのであれば、
"rec" が付いていても止まりそう（な気がする）。

$#proof-tree(rule(
  $Gamma tack ("rec" f x := M): Pi x: T. M' $,
  $...$,
  $Gamma tack.double Pi x: ("Rf" T). (("Rf" ("rec" f x := M) x) =_T t x)$,
))$

とりあえず考えただけなので、整合性があるかは不明。

あとで帰納型を含めてちゃんと考える。
