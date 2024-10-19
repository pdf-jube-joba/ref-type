#import "@preview/ctheorems:1.1.2": *
#import "@preview/simplebnf:0.1.1": *
#import "@preview/curryst:0.3.0": rule, proof-tree

#set heading(numbering: "1.1.")

#let definition = thmbox("definition", "Definition", fill: rgb("#eeffee"))

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

= notation
変数に使う集合は $cal(V)$ とかにしておく。

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
    $Gamma tack Pi x: t. T$,
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
    $T_1 equiv^beta T_2$,
  )) $
]

== stratified な場合
項を一気に定義するのではなく、
証明項、命題、型、などを階層化して定義することができるようだが。

// TODO

== 矛盾しないようにするために注意すること
以下はやらないようにする。
- type: type みたいなこと
- prop のほかに impredicative な sort を追加する
- strong dependent sum
- large elimination

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
    $Gamma tack Pi x: t. T$,
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
    $T_1 equiv^beta T_2$,
  )) $
- assumption の追加
  $ #proof-tree(rule(
    $tack Gamma :: t$,
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
    $Gamma tack P: Pi (\_: A). PP$,
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

= equality を導入して、元の選択によらずに定まる項をつくる。
$"take" x: T. t$ という項として $x$ によらずに $t$ が定まっているときに使うようのものを用意する。
具体的には、 $t: A$ のとき
- $exists x: T$
- $t_1: T, t_2: T$ に対して $t[x := t_1] = t[x := t_2]$
が示せるなら、 $A$ の項として扱う。 
$exists$ については具体的な項の存在を要求すればいいが、
equality を導入する関係上、 equality を定義しなければいけない。

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

#definition[
$a, b: "Term"$ に対して、
$a: A$, $b: A$, であったとして、
$a =_A b$ を次の略記とする。
（Leibniz の equality）
$ Pi P: (A -> PP). (P a -> P b) $
]

もしかしたら、 inductive な形で equality を導入したほうがいいかも。

judgement は変えない。
reduction として $"take" x: T. m -> m[x := y]$ がほしいように思ったけど、
証明が複雑になりそうなので、 $=$ で対応している。

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
$A: TT$ に対して $cal(P)(A): TT$ を導入する。
これで ${A': cal(P)(A) | ... }$ とかが書けるようになって商集合を扱えそう。
当然、 ${x: A | P}: cal(P)(A)$ である。
$A: TT$ と $R: A -> A -> PP$ があって、 $R$ が同値関係を与えているとする。
- $a: A$ に対して $[a]_(A \/ R) := {x: A | x R a}$ とする。
1. ${B: cal(P)(A) | exists a: A, B = [a]_(A \/ R)}$ これは $exists$ をつかっているのでやばい。
2. ${B: cal(P)(A) | }$
