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
        Or[$s in S$][_proposition_]
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
- context を使う
  $ #proof-tree(rule(
    $Gamma tack x: t$,
    $(x : t) in Gamma$
  )) $
]

// TODO

== stratified な場合


= 証明と証明項を抽象化する
#definition[
  #bnf(
    Prod(
      annot: "Term",
      $t$,
      {
        Or[$s in S$][_proposition_]
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