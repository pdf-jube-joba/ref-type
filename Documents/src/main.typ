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

// == 矛盾しないようにするために注意すること
// 以下はやらないようにする。
// - type: type みたいなこと
//   - 普通に sort として $s: s$ があるとだめっぽい？
//   - pure type system として Prop ($*$) 以外に sort $s in S$ であって impredicative ($(s, s) in cal(R)$) となるものがあれば、矛盾するらしい。
//     - これは理解を間違えている気がする。多分、 $(square, s) in cal(R)$ があるとまずい。
//   - system $U$ や $U^-$ など（ Girard's paradox を参照）
//     - これは循環な体系ではない（ $lambda_("HOL")$ の拡張になっている）がだめらしい。
- strong dependent sum っぽいことができるとまずい
 
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

== equality を使う
$A =_(*^s) B -> A -> B$ があるとうれしいが、これを refl でやるには elim についての large elimination に気を付ける必要がある。

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

$exists$ はそもそも入れていいと思う。

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

== さらにいろいろ付け加える
べき集合と部分集合を加えたので、位相空間論とかができるかと思ったが、
それをやるためには $O_1: cal(P)(X), O_2: cal(P)(X)$ に対して $O_1 sect O_2$ が記述できないのでつらい。
やりたいのは
- $sect_lambda O_lambda$ や $union_lambda O_lambda$ に対する reasonable な解釈
- 型レベルではなくても、 $x: X$ と $O: cal(P)(X)$ に対して $x in O$ を表すような述語をつくる

これをやるためには、 $O: cal(P)(X)$ に対して、「$O$ に含まれるための述語を取り出す」必要がある。
これを加える。
term を $"Pred"_t t$ と拡張し、
$"Pred"_(A') {x: A | P} equiv lambda x: A. P$ とする。

型システムに追加するのは、
- $tack B: cal(P)(X)$ なら $"Pred"_X B: X -> *_p$
  - $"Pred"$ 自体は $((X: *_s) -> (B: cal(P)(X)) -> *_p): *_p$ みたいになっている。
    - これってけっこうまずい気がする（ strong impredicative sum みたいな）
    - $(*^s, *^p) in cal(R)$ でないからいいか？
- $tack B: cal(P)(X)$, $tack t: B$ なら $tack.double ("Pred"_X B) t$

これで $O_1 sect O_2 := {x: X | "Pred"_X O_1 x and "Pred"_X O_2 x}$ と書ける。
また、 $x: O_1 sect O_2$ なら $x: O_1$ になる？ ... ならないが、 $"Pred"_X O_1 x$ は示せる。

- $tack B: cal(P)(X)$ なら $B: *^s$ がほしい。
- $B equiv^beta { x: X | "Pred"_X B }$ が成り立てば、 上の問題で $ x: O_1$ が示せる。

== 注意点
位相空間論はできるようになってる。
ただし、 $*^s$ が predicative かどうかで位相空間がどこに入るかを考える必要がある。
また、 $x: X$ と $A: cal(P)(X)$ に対して、 $tack t: A$ と $tack.double ("Pred"_X A) t$ では後者の方が弱い。
そこにも気を付ける必要がある。
- $"sect" := (X: *^s) -> (O: cal(P)(cal(P)(X))) -> (X_1: O) -> (X_2: O) -> {x: X | ("Pred"_X X_1) x and ("Pred"_X X_2) x}$
- $"powerset_fin_sect_closed1" := (X: *^s) -> (O: cal(P)(cal(P)(X))) -> (X_1: O) -> (X_2: O) -> "Pred"_(cal(P)(X)) O ("sect" X O X_1 X_2)$
- $"powerset_fin_sect_closed2" := (X: *^s) -> (O: cal(P)(cal(P)(X))) -> (X_1: cal(P)(X)) -> (X_2: cal(P)(X)) -> (x: X) -> ("Pred"_X X_1) x -> ("Pred"_X X_2) x -> "Pred"_(cal(P)(X)) O ("sect" X O X_1 X_2)$

- $"union" := (X: *^s) -> (O: cal(P)(cal(P)(X))) -> (Lambda: *^s) -> (o: Lambda -> O) -> {x: X | exists lambda: {lambda: Lambda | "Pred"_X (o lambda) x}}$
- $"powerset_union_closed1" := (X: *^s) -> (O: cal(P)(cal(P)(X))) -> (Lambda: *^s) -> (o: Lambda -> O) -> "Pred"_(cal(P)(X)) O ("union" X O Lambda o)$

closed がついているのは $*^p$ の項になる ($*^p$ の impredicativity ... $*^s: square$ で $(square, *^p, *^p)$ より)。

なので、 $"is_topology" (X: *^s) (O: cal(P)(cal(P)(X))): *^p$ という述語が作れる。
ただし、 topological space を帰納型というか record 型というかそんな感じのやつにしたいなら、
それは $*^s$ ではなくて $square$ に住むことになる。
そのため、 $square$ を predicative な形で階層を付ける必要がある。
（ sum 型が predicative になるために制限があるような感じ）

この場合には、 propositional equality では $t_1, t_2: {x: A | P}$ に対して $t_1 =_A t_2 => t_1 =_{x: A | P} t_2$ ができていたものを、
再び $square$ のレベルで似たような equality が示せないと使いにくい。
具体的には、位相空間の compactness が定義されていたとき、 $2$ つの位相空間の等しさの判定時に、 compactness の証明まで要求されるようになってしまう。
だけど、構造の $=$ を要求することは少ないはず？
どちらかといえば同型が登場するので良い。
また compactness などの"構造に対する性質"については、 topology の定義を "expand" して、prop を与えることでも得られる。
こういうのをうまくやる仕組みがあればいい？

== 集合論との比較
集合との比較でいえば、次のものは入れてもよい。
- $A: cal(P)(A)$
- $B: cal(P)(A)$, $C: cal(P)(B)$ $=>$ $C: cal(P)(A)$
- $B: cal(P)(A)$ $=>$ $cal(P)(B): cal(P)(cal(P)(A))$
- $Gamma tack.double P$ $=>$ $A equiv {x: A | P}$
ただ、これがなくても十分に使えそうにはなっている。
例えば次が成り立つ。
- $B: cal(P)(A)$, $C: cal(P)(B)$, $t: C$ なら $t: A$ である。
- $t: A$ かつ $Gamma tack.double P$ なら $t: {x: A | P}$
なので、"項"に対する型としては十分である。

= equality と take について
equality についてできてほしいのは次のようなこと
- $a =_A a$
- $a =_A b => b =_A a$
- $a =_A b => b =_A c => a =_A c$
- $a =_B b => B: cal(P)(A) => a =_A b$
- $a, b: A => B: cal(P)(A) => a =_A b => a =_B b$
- $a =_A b => (P: A -> s) => P a => P b$
最後のが Leibniz equality で、 $a =_A b$ をこれで定義してもよい。

- ここで、 $A: *^s$ を課したほうがいいのか？
- Leibniz equality は、 $P: A -> s$ に対して、 $s = *^p$ しか考えなくていいか？
  - 例えば、 $x: A$ で添え字づけられたような集合 $B(x)$ があるとき、 $x =_A y => B(x) => B(y)$ が作れると明らかに便利

$A: *^s, R: A -> A -> *^p, a: A$ に対して、 $[a]_(A \/ R) := {x: A | R x a}$ と書くことができる。
$[a_0] = [a_1]$ から $R a_0 a_1$ を取り出したい。
- $X_1 subset_X X_2 := (x: X_1) -> "Pred"(X, X_2) x$
- $B_0 =_(cal(P)(A)) B_1 => B_0 subset_A B_0 => B_0 subset_A B_1$ が作れそう
- $[a_0] =_(cal(P)(A)) [a_1] => t: [a_0] => "Pred"(A, [a_1]) t$ も作れそう
- $a_0: [a_0]$ なら $R a_0 a_1$ が示せる！

== Leibniz equality
- $"eq" (A: *^s) (x: A) (y: A)$ := $(P: A -> *^p) -> P x -> P y$ ... $x =_A y$ と書く
- $"refl" (A: *^s) (x: A)$: $"eq" A x x$ := $(P: A -> *^s) |-> (p: P x) |-> p$
になっている。

- $a =_B b, B: cal(P)(A) => a =_A b$ について
  - $Gamma tack p: (P: B -> *^p) -> P a -> P b$ とする
  - $Gamma tack M: (P: A -> *^p) -> P a -> P b$ なる項をつくりたい。
  - $M = (P: A -> *^p) |-> (t: P a) |-> M'$ としておく。
  - $M' = p P t$ だとまずい... $P: A -> *^p$ を入れていて、 $P: B -> *^p$ を入れてないから
- $a: B, b: B, B: cal(P)(A), a =_A b => a =_B b$ について
  - これも同様に、 $P: A -> *^p$ と $P: B -> *^p$ に問題がある。
直感的には、述語を制限したり拡張したりできる。
しかし、その場合には $P$ ではないものができてしまう。
- $P: A -> *^p$ のとき、 $((x: B) |-> P x): (B -> *^p)$
- $P: B -> *^p$ のとき、 $((x: A) |-> "Pred"(A, B) x and P x)$ ただしこれは思うようにいかない。
  - $t: A$ が $"Pred"(A, B) t and P t$ に元を持つならそもそも $t: B$ である。
  - $t: A$ だが $t: B$ でない場合が記述できていない。

なので、 Leibniz equality では記述できていない。
あと、最後のもルールで入れておきたい。

== inductive type との比較
1. parameter を入れないなら次のようになる。
```Coq
Inductive Id: (A: Set) -> (x: A) -> (y: A) -> Prop :=
  | refl : (A: Set) -> (x: A) -> Id A x x.
```
この場合で rec を考える。
- $xi_X(Q, c, (A: *^s) -> (x: A) -> "Id" A x x) = (A: *^s) -> (x: a) -> (Q A a a (c a x))$
- $mu_X(F, f, (A: *^s) -> (x: A) -> "Id" A x x) = (A: *^s) |-> (x: a) |-> f a x$

pattern match は $"Elim" "refl" A a "return" Q | "refl" => f_1 ->^beta f_1 A a$ のように reduction が進む。
$"Rec"_"Id"(c, Q, f) = "Elim" c "return" Q | "refl" => f_1$ である。
$ #proof-tree(rule(
  $Gamma tack "Rec"_"Id"(c, Q, f): Q A x y c$,
  $Gamma tack c: "Id" A x y$,
  $Gamma tack Q: (A: *^s) -> (x: A) -> (y: A) -> "Id" A x y -> s'$,
  $Gamma tack f_1: (A: *^s) -> (a: A) -> Q A a a ("refl" A a a)$,
)) $

2. Coq としての 帰納型としては次のように paramter を入れて定義していた。
```Coq
Inductive Id (A: Set) (x: A) : A -> Prop :=
  | refl : Id A x x.
```
この場合で rec を考える。
よくわかっていないが、 parameter は context に push されているものと思った方がよさそう。
その場合、 $Gamma = A: *^s, x: A$ となった状態で次のように定義している。
```Coq
Inductive Id: A -> Prop :=
  | refl: Id x.
```
- $xi_X(Q, c, "Id" x) = Q x c$
- $mu_X(F, f, "Id" x) = f$

pattern match は $"Elim" "refl" "return" Q | "refl" => f_1 ->^beta f_1 $ のように reduction が進む。
$"Rec"_"Id"(c, Q, f)$ を同様に定義する。
$ #proof-tree(rule(
  $Gamma tack "Rec"_"Id"(c, Q, f): Q y c$,
  $Gamma tack c: "Id" y$,
  $Gamma tack Q: (y: A) -> "Id" y -> s'$,
  $Gamma tack f: Q x "refl"$,
)) $

ただ、 proposition に対しては proof の reduction が進んだところであまりうれしくない。
なので、 $"Rec"_"Id"(c, Q, f)$ に対応することができれば十分である。
あと、 singleton elimination とかを考えないなら、 elim rule は $s' in *^p$ でなければいけない。
この $2$ つを合わせると、次でよさそう。
$ #proof-tree(rule(
  $Gamma tack.double Q b$,
  $Gamma tack.double a =_A b$,
  $Gamma tack.double Q a$,
)) $

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

= bidirectional な type checking がほしい
まずもともとの CoC での type check を考える
基本的な考え方は、まず inference して、状況に合わせて check する
また、 $cal(A)$ や $cal(R)$ を関数ととらえる。
CoC の bidirectional は次のようになる。
- inference $Gamma tack t triangle T$
  - $Gamma$ と $t$ が input で $T$ が output
  - $Gamma tack x triangle T$ if $x: T in Gamma$
  - $Gamma tack (x: A) -> B triangle s_3$ if
    - $Gamma tack A triangle_"sort" s_1$
    - $Gamma, x: A tack B triangle_"sort" s_2$, $s_3 = cal(R)(s_1, s_2)$
  - $Gamma tack lambda x: T. m triangle (x: T) -> M$
    - $Gamma, x: T tack m triangle M$
  - $Gamma tack t_1 t_2 triangle B[x := t_1]$
    - $Gamma t_1 triangle_"prod" (x: A) -> B$
    - $Gamma t_2 triangle.l A$
- check $Gamma tack t triangle.l T$
  - $Gamma$ と $t, T$ が input で output は成功したかどうか
  - $Gamma tack t triangle T'$ をする
  - $T equiv T'$  を確認する
- constrained inference (sort) $Gamma tack t triangle_"sort" s$
  - $Gamma$ と $t$ が input で $s in cal(S)$ が output
  - $Gamma tack t triangle T$ をする
  - $T ->* s$ をえる
- constrained inference (prod) $Gamma tack t triangle_"prod" (x: A) -> B$
  - $Gamma$ と $t$ が input で $(x: A) -> B$ が output
  - $Gamma tack t triangle T$ をする
  - $T ->* (x: A) -> B$ をえる

== 考える必要があること
$Gamma = A: *^s, P_i: A -> *^p$ とする。
- $Gamma, x: A tack P_i x: *^p$ が成り立つ。

${x: A | P_1 x and P_2 x}$ と ${x: {x: A | P_1 x} | P_2 x}$ と二つの集合がある。

- ${x: A | P_1 x and P_2 x}$ はちゃんと型付けできる。
  $ #proof-tree(rule(
    $Gamma tack {x: A | P_1 x and P_2 x} : cal(P)(A)$,
    $Gamma tack A : *^s$,
    $Gamma, x: A tack P_1 x and P_2 x: *^p$,
  )) $
- もう一つもできる。
  $ #proof-tree(rule(
  $Gamma tack {x: {x: A | P_1 x} | P_2 x}: cal(P)({x: A | P_1 x})$,
  rule(
    $Gamma tack {x: A | P_1 x}: *^s$,
    $Gamma tack {x: A | P_1 x}: cal(P)(A)$,
  ),
  rule(
    $Gamma, x: {x: A | P_1 x} tack P_2 x: *^p$,
    $Gamma, x: {x: A | P_1 x} tack P_2: A -> *^p$,
    $Gamma, x: {x: A | P_1 x} tack x: A$,
  )
)) $
ただし、 $B: cal(P)(A)$ でも $C: cal(P)(B) => C: cal(P)(A)$ は成り立たないように作ってしまった。
（もし $B: cal(P)(A)$ を単に $B subset A$ ととらえれば、 $B subset A$, $C subset B$ なら $C subset A$ としてよいが、まだこれを考えてないわ ）
だから、 ${x: {x: A | P_1 x} | P_2 x}; cal(P)(A)$ は成り立たない（だろう）。

次が成り立つはず。
$ Gamma tack t: {x: A | P_1 x and P_2 x} <=> Gamma tack t: {x: {x: A | P_1 x} | P_2 x} $

$arrow.l.double$ については、
$ #proof-tree(rule(
  $Gamma tack t: {x: A | P_1 x and P_2 x}$,
  rule(
    $Gamma tack t: A$,
    rule(
      $Gamma tack t: {x: A | P_1 x}$,
      $Gamma tack t: {x: {x: A | P_1 x} | P_2 x}$,
    )
  ),
  rule(
    $Gamma tack.double P_1 t and P_2 t$,
    rule(
      $Gamma tack.double P_1 t$,
      rule(
        $Gamma tack t: {x: A | P_1 x}$,
        $Gamma tack t: {x: {x: A | P_1 x} | P_2 x}$,
      )
    ),
    rule(
      $Gamma tack.double P_2 t$,
      $Gamma tack t: {x: {x: A | P_1 x} | P_2 x}$,
    )
  )
)) $

$arrow.r.double$ については、
$ #proof-tree(rule(
  $Gamma tack t: {x: {x: A | P_1 x} | P_2 x}$,
  rule(
    $Gamma tack t: {x: A | P_1 x}$,
    rule(
      $Gamma tack t: A$,
      $Gamma tack t: {x: A | P_1 x and P_2 x}$,
    ),
    rule(
      $Gamma tack.double P_1 t$,
      $Gamma tack.double P_1 t and P_2 t$,
    )
  ),
  rule(
    $Gamma tack.double P_2 x$,
    $Gamma tack.double P_1 t and P_2 t$,
  )
)) $

これがめんどくさいのは、 inference して $cal(P)(A)$ だったときの扱い。
また、 $Gamma tack.double P_1 x -> P_2 x$ が示せる場合にも、ユーザーに何を指せるかがめんどくさい。
- $Gamma tack t triangle.l {x: A | P}$ を考える
  - $Gamma tack t triangle T$ をとり、 normal にする
  - $T = {x: A' | P'}$ なら、 $$

== 変える部分
inference は次のようにする。
わかんなくなった。
- $Gamma tack {x: A | P} triangle cal(P)(A)$
  - $Gamma tack A triangle.l *^s$
  - $Gamma, x: A triangle.l *^p$
- $Gamma tack cal(P)(A) triangle *^s$
  - $Gamma tack A triangle.l *^s$
- $Gamma tack "Pred"_A B triangle A -> *^p$
  - $Gamma tack A triangle.l *^s$
  - $Gamma tack B triangle_"pow" cal(P)(A')$

check は次のようにする
- $Gamma tack t triangle.l T$ について $Gamma tack T triangle_"sort" s$ をみる
- $Gamma tack t triangle T'$ について $Gamma tack T' triangle_"sort" s'$ をみる
- $s = s' eq.not *^s$ なら $T equiv T'$ をみる
- $s = s' = *^s$ の場合は次のようにする

直感的には、 $T: cal(P)(T')$ を $T subset T'$ と書くと、 $Gamma tack t: (T = T_1) subset T_2 subset ... subset T_n : *^s$ となる、一番長い列を持ってくると、 $Gamma tack t: T$ と $Gamma tack t: T'$ という $2$ が成り立つなら $T_n equiv T'_n$ が成り立っているだろう。
なのでこれをチェックした後に、 subset に順々に入れるようにすればいい。
- $T = T_1$, $T' = T'_1$ とする。
- $Gamma tack T_i triangle_"pow" cal(P)(T_(i+1))$ をできるまでやり、できなくなった最後を $T_n, T'_m$ とする。
- $T_n equiv T'_m$ を確認する。
- $Gamma tack t triangle.l T$ には $Gamma tack.double ("Pred"_(T_(i+1)) T_i) t$ を示せばいい。
- ただし、 $Gamma tack t: T'_i$ は用いていい（ユーザーに入力させる。）

constrained sort は次のようにする
- $Gamma tack t triangle T$ をとる
- $T ->* s$ なら $s$ とする
- $T ->* cal(P)(A)$ なら $*^s$ とする

constrained prod にも修正が必要
例として、 $Gamma t: T subset B subset M_1 -> M_2$ なら $Gamma tack t: M_1 -> M_2$ なので。
- $Gamma tack t triangle T$ をとる。
- $Gamma tack T triangle_"sort" s$ で $s eq.not *^s$ なら従来の方法 
- $Gamma tack T_i triangle_"pow" T_(i+1)$ を繰り返し、最後を $T_n$ とする。
- $T_n ->^* (x: A) -> B$ を確認する。

constrained inference に $cal(P)(A)$ を入れる
- $Gamma tack t triangle_("pow") cal(P)(A)$
- $Gamma$, $t$ が入力
  - $Gamma tack t triangle T$ をもってくる
  - $Gamma tack T triangle.l *^s$ を確認する、そうじゃない場合は失敗
  - $T ->^* cal(P)(A)$ をみる

== めんどくさい部分
$lambda x: A. x$ は $A -> A$ と infer されるが、 $A subset B$ のときに $(lambda x: A .x): (A -> B)$ を check するのがつらい。
型付け上は確かにできるのだが（$x: A tack x: B$ より）、 check と infer をする上では、ちょっと工夫が必要
というのも、 $t: A -> A$ でも $t: A -> B$ とは限らないため。
（ $t$ がラムダ中小の場合にはよい。）
これと似たような問題を解決するために cumulative を与えていたのかも？
（ $t: "Univ"(n)$ $=>$ $t: "Univ"(n + 1)$ を型規則に入れるよりも、 $"Univ"(n) <= "Univ"(n+1)$ と $B <= B'$ なら $(x: A) -> B <= (x: A) -> B'$ を入れて、 $t: U, U <= U'$ なら $t: U'$ にするなど。）
ただ今回の場合は、 cast を間に挟むことで解決できる。
つまり、 $"cast":= (x: B) -> x$ を入れてやると、 $lambda x: A. ("cast" x)$ が通るようになる。
