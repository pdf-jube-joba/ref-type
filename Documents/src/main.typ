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

= notation
変数に使う集合は $cal(V)$ とかにしておく。
= 資料
- https://theses.hal.science/tel-02058937/document Extending higher-order logic with predicate subtyping : application to PVS
- https://era.ed.ac.uk/bitstream/handle/1842/12487/Luo1990.Pdf Extended Calculus of Constructions
- https://www.cs.cmu.edu/~kw/scans/hurkens95tlca.pdf A simplification of Girard's paradox
- https://ceur-ws.org/Vol-1525/paper-14.pdf Two set-based implementations of Quotient in type theory 

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

== stratified な場合
項を一気に定義するのではなく、
証明項、命題、型、などを階層化して定義することができるようだが。

// TODO

== 矛盾しないようにするために注意すること
以下はやらないようにする。
- type: type みたいなこと
  - 普通に sort として $s: s$ があるとだめっぽい？
  - pure type system として Prop ($*$) 以外に sort $s in S$ であって impredicative ($(s, s) in cal(R)$) となるものがあれば、矛盾するらしい。
  - system $U$ や $U^-$ など（ Girard's paradox を参照）
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

*もしかしたら、 inductive な形で equality を導入したほうがいいかも。*

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
      $Gamma tack cal(P) A: TT$,
      $Gamma tack A: TT$,
    )) $
  - subset を含むようにする1
    $ #proof-tree(rule(
      $Gamma tack A: cal(P) A$,
      $Gamma tack A: TT$,
    )) $
  - subset を含むようにする2
    $ #proof-tree(rule(
      $Gamma tack {x: A | P} : cal(P) A$,
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
1. なんらかの方法で $exists$ を使う場合、 ${B: cal(P)(A) | exists a: A, B = [a]_(A \/ R)}$ と書けるが、これは $exists$ をつかっているので気を付けないとやばい。
  - $f: A -> Y$ が $R$ を保つとき、 $tilde(f)$ が次のようにして記述できそうに思える。
  - $tilde(f) = lambda B: {B: cal(P)(A) | exists a: A, B = [a]_(A \/ R)}. "take" x: {x: A | B = [x]_(A \/ R)}. f x$
  - でもこの記述は示せない。
    - 具体的に項として $A:"hoge", R:"hoge", B:"hoge" tack e: {...}$ となる項 $e$ を取り出すことができない。
      - $exists a: A, B = [a]_(A \/ R)$ から取り出せると strong dependent sum っぽい。（ $pi_1$ だけなら大丈夫だが）
      - $x: B$ で $B: cal(P)(A)$ なら $x: A$ が取り出せるなら、 $"take" x: B. f x$ に型がつく（考えたこと参照 @think1 ）が、それでも $B$ が空でないことはめんどくさい。
    - $x_0, x_1: {x: A | B = [x]_(A \/ R)}$ のとき $R x_0 x_1$ を示す必要があるが、 $[x_0]_(A \/ R) = [x_1]_(A \/ R)$ が言えてもそこから $R x_0 x_1$ が言えない。
  - 問題点としては、次のものがある
    - $exists a: A. P$ を使うことになる
    - $a: B, B = {x: A | P}$ でも $P(a)$ が言えない
2. $B: cal(P)(A)$ に対して、次の性質を考える。
  - 性質 ($P$):
    - $B$ が $R$ で閉じる: $Pi x: B. Pi y: B. R x y$
    - $B$ が空でない: $exists b: B$
    - $B$ が同値なものを全部含む $\"y in B\"$ が表現できたとして $Pi x: B. Pi y: A. Pi p: R x y. \"y in B\"$
  - これなら ${B: cal(P)(A) | P(B)}$ が商集合になっている。
  - $tilde(f) = lambda B: {B: cal(P)(A) | P(B)}. "take" a: B. f a$
    - $B$ が空でないを使う。
    - $R$ で閉じることから well-def になる
    - 同値なものを全部含むが使えないように思えるけど、 $[a]_(A \/ R): {B cal(P)(A) | P(B)}$ を示すのに使いそう。
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
