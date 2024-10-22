#import "@preview/ctheorems:1.1.2": *
#import "@preview/simplebnf:0.1.1": *
#import "@preview/curryst:0.3.0": rule, proof-tree

#set heading(numbering: "1.1.")

#let definition = thmbox("definition", "Definition", fill: rgb("#eeffee"))
#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffff"))
#let proof = thmproof("proof", "Proof")
#let WIP = square(size: 10pt, fill: rgb("#e81616"))

#show: thmrules.with(qed-symbol: $square$)

= logical な consistency について
定義を思い出すと、
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

この体系で示したいのは consistency と呼ばれる次の定理である。
#theorem[
  どんな項 $t$ についても、 $tack t: (Pi x:PP. x)$ が成り立たない。
]
ここで $Pi x:PP. x$ は論理だと $bot$ に対応する項になっている。
なので、仮定なしに矛盾しない体系であることを言っている。

= lemmas
#theorem[
  合流性がある。
]<confluence>
多分ある。

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

- context $Gamma$ に対して、 $"Hold" t$ の部分を $Gamma$ のそれまでに登場していない変数に置き換える。
- $Gamma tack.double t$ のコンテキストの含まれる導出木を見て上と下をくっつける。
をやることで、項の定義は変わらずコンテキストから Hold のみが抜けた次のような体系であると思える。

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
- 証明項を作る
  $ #proof-tree(rule(
    $Gamma tack "Proof" t: t$,
    $Gamma tack t': t$,
    $Gamma tack t: PP$,
  )) $
]

実際、もとの体系の導出木に対して次をやれば得られる。
- 「assumption の追加」 は 「context をのばす」に対応させる。
  $ #proof-tree(rule(
    $tack Gamma :: "Hold" t$,
    $tack Gamma$,
    $Gamma tack t: PP$,
  )) ==> #proof-tree(rule(
    $tack Gamma :: (x: t)$,
    $tack Gamma$,
    $Gamma tack t: s$,
    $x in.not Gamma$,
    $s in S$,
  )) $
- 「項の使用」と「証明項を作る」の導出木は連結する。
   $ #proof-tree(rule(
      $Gamma tack "Proof" t: t$,
      rule(
        $Gamma tack.double t$,
        $Gamma tack p: t$,
        $Gamma tack t: P$,
      ),
   )) ==> #proof-tree(rule(
      $Gamma tack "Proof" t: t$,
      $Gamma tack p: t$,
      $Gamma tack t: P$,
    ))
  $
- 「assumption の使用」と「証明項を作る」の導出木は連結し、さらに上に変数を登場させる。
  $ #proof-tree(rule(
      $Gamma tack "Proof" t: t$,
      rule(
        $Gamma tack.double t$,
        $"Hold" t in Gamma$,
      ),
   )) ==> #proof-tree(rule(
      $Gamma tack "Proof" t: t$,
      rule(
        $Gamma tack x: t$,
        $x: t in Gamma$,
      ),
        $Gamma tack t: PP$,
    ))
  $

#theorem[
  $Gamma tack t: PP$ なら $t equiv^beta s$ ではない。
]
TODO これがほしい。

ここで、コンテキストで型のつく項について、 "sort" のようなものを考えると、
項の階層をわけることができる。
（これが pure type system から通常の stratified な定義への変換ができる根拠のはず。）
特に、型として現れる項は $"Proof" t$ を含まない。

#theorem[
- $Gamma tack t: T$ なら $T$ は部分項に $"Proof" m$ を含まない。
- $Gamma tack T: s$ なら $T$ は部分項に $"Proof" m$ を含まない。
- $tack Gamma$ なら $(x: t) in Gamma$ に対して $t$ は部分項に $"Proof" m$ を含まない。
]

#proof[
証明の順序としては、自然数 $n$ についての次の命題を考えて、 $n$ の帰納法で示す。
- (A) 任意の $Gamma$, $t$, $T$ 及び （$Gamma tack t: T$ の導出木であって長さが $n$ 以下のもの）については次が成り立つ。
  1. $T$ は部分項に $"Proof" \_$ を含まない。
  2. $T equiv^beta s$ なら $t$ は部分項に $"Proof" \_$ を含まない。
  3. $Gamma$ の $x: T in Gamma$ に対して $T$ は部分項に $"Proof" \_$ を含まない。
- (B) 任意の $Gamma$ と $tack Gamma$ の導出木であって長さが $n$ 以下のものについて
  4. $Gamma$ の $x: T in Gamma$ に対して $T$ は部分項に $"Proof" \_$ を含まない。


$n = 1$ なら明らかに成り立つ。
$n = k$ で成り立つとして $n = k + 1$ に対して $Gamma, t, T$ とその導出木をとってきて、導出木の最後をみて命題を示す。
- empty context の場合、 (B) を示す必要があるがこれは確かにそう。
- context をのばす場合、 $Gamma = Gamma' :: x: t$ として (B) を示す必要があるが、
  - $tack Gamma'$ よりここに含まれているやつは成り立つ
  - $t$ については $Gamma' tack t: s$ より仮定から成り立つ。
- variable を使う場合、 (A) を示す必要がある
  1. については $tack Gamma$ より $t$ は "proof" なし
  2. については $t = x$ なので成り立つ。
  3. については $tack Gamma$ より。
- axiom を使う場合、 1. と 2. はよくて、 3. については $tack Gamma$ より。
- dependent product type の導入の場合：
  1. $s_2$ は部分項に含まない
  2. $t$ は "proof" なしなのが $Gamma tack t: s_1$ からいえて、 $T$ も "proof" なしなのが $Gamma :: x: t tack T: s_2$ からいえるので、 $Pi x:t. T$ もそう。
  3. $Gamma tack t: s_1$ から $Gamma$ についていえる。
- dependent product の intro:
  1. $Gamma tack (Pi x: t.M): s$ より。
  2. 合流性 @confluence から、 $Pi x:t. M equiv^beta s_2$ が成り立たない。
  3. $Gamma tack (Pi x: t. M): s$ より。
- application: TODO 一番の鬼門 #WIP
  1. 
  2. 
  3.
- $beta$ reduction: 1.2.3 それぞれ、 $Gamma t: T_1$ からいえる。
- 証明項を作る:
  1. $Gamma tack t: PP$ より $t$ は "Proof" なし
  2. $Gamma tack t: PP$ より、 $t equiv^beta s$ なら矛盾するはず TODO
  3. $Gamma tack t': t$ より。

本当に成り立つのか怪しくなってきた。
]

結局本当にやりたいことは多分次が成り立つだろうということ
#theorem[
もともとの CoC の項やコンテキストに対してこれを CoC+Proof の項やコンテキストとみなすことができるが、
  この操作を $Gamma |-> overline(Gamma), t |-> overline(t)$ と書く。
- $overline(Gamma) tack_("CoC + Proof") overline(t): overline(t')$ なら $Gamma tack_("CoC") t: t'$ が成り立つ。
- $overline(Gamma) tack_("CoC + Proof") t: overline(t')$ ならある項 $underline(t)$ が存在して $Gamma tack_("Coc") underline(t): t'$
]

これが示せれば、
