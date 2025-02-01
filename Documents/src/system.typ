#import "@preview/ctheorems:1.1.2": *
#import "@preview/simplebnf:0.1.1": *
#import "@preview/curryst:0.3.0": rule, proof-tree

#set heading(numbering: "1.1.")

#let definition = thmbox("definition", "Definition", fill: rgb("#eeffee"))

#show: thmrules.with(qed-symbol: $square$)

= 体系について
とりあえず全部をここに集めたやつ
- $cal(S) = {*^p, *^s, square}$
- $cal(A)= {(*^p: square), (*^s, square)}$
- $cal(R) =$
  - ${(*^p, *^p), (*^p, square), (square, *^p), (square, square)}$
  - ${(*^s, *^s), (*^s, square), (*^s, *^p)}$

#definition("項の定義")[
  #bnf(
    Prod(
      annot: "Term",
      $t$,
      {
        Or[$s in S$][_kind_]
        Or[$x$][ _variable_]
        Or[$lambda x: t. t$][_lambda abstraction_]
        Or[$Pi x: t. t$][_dependent product type_]
        Or[$t$ $t$][_application_]
      },
    ),
    Prod(
      $...$,
      {
        Or[$"Proof" t$][_proof of t_]
      }
    ),
    Prod(
      $...$,
      {
        Or[${x: t | t}$][_refinement type_]
        Or[$cal(P) (t)$][_power set_]
        Or[$"Pred"_t t$][_predicate_]
      }
    ),
    Prod(
      $...$,
      {
        Or[$t =_t t$][_equality type_]
        Or[$"relf"_t t$][_reflection_]
        Or[$"Idind" ... $][_id induction 後でやる_]
        Or[$exists t$][_existence_]
        Or[$"Take" x. t. t$][_take operator_]
      }
    )
  )
]

#definition("beta")[
- $"Idind"_A (P, "refl"_A a, )$
- $"Pred"_A {x: t | P} ->^beta lambda x: t. P$ ... $A equiv t$ のときをほぼ想定
]

#definition("judgementの定義")[
  #bnf(
    Prod(
      annot: "Context snippet",
      $gamma$,
      {
        Or[$x: t$][_declare_]
        Or[$"Hold" t$][_assumption_]
      }
    )
  )
  #bnf(
    Prod(
      annot: "Context",
      $Gamma$,
      {
        Or[$emptyset$][_empty context_]
        Or[$Gamma, gamma$][$gamma$: Context snippet, _concat_]
      }
    )
  )
  #bnf(
    Prod(
      annot: "Judgement",
      $Gamma$,
      {
        Or[$tack Gamma$][_well formed context_]
        Or[$Gamma tack t: t$][_typing_]
        Or[$Gamma tack.double t$][_provable_]
      }
    )
  )
]

#definition("CoC部分")[
- empty context の well found
  $ #proof-tree(rule(
    $tack emptyset$
  )) $
- context をのばす
  $ #proof-tree(rule(
    $tack Gamma, (x: t)$,
    $tack Gamma$,
    $Gamma tack t: s$,
    $x in.not Gamma$,
    $s in S$,
  )) $
- weak
  $ #proof-tree(rule(
    $Gamma, gamma tack t_1: t_2$,
    $Gamma tack t_1: t_2$
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
    $Gamma tack (Pi x: t. T): s_2$,
    $Gamma tack t: s_1$,
    $Gamma, x: t tack T: s_2$,
    $(s_1, s_2) in R$,
  )) $
- dependent product の intro
  $ #proof-tree(rule(
    $Gamma tack (lambda x: t. m): (Pi x:t. M)$,
    $Gamma tack (Pi x:t. M): s$,
    $Gamma, x: t tack m: M$,
    $s in S$,
  )) $
- application 
  $ #proof-tree(rule(
    $Gamma tack f a: T[x := a]$,
    $Gamma tack f: (Pi x:t. T)$,
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

#definition("proof term 部分")[
- assumption の追加
  $ #proof-tree(rule(
    $tack Gamma :: "Hold" t$,
    $tack Gamma$,
    $Gamma tack t: *^p$,
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
    $Gamma tack t: *^p$,
   )) $
- 証明項を作る
  $ #proof-tree(rule(
    $Gamma tack "Proof" t: t$,
    $Gamma tack.double t$
  )) $
]

#definition("set 部分")[
- power set form
  $ #proof-tree(rule(
    $Gamma tack cal(P)(A): *^s$,
    $Gamma tack A: *^s$,
  )) $
- power set weak
  $ #proof-tree(rule(
    $Gamma tack B: *^s$,
    $Gamma tack B: cal(P)(A)$,
  )) $
- subset form
  $ #proof-tree(rule(
    $Gamma tack {x: A | P}: cal(P)(A)$,
    $Gamma tack A: *^s$,
    $Gamma, x: A tack P: *^p$,
  )) $
- predicate form
  $ #proof-tree(rule(
    $Gamma tack "Pred"_A B : A -> *^p$,
    $Gamma tack A: *^s$,
    $Gamma tack B: cal(P)(A)$,
  )) $
- subset intro
  $ #proof-tree(rule(
    $Gamma tack t: B$,
    $Gamma tack B: cal(P)(A)$,
    $Gamma tack t: A$,
    $Gamma tack.double ("Pred"_A B) t$,
  )) $
- subset elim set
  $ #proof-tree(rule(
    $Gamma tack t: A$,
    $Gamma tack B: cal(P)(A)$,
    $Gamma tack t: B$,
  )) $
- subset elim prop
  $ #proof-tree(rule(
    $Gamma tack.double ("Pred"_A B) t$,
    $Gamma tack B: cal(P)(A)$,
    $Gamma tack t: B$,
  )) $
]

#definition("Id")[
- id form
  $ #proof-tree(rule(
    $Gamma tack a =_A b: *^p$,
    $Gamma tack A: *^s$,
    $Gamma tack a: A$,
    $Gamma tack b: A$,
  )) $
- id intro
  $ #proof-tree(rule(
    $Gamma tack "refl"_A a: a =_A a$,
    $Gamma tack a =_A a: *^p$,
  )) $
- id elim
  $ #proof-tree(rule(
    $Gamma tack.double P b$,
    $Gamma tack.double a =_A b$,
    $Gamma tack P : A -> *^p$,
    $Gamma tack.double P a$,
  )) $
- id subset
  $ #proof-tree(rule(
    $Gamma tack.double a =_B b$,
    $Gamma tack.double a =_A b$,
    $Gamma tack B: cal(P)(A)$,
    $Gamma tack a: B$,
    $Gamma tack b: B$,
  )) $
- exists form
  $ #proof-tree(rule(
    $Gamma tack exists t: *^p$,
    $Gamma tack t: *^s $,
  )) $
- exist intro
  $ #proof-tree(rule(
    $Gamma tack.double exists t$,
    $Gamma tack t: *^s$,
    $Gamma tack e: t$,
  )) $
- take intro
  $ #proof-tree(rule(
    $Gamma tack ("take" x: T. t): M$,
    $Gamma tack T: *^s$,
    $Gamma, x: T tack t: M$,
    $Gamma tack M: *^s$,
    $Gamma tack.double exists T$,
    $Gamma tack.double Pi (y_1: T). Pi (y_2: T). t[x := y_1] =_M t[x := y_2]$
  )) $
- take elim
  $ #proof-tree(rule(
    $Gamma tack ("take" x: T. t) =_M t[x := e]$,
    $Gamma tack ("take" x: T. t): M$,
    $Gamma tack e: T$,
  )) $
]
