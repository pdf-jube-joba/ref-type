# このページの目的
Coq や Lean の型システムについてのメモをとっておく。

# 知りたいこと
- 何をしたら矛盾するのか
- CoC 以外の PTS とその解釈
- モデルの与え方
- 無矛盾性の証明
- どんな順番で示していけばいいのか

# reference
## 一般
- Types and Programming Languages
- Advanced Topics in Types and Programming Languages
## CoC や PTS
- CoC の元論文
  - Coquand, Thierry, and Gérard Huet. The calculus of constructions. Diss. INRIA, 1986.
    - https://inria.hal.science/inria-00076024/document
- 何を示していけばいいかの指針
  - introduction to generalized type systems, Henk Barendregt, 1991.
    - https://homepages.inf.ed.ac.uk/wadler/papers/barendregt/pure-type-systems.pdf
  - lambda calculi with types, Henk Barendregt, 1992.
    - https://home.ttic.edu/~dreyer/course/papers/barendregt.pdf
- Extended Calculus of Constructions, Zhaohui Luo, 1990.
  - https://era.ed.ac.uk/bitstream/handle/1842/12487/Luo1990.Pdf
  - universe が階層付き + cumulative （$x: U_i$ なら $x: U_{i+1}$ のようなことができる。）
  - predicative dependent sum を作る

## PTS について
- The Structural Theory of Pure Type Systems, Cody Roux and Floris van Doorn, 2014.
  - https://florisvandoorn.com/papers/struct_pts.pdf
  - これは PTS を混ぜたときの性質の話
- formalization of the naive type theory
  - https://mimuw.edu.pl/media/uploads/doctorates/thesis-agnieszka-kozubek.pdf
  - PTS として set と prop を（属する universe をわけつつ）別々に用意して、 naive な set theory を定義しようとしている。
  - Power set が定義できる！

## 帰納型
- Calculus of Inductive Constructions, 2008, MariaJo˜aoFrade
  - http://cl-informatik.uibk.ac.at/teaching/ss19/itp/slides_vo/09.pdf
- Coq manual
  - https://coq.inria.fr/doc/V8.8.2/refman/language/cic.html#inductive-definitions
- Frank Pfenning, Christine Paulin-Mohring. Inductively Defined Types in the Calculus of Constructions
  - https://www.cs.cmu.edu/~fp/papers/mfps89.pdf
- Inductive definitions in the system Coq rules and properties
  - https://link.springer.com/chapter/10.1007/BFb0037116
- https://cstheory.stackexchange.com/questions/36475/defining-primitive-recursive-functions-over-general-data-types
- https://cs.stackexchange.com/questions/89706/how-to-derive-dependently-typed-eliminators
- Complete Bidirectional Typing for the Calculus of Inductive Constructions
  - https://arxiv.org/pdf/2102.06513
  - これは recursor を pattern match を fix に分けている ... pattern 単体では primitive recursion の形をしていない
- Cumulative Inductive Types In Coq
  - https://drops.dagstuhl.de/storage/00lipics/lipics-vol108-fscd2018/LIPIcs.FSCD.2018.29/LIPIcs.FSCD.2018.29.pdf
- Inductively defined types 
  - https://link.springer.com/content/pdf/10.1007/3-540-52335-9_47.pdf
- Amin Timany. Cumulative Inductive Types In Coq
  - https://drops.dagstuhl.de/storage/00lipics/lipics-vol108-fscd2018/LIPIcs.FSCD.2018.29/LIPIcs.FSCD.2018.29.pdf
- Amin Timany and Bart Jacobs. First Steps Towards Cumulative Inductive Types in CIC
  - https://cs.au.dk/~timany/publications/files/2015_ICTAC_first_steps_cumind.pdf

## strong normalization や type check について
- Complete Bidirectional Typing for the Calculus of Inductive Constructions
  - https://arxiv.org/pdf/2102.06513
- Modular proof of strong normalization for the calculus of constructions. Geuvers, Herman, and Mark-Jan Nederhof. 1991.
  - https://www.cambridge.org/core/services/aop-cambridge-core/content/view/348B6914C707F5282ED91E08AE47BDB8/S0956796800020037a.pdf/modular-proof-of-strong-normalization-for-the-calculus-of-constructions.pdf
- Constructions Inductive Types and Strong Normalization
  - https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=23af5ccb0b9d053741aeea62e4c8ac911da52327
- A typechecker for bijective pure type systems
  - https://pure.tue.nl/ws/portalfiles/portal/1688613/9314435.pdf
  - context に type とその sort をいれた体系にして type check をいい感じにする

## proof-irrelevance
- ON THE STRENGTH OF PROOF-IRRELEVANT TYPE THEORIES
  - https://www.lix.polytechnique.fr/Labo/Benjamin.Werner/publis/lmcs.pdf

## inconsistency について
- (In)consistency of Extensions of Higher Order Logic and Type Theory, Herman Geuvers, 2006.
  - https://alexandria.tue.nl/openaccess/Metis211677.pdf
- failure of normalization in impredicative type theory with proof-irrelevant propositional equality, ANDREAS ABEL, THIERRY COQUAND, 2020
  - https://arxiv.org/pdf/1911.08174
- A variation of Reynolds-Hurkens Paradox
  - https://arxiv.org/pdf/2308.16726
- Inconsistency of classical logic in type theory
  - https://www.cs.ru.nl/~herman/PUBS/newnote.pdf
- Inconsistency of “Automath powersets” in impredicative type theory
  - https://www.cs.ru.nl/~herman/PUBS/InconsAutSetTh.pdf
- Proof-irrelevance out of excluded-middle and choice in the calculus of constructions
  - https://core.ac.uk/reader/85216080
- simplification of Girard's paradox
  - https://link.springer.com/content/pdf/10.1007/BFb0014058.pdf?pdf=inline%20link
- https://github.com/coq/coq/wiki/Impredicative-Set
- https://ionathan.ch/2021/11/24/inconsistencies.html
