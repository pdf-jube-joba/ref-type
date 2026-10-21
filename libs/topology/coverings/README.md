# 被覆空間と分類

`Projection[E, B, total, base, projection]` は全空間、底空間、位相と射影を受け取る。
`Covering` は連続性、全射性、および各底点の近傍でファイバーに離散位相を入れた積への局所自明化を要求する。

| module | 内容 |
| --- | --- |
| `Projection.Around` / `Sheets` | 局所自明化、連続な局所切断、開シート |
| `Projection.Lifting.Existence` / `Uniqueness` | 道の持ち上げの存在と一意性 |
| `Projection.Lifting.Squares` / `Homotopy` | 正方形の持ち上げと端点固定ホモトピーの反映 |
| `Projection.Transport.Groupoid` / `Action` | 基本亜群による輸送と基本群のファイバー上の右作用 |
| `Projection.Fundamental` / `Monodromy` | 誘導基本群の単射性、像と安定化部分群の一致、剰余類とファイバーの同変全単射 |
| `PathAction.Realization` | 基本亜群の作用からシートの位相と局所自明化を構成し、輸送の一致を証明 |
| `Subgroups.existsStandardRealization` | 局所道連結・半局所単連結な道連結空間で任意の部分群を基点付き連結被覆として実現 |
| `Comparison.pointedClassification` / `uniquePointedMap` | 安定化部分群の一致による基点付き同型と、その写像の一意性 |
| `Comparison.unpointedClassification` | 基点なしの連結被覆の同型と部分群の共役による分類 |
| `Subgroups.existsUniversalCover` / `Comparison.universalLifting` | 単連結な普遍被覆の存在と、指定した基点を通る他の被覆への写像 |
| `Projection.Deck.normalizerQuotient` / `normalCoverCriterion` | deck 変換群と正規化群の商、正規被覆の判定 |

持ち上げの存在には区間・正方形のコンパクト性と有限細分を使う。
一意性は局所自明化の離散ファイバーと、離散空間への連続な道の定値性から示す。

`fundamental_groups.Neighborhoods` の `goodBasis` は、標準的な局所道連結性と半局所単連結性から、道連結で包含が基本群を消す開近傍の基底を与える。
`PathAction.Realization` はその基底上の道による輸送からシートを定め、位相の公理、射影の連続性、積への局所自明化を証明する。
剰余類上の右作用を入れると、`Subgroups.Realization[H]` は指定した部分群 \(H\) を誘導基本群の像に持つ。

`Projection.Fundamental[e].Monodromy[covering].imageMembership` は \(p_*\pi_1(E,e)\) と安定化部分群の一致を与える。
分類の `SameSubgroup` と `Conjugate` はこの安定化部分群で述べる。
共役の規約は \(g\mapsto aga^{-1}\) である。

`Projection.Deck[point].Carrier` は射影と可換する全空間の自己同相写像であり、`group` の積は通常の関数合成である。
`Classification.NormalCosets` は \(H\backslash\pi_1(B,b)\) のうち、代表元が \(H\) を正規化する剰余類である。
`normalizerToClass` と `classToNormalizer` はこの代表元による特徴付けを証明する。
`normalizerQuotient` はこの集合に群構造を与え、deck 変換群からの準同型と相互逆を返す。
`QuotientIsomorphism.product` は代表元の積が \([a][b]=[ab]\) になることを保証するので、商は \(N(H)/H\) である。
正規被覆の判定は、\(H\) の正規性と基点上のファイバーに対する deck 変換の推移性の同値である。

```sh
target/debug/cli libs/topology/coverings --module covering_spaces
```
