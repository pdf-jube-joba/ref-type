# 基本群と被覆の分類

実装・検査完了。
基本群は実区間上の道の端点固定ホモトピー類から構成し、被覆は連続な全射の局所自明化として定義する。

- [x] `fundamental_groups.TwoOpenSets.vanKampen` は、二つの開集合と共通部分の基本群について融合積の普遍性を証明する。
- [x] `covering_spaces.Subgroups.existsStandardRealization` は、局所道連結・半局所単連結な道連結空間の任意の部分群から基点付き連結被覆を構成する。
- [x] `Comparison.pointedClassification` と `uniquePointedMap` は、同じ部分群に対応する基点付き被覆の同型と写像の一意性を証明する。
- [x] `Comparison.unpointedClassification` は、基点なしの連結被覆を部分群の共役で分類する。
- [x] `Subgroups.existsUniversalCover` と `Comparison.universalLifting` は、単連結な普遍被覆とその普遍性を与える。
- [x] `Projection.Deck.normalizerQuotient` と `normalCoverCriterion` は、deck 変換群と \(N(H)/H\) の群としての対応、正規被覆の判定を与える。

`Neighborhoods.goodBasis` は標準的な局所道連結性と半局所単連結性から必要な近傍基底を導く。
`PathAction.Realization` は基本亜群の作用からシートの位相と局所自明化を構成し、構成した被覆の輸送が元の作用と一致することを証明する。

融合積は `algebra.AmalgamatedProduct.Universal` の普遍性で表す。
`TwoOpenSets` は標準的な包含による誘導準同型がこの普遍性を満たすことを証明する。
`AmalgamatedProduct.Other.canonicalIsomorphism` は同じ普遍性を満たす別の群との標準同型を構成する。

検査は共有キャッシュを用いる次の範囲で成功した。

```sh
target/debug/cli libs/topology/fundamental --module fundamental_groups
target/debug/cli libs/topology/coverings --module covering_spaces
target/debug/cli libs/algebra/basic --module algebra.AmalgamatedProduct
```
