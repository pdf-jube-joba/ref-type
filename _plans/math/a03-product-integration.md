# A03 積測度と Fubini

## 要件

- 主な実装先は `product_integration`。
- σ 有限測度の積を構成し、Euclid 空間の直積の Lebesgue 測度と比較する。
- Tonelli と Fubini の定理を証明し、複素・有限次元値の可積分関数に拡張する。
- 畳み込みの存在条件、積分の交換、台と L1 ノルムの評価を公開する。

## 依存するタスク

- [A02 Euclid 空間の Lebesgue 測度](a02-lebesgue-measure.md)

## 実装 API

[product_integration](../../libs/analysis/product_integration/README.md) に実装する。
`Product` が σ 有限積測度、`Integration` が Tonelli・実数値 Fubini、同 module の `Complex` と `Vector` が成分値積分を提供する。
`EuclideanProduct.Comparison.theorem` は座標連結による積測度と Euclid Lebesgue 測度の Borel 制限の一致を証明する。
`Convolution.For.exists` は共同可測な畳み込み核の存在条件から a.e. 可積分性、積分交換と L1 評価を導き、`Support.theorem` は台の包含を与える。
最小利用例は `Examples` で検査する。
