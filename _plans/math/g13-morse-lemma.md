# G13 Morse 補題の局所解析

## 実装

[morse_lemma](../../libs/geometry/morse_lemma/README.md) に実装した。
以下の公開定理は結論を仮定入力にせず、実際の線形同型・滑らかな両側逆・開近傍を構成する。

| 要件 | 公開 API |
| --- | --- |
| 非退化対称形式の分解と慣性指数 | `Inertia.normalFormExists`、`Inertia.Index.negativeIndex` / `positiveIndex`、合同不変性と指数の選択独立性 |
| 非退化臨界点の局所正規形 | `Hadamard.localExistence`、`NormalForm.localExistence`、`NormalForm.Indices` |
| パラメータに沿う局所版 | `Parametric.Function.criticalBranchExists`、`FiberHadamard.localExistence`、`Morse.localExistence` |
| 臨界点の性質 | `CriticalPoints.At.isolated` / `locallyConstant`、`Parametric.Function.Indices.locallyConstant` |

非線形な一変数関数、鞍点、非定数の臨界点族、零次元の独立した例を `Examples` に置く。
実装の説明・利用方法と、型検査の範囲・再現手順・制限は [README](../../libs/geometry/morse_lemma/README.md) と [検査記録](../../libs/geometry/morse_lemma/VALIDATION.md) に分けて記す。
対象の 137 module 全ての再検査と依存閉包の検証は通過した。
ライブラリ全体の検査は、基点 main と同一の `euclidean_sobolev/Euclidean/Order/Weight.ref:14` で失敗しており、全体の通過とは区別する。

## 要件

- 主な実装先は `morse_lemma`。
- 実対称双線形形式の慣性指数と非退化性を扱い、座標変更による平方和と負平方和への分解を証明する。
- 非退化臨界点の近傍で、滑らかな関数を臨界値と標準二次形式の和にする座標を構成する。
- パラメータに沿う局所版と、臨界点の孤立性・指数の局所定数性を公開する。

## 依存するタスク

- [G02 逆関数・陰関数と正則値の局所形](g02-inverse-implicit.md)
- [Hermitian 行列と連続な局所枠](../../libs/algebra/hermitian_frames/README.md)
