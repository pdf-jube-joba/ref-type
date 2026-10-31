# C02 円板束・球面束と Thom 空間

## 要件

- 主な実装先は `thom_spaces`。
- 実・複素の計量付き束の円板束・球面束とその商である Thom 空間を構成する。
- 計量によらない比較、自明束の suspension 表示、直和と反復 Thom 空間の比較を証明する。
- 基底が有限 CW の場合の束対の有限 CW 型、cofibration と相対特異理論への接続を構成する。

## 依存するタスク

- [束の計量・補束と同型類](../../libs/geometry/bundle_complements/README.md)
- [K02 CW cofibration と Puppe 列](../../libs/topology/puppe_sequences/README.md)
- [B04 束のホモトピー不変性と clutching](../../libs/geometry/bundle_homotopy/README.md)

## 実装状況

実装済: [thom_spaces](../../libs/topology/thom_spaces/README.md)。
実・複素の計量付き円板束・球面束と基点付き Thom 商、任意の連続計量の間の同相、直和と反復 Thom 商との比較を構成した。
自明束は実次元 \(n\)・\(2n\) の円板 suspension モデルへ同相であり、既存の懸垂を反復した任意の自然数次数の表示とも比較する。

有限 CW 基底では、B04 のセル上の自明化から実際の束対を有限 CW 複体・部分複体へ比較する対ホモトピー同値を構成した。
実・複素の入口は `FiniteBase.pairFiniteType` であり、`PairModel` は有限モデルと部分空間を保つ両側のホモトピーを公開する。
付着写像のセル近似、任意のセル付着の対比較、および部分複体の誘導位相の有限 CW 構造も証明した。
球面境界の cofibration、Puppe 比較、付加点を切除した実際の円板・球面対の相対特異理論、および有限 CW 対モデルとの相対比較を接続した。
ランク0と空の基底を含む実・複素の例を検査する。

最終ソースと検査結果は [完了時の検証記録](../../benchmarks/records/c02-thom-spaces/completed/README.md) に保存する。
