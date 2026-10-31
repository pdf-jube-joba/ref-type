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

実装中: [thom_spaces](../../libs/topology/thom_spaces/README.md)。
円板束・球面束・基点を加えた Thom 商、実・複素の計量変更の同相、直和の反復商比較、cofibration、基点を加えた対の相対特異理論比較を構成した。
自明束には円板 suspension モデルとの同相がある。
円板束と底のホモトピー同値、および有限 CW 基底の各セル上の束の自明化も構成した。

有限 CW 対のモデルと対の比較同値は未実装である。
既存の reduced suspension の反復への比較と、追加した一点を除く相対特異理論の比較も残る。
C02 全体の完了状態には達していない。
