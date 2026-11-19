# B08 Grassmannian のセル分解

## 作業状況

[grassmannian_cells](../../libs/geometry/grassmannian_cells/README.md) に Schubert 記号、階段形から直交射影モデルへの連続単射、弱位相の増大列の有限段階化を追加した。
型検査は300秒の時間上限で未完了。
セルの同相・付着による有限 CW 構造、向き付き被覆、具体的な安定化極限への適用が残っており、B08 は未完了である。

## 要件

- 主な実装先は `grassmannian_cells`。
- 実・複素の有限 Grassmannian に Schubert セルの座標を構成し、閉包の付着による有限 CW 構造を証明する。
- 周囲次元の標準包含と向き付き Grassmannian の被覆に、CW 構造とその比較を与える。
- 安定化の直極限に弱位相を与え、コンパクトな球面からの写像とホモトピーを有限段階で表す補題を公開する。

## 依存するタスク

- [B05 有限 Grassmannian と普遍束](b05-grassmannians.md)
- [K02 CW cofibration と Puppe 列](../../libs/topology/puppe_sequences/README.md)
