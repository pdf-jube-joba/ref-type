# T02 安定ホモトピー類と Thom スペクトラム

## 要件

- 主な実装先は `stable_thom_spaces`。
- 基点付き球面からのホモトピー類、suspension 写像、その直極限による安定ホモトピー群を構成する。
- 有限 Grassmannian 上の普遍束の Thom 空間と構造写像から MO・MSO と枠付きの場合の球面スペクトラムを構成する。
- 有限段階の表示、安定化、直和による積と符号を証明し、後続が有限段階の代表で操作できる API を公開する。

## 依存するタスク

- [B06 束の分類写像と安定化](b06-bundle-classification.md)
- [C02 円板束・球面束と Thom 空間](c02-thom-spaces.md)
- [K02 CW cofibration と Puppe 列](../../libs/topology/puppe_sequences/README.md)
- [B08 Grassmannian のセル分解](b08-grassmannian-cells.md)
