# G04 collar と境界の貼り合わせ

## 要件

- 主な実装先は `manifold_gluing`。
- コンパクトな境界付き多様体の collar を構成し、指定された境界近傍での相対版と選択の比較を証明する。
- 境界の微分同相に沿う貼り合わせと double の滑らかな構造を構成する。
- 積の角の丸め、向きと境界向きの符号、collar を保つ写像の貼り合わせを公開する。

## 依存するタスク

- [G01 滑らかな bump 関数と従属分割](g01-smooth-partitions.md)
- [G03 境界・角付き多様体](g03-boundary-manifolds.md)

## 実装

実装済み。
公開 API と定理の範囲は [manifold_gluing](../../libs/geometry/manifold_gluing/README.md) にまとめる。

| 要件 | 実装 |
| --- | --- |
| コンパクトな境界付き多様体の collar | `CollarEmbedding.On.With.exists`、実際の局所逆写像と一様な正の幅を持つ大域 collar |
| 指定近傍での相対版と選択の比較 | `CollarRelative.On.With.In.exists`、`CollarComparison` の境界を固定する滑らかな比較 |
| 境界の微分同相による貼り合わせと double | `CompactGluing`、`Double` の実際の商・滑らかな atlas・境界なしの保証、左右と継ぎ目の滑らかな包含と値の法則 |
| 積の角の丸め | `ProductCollar` のコンパクト領域に支持された丸め、`RoundedBoundary.Compact.exists` の境界 atlas と `Boundary.Cover`、各点で有効な境界面が高々一つである保証 |
| 向きと境界向きの符号 | `GluingForms` の実際の継ぎ目写像の微分による frame と最高次形式の符号、外向き境界形式の打ち消し、`DoubleForms` による double への特殊化 |
| collar を保つ写像の貼り合わせ | `SeamCollar.Image.Compact.Cover.CollarMaps` の実際の滑らかな写像の貼り合わせと恒等写像の例 |

相対版は、境界全体の指定された開近傍に collar の像を収める定理である。
既存の部分 collar と一致する拡張は、これより強い別の定理である。
