# B08 Grassmannian のセル分解

## 作業状況

[grassmannian_cells](../../libs/geometry/grassmannian_cells/README.md) に全要件に対応する定義と証明項を記述した。
実装した範囲と型検査による確認がない範囲を区別し、以下を記録する。

| 要件 | 実装した API |
| --- | --- |
| Schubert 座標、総次元式、階段形分解、網羅性・非交叉 | `Symbols.FreeCount`、`Canonical.FiniteCoordinates`、`Reduction`、`DecompositionReal`・`DecompositionComplex` |
| 閉球の積と標準円板の同一視 | `Rotations.Parameters.Disk`、`Characteristic.diskExists` |
| 特性写像の内部同相、境界の低次元セルへの包含 | `StandardDisk.interiorImage`・`interiorHomeomorphism`、`Characteristic.boundaryLower` |
| 実・複素の有限 CW 構造 | `CWReal.exists`・`CWComplex.exists`、既存の `algebraic_topology.CW.FiniteComplex` |
| 周囲次元の標準包含と CW 構造の比較 | `AmbientReal.CW`・`AmbientComplex.CW` の `cellular`・`reflects`・`cellHomeomorphism`、`With.filtrationEquals` |
| 向き付き実 Grassmannian の被覆 | `OrientedReal.covering`・`twoSheets`、`Atlas.In.homeomorphism` |
| 被覆へ持ち上げた有限 CW 構造と比較 | `OrientedReal.CW.exists`、`With.projects`・`filtrationEqualsPreimage` |
| 安定化極限、球面写像・ホモトピーの有限段階化 | `StableReal`・`StableComplex` の `weakTopology`・`Maps.exists`・`Spheres.sphereMap`・`sphereHomotopy` |

2026-11-20 の追補では、対象パッケージの `--parse-only --diagnostics compact` と `git diff --check` が終了コード0で完了した。
対象・全体の型検査は実行していない。
構文解析は名前解決や型の整合性を検査しないため、上表の追補全体は型検査による確認がない。
引き継ぎ前の初回型検査も300秒で未完了であり、B08 の形式的な検証完了は宣言しない。
新しい公理宣言や未証明のための置き換えは追加していない。
成果は既存の [Draft PR #81](https://github.com/pdf-jube-joba/ref-type/pull/81) に継続してまとめる。

## 要件

- 主な実装先は `grassmannian_cells`。
- 実・複素の有限 Grassmannian に Schubert セルの座標を構成し、閉包の付着による有限 CW 構造を証明する。
- 周囲次元の標準包含と向き付き Grassmannian の被覆に、CW 構造とその比較を与える。
- 安定化の直極限に弱位相を与え、コンパクトな球面からの写像とホモトピーを有限段階で表す補題を公開する。

## 依存するタスク

- [B05 有限 Grassmannian と普遍束](b05-grassmannians.md)
- [K02 CW cofibration と Puppe 列](../../libs/topology/puppe_sequences/README.md)
