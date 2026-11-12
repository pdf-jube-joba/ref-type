# G05 コンパクト多様体の埋め込み

## 要件

- 主な実装先は `compact_embeddings`。
- 有限チャートと cutoff 関数から閉コンパクト多様体の有限次元 Euclid 空間への滑らかな埋め込みを構成する。
- 境界付きの場合に collar と整合する半空間への neat embedding を構成する。
- 安定化後の二つの埋め込みを結ぶ埋め込みの族を構成し、端を固定する相対版を公開する。

## 依存するタスク

- [G01 滑らかな bump 関数と従属分割](../../libs/geometry/smooth_partitions/README.md)
- [G02 逆関数・陰関数と正則値の局所形](../../libs/geometry/inverse_implicit/README.md)
- [G04 collar と境界の貼り合わせ](../../libs/geometry/manifold_gluing/README.md)

## 実装

[compact_embeddings](../../libs/geometry/compact_embeddings/README.md) に実装。

- `Compact.On.exists`: 有限チャート・cutoff の選択から実際の Euclid 埋め込みを構成し、空多様体も扱う。
- `NeatExistence.On.With.Compact.exists`: compact double、Euclid 埋め込み、collar の潰し写像と高さから半空間への neat embedding を構成する。正の幅の collar 上で厳密な積の式を証明する。
- `Stabilization.On.Between`: 安定化した埋め込みの滑らかな族、両端を固定する相対版、パラメータ変換と前合成の自然性を公開する。
- `Naturality.On`: 微分同相による引き戻しと任意の二つの構成結果の比較。
- `Examples`: 空多様体、一点、実直線の族、両端の像と collar 条件を含む閉区間の例。
