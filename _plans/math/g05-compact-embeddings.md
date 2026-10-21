# G05 コンパクト多様体の埋め込み

## 要件

- 主な実装先は `compact_embeddings`。
- 有限チャートと cutoff 関数から閉コンパクト多様体の有限次元 Euclid 空間への滑らかな埋め込みを構成する。
- 境界付きの場合に collar と整合する半空間への neat embedding を構成する。
- 安定化後の二つの埋め込みを結ぶ埋め込みの族を構成し、端を固定する相対版を公開する。

## 依存するタスク

- [G01 滑らかな bump 関数と従属分割](g01-smooth-partitions.md)
- [G02 逆関数・陰関数と正則値の局所形](g02-inverse-implicit.md)
- [G04 collar と境界の貼り合わせ](g04-collars-gluing.md)
