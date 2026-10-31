# A05 Lp 空間のノルムと完備性

## 要件

- 主な実装先は `lp_spaces`。
- 既存の Lp の商にノルムと線形構造を与え、Hölder・Minkowski と完備性を証明する。
- 実・複素 L2 の Hilbert 空間構造、可積分単関数とコンパクト台付き連続関数の稠密性を証明する。
- 平行移動の連続性と近似単位による平滑化を構成し、コンパクト台付き滑らかな関数の稠密性を公開する。

## 依存するタスク

- [A03 積測度と Fubini](a03-product-integration.md)
- [G01 滑らかな bump 関数と従属分割](g01-smooth-partitions.md)

## 実装

`libs/analysis/lp_spaces/README.md` に公開 API と測度・指数の適用範囲を記載する。
`On.Finite`・`On.Infinity` が既存の商の実 Banach 構造を、`On.Hilbert`・`On.Complex` が実・複素 L2 の Hilbert 構造を与える。
単関数近似、Euclid 上のコンパクト台連続・滑らかな関数の稠密性、平行移動の連続性、Borel 代表と共同可測性、畳み込みの滑らかさ・縮小評価・近似単位の収束を証明する。
`Examples` と `EuclideanExamples` は一般の測度・次元・有限実指数・商の元を使う検査対象の利用例である。
検査記録は `benchmarks/records/a05-lp-spaces/` に保存する。
