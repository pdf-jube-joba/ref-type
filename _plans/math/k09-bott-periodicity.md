# K09 Bott 周期性と整数次数

## 要件

- 主な実装先は `periodic_k_theory`。
- Bott 元との外積による2周期同型を相対・被約理論に構成し、全整数次数へ延長する。
- 次数付き積の符号、6項完全列、自然性を証明する。
- 一点・球面の K 群と Bott 元の反復による生成元を計算し、負一次の一点での消滅を証明する。

## 依存するタスク

- [K08 Bott の基本積定理](k08-bott-product.md)（実装済み）

## 公開した実装

[periodic_k_theory](../../libs/topology/periodic_k_theory/README.md) に実装した。

- `Reduced` と `RelativePair` は実際の Bott 外積と逆写像を構成し、`Formula.productFormula` が既存の相対外積との一致を示す。
- `TwoShift`、`Negative`、`Integer` は二重 suspension との比較、自然な2周期同型、全整数次数、元の負次数との比較を与える。
- `Product.gradedCommutative` は実際の因子交換に対する Koszul 符号を示す。
- `SixTerm` と `SixTerm.Naturality` は6か所の完全性と6つの自然な可換図式を与える。
- `Point.oddZero` は一般線形群の道連結性と区間・境界対の計算から通常の一点の負一次群の消滅を示す。
- `Point.At`、`Spheres.At`、`Spheres.Ordinary`、`Spheres.OrdinaryOdd` は一点・球面の群を計算し、`BottSpheres` は Bott 外積を反復した生成元を与える。
- `Examples` は一点の消滅、生成元、Bott 同型と負次数の周期同型の往復を含む最小利用例を公開する。

通常検査はリポジトリの `cargo build -p cli --release --locked` と `python3 scripts/check_all.py --memory-mib 10240` を使う。
