# 位相幾何

位相空間とホモトピーの基礎から、特異理論、具体的な空間の計算へ進む。
パッケージの直接依存は各 `ref.toml`、全体の検査対象は [libs/ref.toml](../ref.toml) にある。

| 配置 | 内容 |
| --- | --- |
| [basic](basic/README.md) | 位相空間、部分空間、連続写像、コンパクト性、分離性 |
| [metric](metric/README.md) | 距離空間、距離化、実数直線と従属分割 |
| [constructions](constructions/README.md) | 積、商、直和、貼り合わせ、compact-open 位相 |
| [algebra](algebra/README.md) | 位相的代数、座標空間と行列位相 |
| [thom_spaces](thom_spaces/README.md) | 円板束・球面束、Thom 商と計量・直和比較（C02 実装中） |
| [homotopy](homotopy/README.md) | ホモトピー、基点付き商、mapping cone、CW 対と標準単体 |
| [singular](singular/README.md) | 特異鎖・余鎖、切除、積、有限モデルとの比較 |
| [spheres](spheres/README.md) | 球面の向き、反転と円周の整数べき写像の次数 |
| [examples](examples/README.md) | 特徴的な空間と有限モデルでの利用例 |

各パッケージの名前は、配置とは別に `ref.toml` の `name` で定まる。
例えば `singular/cohomology` は `singular_cohomology`、`homotopy` は `algebraic_topology` として参照する。

基本群と被覆については [fundamental](fundamental/README.md) と [coverings](coverings/README.md) を参照する。

CW 部分複体のホモトピー拡張性、基点付き cofiber の反復と反変 Hom の完全性は [puppe_sequences](puppe_sequences/README.md) にまとめる。
