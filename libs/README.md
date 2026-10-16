# ライブラリ

依存先は各 `ref.toml`、公開 module は `src/root.ref` にある。
`std` 以外は約5,000行を目安に、共有基盤から応用へ依存する単位で分ける。

| 配置 | パッケージ | 内容 |
| --- | --- | --- |
| [std](std/README.md) | `std` | 論理、データ、整数・有理数、商、代数構造 |
| [category](category/README.md) | `category` | 圏、関手、自然変換、普遍性、随伴、加法圏・アーベル圏 |
| [real/axiomatic](real/axiomatic/README.md) | `ordered_fields` | 順序体と上限完備性の共通構造 |
| [real/dedekind](real/dedekind/README.md) | `dedekind_reals` | 有理数の切断による実数、演算・順序・完備性 |
| [real/cauchy](real/cauchy/README.md) | `cauchy_reals` | 有理数 Cauchy 列の商による実数、演算・順序・完備性 |
| [real/basic](real/basic/README.md) | `real` | 構成済みの実数の演算、距離評価、数列、平方根、有限和 |
| [complex](complex/README.md) | `complex` | 実数対による複素数と体の構造 |
| [algebra/basic](algebra/basic/README.md) | `algebra` | 準同型、群完成、商、多項式環 |
| [algebra/module_theory](algebra/module_theory/README.md) | `module_theory` | 環上の加群、自由加群、直和、テンソル積、完全列 |
| [algebra/commutative_algebra](algebra/commutative_algebra/README.md) | `commutative_algebra` | Hom とテンソル積、射影性、有限自由加群の行列 |
| [algebra/integer_matrices](algebra/integer_matrices/README.md) | `integer_matrices` | 整数行列の演算、Smith 標準形と変換行列 |
| [algebra/finitely_generated_modules](algebra/finitely_generated_modules/README.md) | `finitely_generated_modules` | 整数の核・像・部分加群の基底、巡回加群、体上の有限次元部分空間 |
| [algebra/linear_algebra](algebra/linear_algebra/README.md) | `linear_algebra` | 体上の線形代数、多重線形・外代数、実数・複素数への具体化 |
| [algebra/homological/chain_complexes](algebra/homological/chain_complexes/README.md) | `chain_complexes` | 自然数・整数次数の複体、ホモロジー、写像・ホモトピー・複体の圏 |
| [algebra/homological/double_complexes](algebra/homological/double_complexes/README.md) | `double_complexes` | 非負鎖複体、二重複体、total、比較の完全性と符号付き交換 |
| [algebra/homological/resolutions](algebra/homological/resolutions/README.md) | `resolutions` | 射影分解、比較定理、Hom・テンソル複体、二重 total による分解比較 |
| [algebra/homological/tensor_chains](algebra/homological/tensor_chains/README.md) | `tensor_chains` | 整数次数のテンソル total、外積と自然性、符号付き次数移動、可換四角形 |
| [algebra/homological/derived_functors](algebra/homological/derived_functors/README.md) | `derived_functors` | Ext・Tor、分解からの独立性と自然性、巡回加群の分解、普遍係数 |
| [algebra/homological/field_kunneth](algebra/homological/field_kunneth/README.md) | `field_kunneth` | 有限自由体係数余鎖複体、標準外積同型、自然性・交換符号・単位 |
| [algebra/homological/computations](algebra/homological/computations/README.md) | `homological_algebra` | 有限整数複体のホモロジー計算、普遍係数・整数 Künneth の自然な短完全列 |
| [analysis/calculus](analysis/calculus/README.md) | `calculus` | 極限、平均値定理、多変数微分、滑らかな写像 |
| [analysis/integration](analysis/integration/README.md) | `integration` | リーマン積分、L¹ 完備化によるルベーグ積分 |
| [geometry/manifolds](geometry/manifolds/README.md) | `manifolds` | アトラス、滑らかな写像、接空間と微分 |
| [geometry/euclidean_forms](geometry/euclidean_forms/README.md) | `euclidean_forms` | 局所微分形式、外積・外微分、座標表示、引き戻し |
| [geometry/differential_forms](geometry/differential_forms/README.md) | `differential_forms` | 大域微分形式、貼り合わせ、引き戻し、De Rham コホモロジー |
| [topology/basic](topology/basic/README.md) | `topology` | 位相・部分空間、連続写像、コンパクト性、分離性 |
| [topology/metric_spaces](topology/metric_spaces/README.md) | `metric_spaces` | 距離位相、距離化、実数直線、実数値関数、有限従属分割 |
| [topology/topological_constructions](topology/topological_constructions/README.md) | `topological_constructions` | 積、商、直和、貼り合わせ、compact-open 位相 |
| [topology/topological_algebra](topology/topological_algebra/README.md) | `topological_algebra` | 位相的代数、座標空間・行列位相、連続性判定 |
| [topology/algebraic_topology](topology/algebraic_topology/README.md) | `algebraic_topology` | ホモトピー、基点付き商、mapping cone、有限 CW 対、標準単体の座標 |
| [topology/singular_cohomology](topology/singular_cohomology/README.md) | `singular_cohomology` | 特異鎖・余鎖、相対・被約理論、ホモトピー不変性、道成分と可縮空間 |

標準の実数は `dedekind_reals` から `real` に渡す。
共通の数値補題は `real.Analysis`、演算と法則の分離には `Def` / `Prop`、等式連鎖には [eq_reason!](std/README.md#等式と合同則) を使う。

## 型検査

```sh
cargo run -p cli -- libs
cargo run -p cli -- libs/std --module std.Data.Nat
```

`libs/ref.toml` の workspace 全体で `libs/refcache/` を共有する。
再検査・資源制限・進捗は [利用方法](../src/USAGE.md#検査とキャッシュ) を参照。

具体例は [複体](algebra/homological/concrete_complexes/README.md)、[座標計算](geometry/coordinate_calculus/README.md)、[cell_spaces](topology/cell_spaces/src/root.ref)、[スカラーの互換性](analysis/scalar_compatibility/README.md)、[小さい圏](category/src/SmallCategories.ref) と [終対象の圏の極限](category/src/TerminalLimits.ref) にある。

[特異コホモロジーの利用例](topology/cohomology_models/README.md)は代表余鎖、相対接続、係数付き誘導写像、道成分と空空間・一点・区間の計算を検査する。
