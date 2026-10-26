# ライブラリ

依存先は各 `ref.toml`、公開 module は `src/root.ref` にある。
`std` 以外は約5,000行を目安に、共有基盤から応用へ依存する単位で分ける。

## 基礎

| 配置 | パッケージ | 内容 |
| --- | --- | --- |
| [std](std/README.md) | `std` | 論理、データ、整数・有理数、商、代数構造 |
| [category](category/README.md) | `category` | 圏、関手、自然変換、普遍性、随伴、加法圏・アーベル圏 |

## 数系

| 配置 | パッケージ | 内容 |
| --- | --- | --- |
| [real/axiomatic](real/axiomatic/README.md) | `ordered_fields` | 順序体と上限完備性の共通構造 |
| [real/dedekind](real/dedekind/README.md) | `dedekind_reals` | 有理数の切断による実数、演算・順序・完備性 |
| [real/cauchy](real/cauchy/README.md) | `cauchy_reals` | 有理数 Cauchy 列の商による実数、演算・順序・完備性 |
| [real/basic](real/basic/README.md) | `real` | 構成済みの実数の演算、距離評価、数列、平方根、有限和 |
| [complex](complex/README.md) | `complex` | 実数対による複素数と体の構造 |

標準の実数は `dedekind_reals` から `real` に渡す。
共通の数値補題は `real.Analysis`、演算と法則の分離には `Def` / `Prop`、等式連鎖には [eq_reason!](std/README.md#等式と合同則) を使う。

## 代数

| 配置 | パッケージ | 内容 |
| --- | --- | --- |
| [algebra/basic](algebra/basic/README.md) | `algebra` | 準同型、群完成、商、多項式環 |
| [algebra/galois](algebra/galois/README.md) | `galois` | 体拡大、最小多項式、自己同型の延長、ガロア接続、根号・作図可能性、有理数の代数閉包の定義 |
| [algebra/quintic](algebra/quintic/README.md) | `quintic` | 一般5次方程式の根号非可解性と作図不可能性 |
| [algebra/module_theory](algebra/module_theory/README.md) | `module_theory` | 環上の加群、自由加群、直和、テンソル積、完全列 |
| [algebra/commutative_algebra](algebra/commutative_algebra/README.md) | `commutative_algebra` | Hom とテンソル積、射影性、有限自由加群の行列 |
| [algebra/integer_matrices](algebra/integer_matrices/README.md) | `integer_matrices` | 整数行列の演算、Smith 標準形と変換行列 |
| [algebra/finitely_generated_modules](algebra/finitely_generated_modules/README.md) | `finitely_generated_modules` | 整数の核・像・部分加群の基底、巡回加群、体上の有限次元部分空間 |
| [algebra/linear_algebra](algebra/linear_algebra/README.md) | `linear_algebra` | 可換環上の線形・多重線形・外代数、実数・複素数への具体化 |
| [algebra/matrix_invariants](algebra/matrix_invariants/README.md) | `matrix_invariants` | 行列式、余因子・随伴行列、逆行列、実・複素行列族の連続性と開性 |
| [algebra/polynomial_linear_algebra](algebra/polynomial_linear_algebra/README.md) | `polynomial_linear_algebra` | 多項式の除法・互除法と Bézout 係数、中国剰余定理、Cayley–Hamilton、核の直和分解と係数変更 |
| [algebra/fundamental_algebra](algebra/fundamental_algebra/README.md) | `fundamental_algebra` | 複素多項式の無限遠での評価・最小値・根の存在、重複度付き完全分解と一意な有限根族 |
| [algebra/complex_polynomial_roots](algebra/complex_polynomial_roots/README.md) | `complex_polynomial_roots` | 根の有界性、有限対称積と係数空間の同相、分離した根群の連続な因子 |
| [algebra/hermitian_frames](algebra/hermitian_frames/README.md) | `hermitian_frames` | Hermitian 形式、連続な正規直交化、射影の局所枠と逆座標、ユニタリ群 |
| [algebra/spectral_splitting](algebra/spectral_splitting/README.md) | `spectral_splitting` | 単位円内外の根因子、連続なスペクトル射影、像束とホモトピー比較 |
| [algebra/lie_algebras](algebra/lie_algebras/README.md) | `lie_algebras` | リー代数、随伴表現、交換子、部分リー代数、自己準同型代数 |
| [algebra/clifford](algebra/clifford/README.md) | `clifford` | クリフォード代数の商構成と普遍性、Pin・Spin と複素拡張の群構造 |
| [algebra/homological/chain_complexes](algebra/homological/chain_complexes/README.md) | `chain_complexes` | 自然数・整数次数の複体、ホモロジー、写像・ホモトピー・複体の圏 |
| [algebra/homological/double_complexes](algebra/homological/double_complexes/README.md) | `double_complexes` | 非負鎖複体、二重複体、total、比較の完全性と符号付き交換 |
| [algebra/homological/resolutions](algebra/homological/resolutions/README.md) | `resolutions` | 射影分解、比較定理、Hom・テンソル複体、二重 total による分解比較 |
| [algebra/homological/tensor_chains](algebra/homological/tensor_chains/README.md) | `tensor_chains` | 整数次数のテンソル total、外積と自然性、符号付き次数移動、可換四角形 |
| [algebra/homological/derived_functors](algebra/homological/derived_functors/README.md) | `derived_functors` | Ext・Tor、分解からの独立性と自然性、巡回加群の分解、普遍係数 |
| [algebra/homological/field_kunneth](algebra/homological/field_kunneth/README.md) | `field_kunneth` | 有限自由体係数余鎖複体、標準外積同型、自然性・交換符号・単位 |
| [algebra/homological/computations](algebra/homological/computations/README.md) | `homological_algebra` | 有限整数複体のホモロジー計算、普遍係数・整数 Künneth の自然な短完全列 |

## 解析

| 配置 | パッケージ | 内容 |
| --- | --- | --- |
| [analysis/uniform_approximation](analysis/uniform_approximation/README.md) | `uniform_approximation` | 実・複素 Stone–Weierstrass、円周と積上の Laurent 近似、行列・束自己準同型の一様評価 |
| [analysis/calculus](analysis/calculus/README.md) | `calculus` | 極限、平均値定理、多変数微分、滑らかな写像 |
| [analysis/differential_equations](analysis/differential_equations/README.md) | `differential_equations` | Picard の積分作用素、常微分方程式の局所解の存在・一意性、滑らかなベクトル場の解の滑らかさ |
| [analysis/functional](analysis/functional/README.md) | `functional_analysis` | 実ノルム空間・Hilbert 空間、Arzelà–Ascoli・Riesz 表現・Hahn–Banach・開写像定理、コンパクト台、\(L^p\)・弱微分・Sobolev 空間の定義 |
| [analysis/integration](analysis/integration/README.md) | `integration` | リーマン積分、L¹ 完備化によるルベーグ積分 |

## 幾何

| 配置 | パッケージ | 内容 |
| --- | --- | --- |
| [geometry/manifolds](geometry/manifolds/README.md) | `manifolds` | アトラス、滑らかな写像、接空間と微分 |
| [geometry/vector_bundles](geometry/vector_bundles/README.md) | `vector_bundles` | 一般の実・複素束、局所定数ランク、束写像・切断・引き戻しと普遍性 |
| [geometry/bundle_operations](geometry/bundle_operations/README.md) | `bundle_operations` | Cocycle の貼り合わせ、直和・テンソル・双対・Hom・外冪、実化・複素化と引き戻し |
| [geometry/bundle_complements](geometry/bundle_complements/README.md) | `bundle_complements` | 有限分割からの計量・有限埋め込み、直交補束、連続射影の像と同型類の集合 |
| [geometry/bundle_homotopy](geometry/bundle_homotopy/README.md) | `bundle_homotopy` | 束のホモトピー比較、cofibration に沿う相対延長、球面の clutching と gauge による同型判定 |
| [geometry/tangent_bundles](geometry/tangent_bundles/README.md) | `tangent_bundles` | 接束の全空間、接写像、関手則、滑らかなファイバー演算 |
| [geometry/normal_bundles](geometry/normal_bundles/README.md) | `normal_bundles` | はめ込みの法束、局所正規直交枠、直和分解、底空間変更と安定化 |
| [geometry/examples/tangent_normal](geometry/examples/tangent_normal/README.md) | `tangent_normal` | ユークリッド接束、座標包含、放物線、退化次数の利用例 |
| [geometry/lie_groups](geometry/lie_groups/README.md) | `lie_groups` | リー群・リー代数、随伴微分・指数写像、O・SO・Pin・Spin と複素拡張のリー群構造 |
| [geometry/euclidean_forms](geometry/euclidean_forms/README.md) | `euclidean_forms` | 局所微分形式、外積・外微分、座標表示、引き戻し |
| [geometry/differential_forms](geometry/differential_forms/README.md) | `differential_forms` | 大域微分形式、貼り合わせ、引き戻し、De Rham コホモロジー |

## 位相幾何

[分野内の配置と依存の案内](topology/README.md)。

| 配置 | パッケージ | 内容 |
| --- | --- | --- |
| [topology/basic](topology/basic/README.md) | `topology` | 位相・部分空間、連続写像、コンパクト性、分離性 |
| [topology/metric](topology/metric/README.md) | `metric_spaces` | 距離位相、距離化、実数直線、実数値関数、有限従属分割 |
| [topology/clutching_linearization](topology/clutching_linearization/README.md) | `clutching_linearization` | Laurent 近似、companion 安定線形化、選択に依存しないスペクトル逆クラス、自然性・直和・基本積の相互逆 |
| [topology/k_theory](topology/k_theory/README.md) | `topological_k_theory` | 複素束の Grothendieck 環、安定同型判定、反変引き戻し、ランクと被約群、有限離散計算 |
| [topology/constructions](topology/constructions/README.md) | `topological_constructions` | 積、商、直和、貼り合わせ、compact-open 位相 |
| [topology/algebra](topology/algebra/README.md) | `topological_algebra` | 位相的代数、座標空間・行列位相、連続性判定 |
| [topology/homotopy](topology/homotopy/README.md) | `algebraic_topology` | ホモトピー、基点付き商、mapping cone、有限 CW 対、標準単体の座標 |
| [topology/fundamental](topology/fundamental/README.md) | `fundamental_groups` | 基本亜群・基本群、融合積の van Kampen の定理、単連結性 |
| [topology/coverings](topology/coverings/README.md) | `covering_spaces` | 被覆の持ち上げ、部分群・共役類による分類、普遍被覆と deck 変換 |
| [topology/singular/cohomology](topology/singular/cohomology/README.md) | `singular_cohomology` | 特異鎖・余鎖、相対・被約理論、ホモトピー不変性、道成分と可縮空間 |
| [topology/singular/subdivision](topology/singular/subdivision/README.md) | `singular_subdivision` | 重心細分、小鎖、開被覆と部分空間の比較 |
| [topology/singular/products](topology/singular/products/README.md) | `singular_products` | 特異余鎖とコホモロジーのカップ積、Leibniz 則、単位・結合・自然性 |
| [topology/singular/excision](topology/singular/excision/README.md) | `singular_excision` | 切除、Mayer–Vietoris、良い対と商空間の比較 |
| [topology/singular/eilenberg_zilber](topology/singular/eilenberg_zilber/README.md) | `singular_eilenberg_zilber` | Alexander–Whitney と shuffle の鎖ホモトピー同値 |
| [topology/singular/symmetry](topology/singular/symmetry/README.md) | `singular_symmetry` | カップ積の交換ホモトピーと次数付き可換性 |
| [topology/singular/cech](topology/singular/cech/README.md) | `singular_cech` | 被覆の二重複体と射影的複体の比較 |
| [topology/singular/simplicial](topology/singular/simplicial/README.md) | `singular_simplicial` | 有限単体複体の実現、アフィン特異鎖と積の比較 |
| [topology/singular/cellular](topology/singular/cellular/README.md) | `singular_cellular` | 有限 CW 複体のセル基底・付着次数、任意係数の比較と自然性 |
| [topology/singular/cellular_algebra](topology/singular/cellular_algebra/README.md) | `singular_cellular_algebra` | 相対鎖の直和、Hom と比較写像の補題 |
| [topology/singular/finite_algebra](topology/singular/finite_algebra/README.md) | `singular_finite_algebra` | 有限モデルとの係数比較、普遍係数と Künneth |
| [topology/singular/tensor_dual](topology/singular/tensor_dual/README.md) | `singular_tensor_dual` | 有限双対基底によるテンソル積と Hom の比較 |
| [topology/singular/tensor_bridge](topology/singular/tensor_bridge/README.md) | `singular_tensor_bridge` | 整数次数と非負次数のテンソル複体の比較 |
| [topology/singular/low_degree](topology/singular/low_degree/README.md) | `singular_low_degree` | 道の選択による鎖の正規化と積空間の一次コホモロジー |
| [topology/spheres](topology/spheres/README.md) | `sphere_maps` | 球面の向き、反転と円周の整数べき写像の次数 |
| [topology/examples/cohomology](topology/examples/cohomology/README.md) | `cohomology_models` | 空空間・可縮空間・球面の計算と相対理論の利用例 |
| [topology/examples/finite_models](topology/examples/finite_models/README.md) | `cohomology_examples` | 有限グラフ、トーラス、実射影平面の群・積・誘導写像 |

## 型検査

```sh
cargo run -p cli -- libs
cargo run -p cli -- libs/std --module std.Data.Nat
```

`libs/ref.toml` の workspace 全体で `libs/refcache/` を共有する。
再検査・資源制限・進捗は [利用方法](../src/USAGE.md#検査とキャッシュ) を参照。

具体例は [複体](algebra/homological/concrete_complexes/README.md)、[座標計算](geometry/coordinate_calculus/README.md)、[cell_spaces](topology/examples/cells/src/root.ref)、[スカラーの互換性](analysis/scalar_compatibility/README.md)、[小さい圏](category/src/SmallCategories.ref) と [終対象の圏の極限](category/src/TerminalLimits.ref) にある。

[特異コホモロジーの利用例](topology/examples/cohomology/README.md)は代表余鎖、相対接続、係数付き誘導写像、道成分と空空間・一点・区間の計算を検査する。
[有限モデルの利用例](topology/examples/finite_models/README.md)は空間との比較写像を使って群とコホモロジーの積を計算する。
