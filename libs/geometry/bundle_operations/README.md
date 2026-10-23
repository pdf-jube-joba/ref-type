# 束の貼り合わせと線形演算

`bundle_operations.Operations.Over` は [vector_bundles](../vector_bundles/README.md) の実・複素束に対する貼り合わせと線形演算を構成する。
スカラー、位相、局所枠には同じ `K, field, conjugation, scalar` を渡す。
全空間の位相と局所自明化を構成し、束写像・束同型の連続性と逆写像を証明する。

## Cocycle と表示の比較

`Cocycle[X, I, baseSpace, domain, dimension].With[cocycle]` は通常の遷移関数と恒等・合成則を受け取る。
ファイバー `Fiber x` は、点を含むすべての座標で遷移関数に適合する座標族である。
`At.Frame` の評価と座標族の組み立てが互いに逆であることを証明する。
`Continuous` は領域の開性、被覆、重なり上の遷移関数の連続性であり、`regular` と `Construction.bundle` が実際の全空間と局所自明化を作る。
`Atlas` と `Final` が座標写像から終位相を構成し、その普遍性と開部分空間への制限を証明する。

`CocycleFromAtlas` は与えられた束の枠から遷移関数を取り出す。
`WithCover.isomorphism` はその cocycle から再構成した束と元の束を比較する。
被覆を変更する `With.Refine` と、細分と枠変更を同時に行う `With.Reframe.Using` は、新しい cocycle、貼り合わせた束、比較同型と `transitionFormula` を公開する。
枠変更 \(g_j\) に対する新しい遷移関数は \(g_k\tau_{\rho(j),\rho(k)}g_j^{-1}\) である。
`ChartRestriction`、`GaugeChart`、`CoordinateGauge`、`AtlasChange` は既存の束のチャートにも適用できる。
`ScalarGauge.regular` は連続な非零スカラーの族による枠変更の両方向の連続性を証明する。

## 線形演算

| API | ファイバー・位相と公開する写像 |
| --- | --- |
| `DirectSum` | ファイバーの積、全空間の積への誘導位相、射影、`Of.From.pair`、`Of.Inclusions`、`Of.To.copair` と各普遍性 |
| `Tensor` | 既存の代数的テンソル積、有限個の純テンソルの和からの終位相、`Of.Pure`、連続双線形写像に対する `Of.Universal` と一意性 |
| `Dual` | 既存の線形汎関数、連続局所切断による評価で生成する位相、`Pairing` と反変な `Contramap` |
| `Hom` | 既存の線形写像そのもの、`Of.tensorHom` による \(E^*\otimes F\) からの位相の移送、連続な `Of.Evaluation` と `Of.Mapping` |
| `Exterior[k]` | \(E^*\) 上の交代 \(k\) 形式、局所切断の組による評価位相、共変な `Mapping` と連続な `Wedge` |
| `Scalars.Realification` | 複素ファイバーの実スカラーへの制限、元の全空間との同相、実部・虚部の座標 |
| `Scalars.Complexification` | \(E\otimes_{\mathbb R}\mathbb C\)、実テンソル積から構成した複素スカラー作用、有限和からの終位相 |

`Mapping`、`Contramap`、実化・複素化の `Maps` は入力された連続な束写像から連続な束写像を構成する。
`Hom.Of.Mapping.evaluation` は \(h\mapsto b\circ h\circ a\) の評価式を証明する。
`Tensor.Of.Parametric` は底と入力の両方が変わる線形作用の連続性を有限個の基底上の検査に還元し、テンソル結合同型と Hom の評価に使う。
`Tensor.Of.Pure.Along`、`Dual.Pairing`、`Exterior.Wedge` は任意のパラメータ空間上の連続なベクトル族にも適用できる。
`Exterior.Mapping.WedgeNaturality` は束写像による外積の自然性を証明する。

各演算の `Pullback.isomorphism` は、演算した束の引き戻しと引き戻した束の演算を比較する実際の束同型である。
二変数の演算では `Of[same].Pullback` を使う。
実化・複素化を含め、比較の両方向は各ファイバーで恒等写像であり、局所枠の整合から両方向の連続性を証明する。

## 局所モデルと整合性

`CoordinateSum` は座標の連結・分割を与える。
`TensorFrame` は純テンソルを座標係数の積に移し、有限和による逆写像を証明する。
`DualFrame` は双対基底での評価、`TensorHom.Finite` は有限次元のテンソルと線形写像の同型を与える。
`AlternatingFrame` は狭義増加な添字の組による交代形式の係数と復元を与える。
`Scalars.RealCoordinates` と `ComplexTensor.Finite` は通常の実化・複素化の座標との同型と連続性を証明する。
各束の `In` はこれらのモデルを実際の局所自明化として用い、零次元と空の添字集合も含む。

`DirectSumAssociator`、`DirectSum.Of.Symmetry`、`DirectSumUnit`、`DirectSumRightUnit` と、対応する `Tensor` の同型を公開する。
`DirectSumPentagon`・`TensorPentagon`、`DirectSumHexagon`・`TensorHexagon`、その `OppositeHexagon`、`DirectSumTriangle`・`TensorTriangle` は合成した束同型どうしの等式を証明する。
`UnitAtBase` は等しい底位相の上で選んだ零束・標準一次元束との比較も明示する。
`DirectSumIsomorphisms` と `TensorIsomorphisms` は二つの束同型から演算後の束同型を作る。
`SymmetryNaturality`、`AssociatorNaturality`、`UnitNaturality`、`TensorDistributionNaturality` は束写像との可換性を写像の等式として証明する。
`TensorDistribution` は \(E\otimes(F\oplus G)\cong(E\otimes F)\oplus(E\otimes G)\) を、射影・包含と純テンソル上の式から構成し、両逆を証明する。
`TensorRightDistribution` は交換同型による比較を通して右分配を構成する。

## 利用例と検査

[Over.GaugeExample](src/Operations/Over/GaugeExample.ref) は実直線上の自明束を、全直線と正の半直線に細分し、一方の枠を連続な非定数の非零スカラーで変更する。
新しい遷移関数から貼り合わせた束と元の束の比較同型を作る。
[Over.Examples](src/Operations/Over/Examples.ref) はこの表示の束に直和・テンソル・双対・Hom・外冪を適用し、二乗写像に沿う引き戻しとの比較、Hom の評価、結合同型の自然性を使用する。
零束とのテンソル、零次外冪、二つの成分でランクが異なる束のテンソル、空の底空間上の直和も構成する。
[Operations.Examples](src/Operations/Examples.ref) は実・複素の両方で例を具体化し、実化・複素化の引き戻し同型も使用する。

```sh
cargo build -p cli --locked --offline
target/debug/cli libs/geometry/bundle_operations --memory-mib 8192 --cache-stats
target/debug/cli libs --module bundle_operations --memory-mib 8192 --cache-stats
```

対象と依存閉包の4,265 module の検査が成功し、新規271 module・3,430ソース検査ステップを検査して3,994 module のキャッシュを再利用した。
最大 RSS は約4,843 MiB、worker は1で、復旧・重複・再実行・失われたステップ・キャッシュ保存失敗はすべて0であった。
workspace からの `--module bundle_operations` は738 module を再利用し、workspace 全体も70 package・7,247 module をすべて再利用して成功した。
これらの最終検査はソース再検査0ステップで、復旧・重複・再実行・失われたステップ・キャッシュ保存失敗はすべて0であった。
