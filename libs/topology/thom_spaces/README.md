# 円板束・球面束と Thom 商

C02 の実装中のパッケージである。
実・複素の計量束、計量変更の同相、直和の反復商、cofibration と特異理論の比較を構成している。
球面束を含む有限 CW 対のモデルの構成は未完了である。

## 円板束と基点

入口は `Thom.Over[K, field, conjugation, scalar].For[X, F, bundle].With[metric]`。
計量は `bundle_complements` の連続な正定値計量を使う。
`DiskBundle` と `SphereBundle` は、全空間の二乗ノルムの劣位集合・等位集合に誘導位相を入れたものである。
`diskProjectionContinuous`、`sphereProjectionContinuous`、`sphereInclusionContinuous` と零切断を公開する。

`Thom` は基点を加えた円板束で、球面束と追加した基点を一緒に潰した商である。
したがってランク0では \(X_+\)、空の底では一点となる。
`class`、`point`、`collapsed`、`quotientContinuous` が商の基本 API である。
`Thom.Collapse.Lift` は球面上で指定の基点となる連続写像の降下を与える。

## 比較

| API | 構成・証明 |
| --- | --- |
| `Thom.Real.For.Change` / `Thom.Complex.For.Change` | 任意の二つの連続計量に対する全空間・円板束・Thom 商の同相 |
| `Over.For.Change.sphereHomeomorphism` | スカラーを共通化した球面束の正規化同相 |
| `Thom.Real.Trivial.Compare` / `Thom.Complex.Trivial.Compare` | 自明束の Thom 商と実次元 \(n\)・\(2n\) の円板 suspension モデルの同相 |
| `Thom.Real.DirectSum.Compare` / `Thom.Complex.DirectSum.Compare` | 直和束の任意の計量の Thom 商と反復 Thom 商の同相 |
| `Over.For.With.Radial.Boundary.cofibration` | 球面境界包含の cylinder retraction |
| `Over.For.With.ThomPair.mappingConeComparison` | 基点を加えた対に対する `puppe_sequences.Pair.equivalence` の適用 |
| `Over.For.With.ThomPair.Collar` | 開いた半径近傍の強変形収縮と `goodPair` |
| `Collar.Homology[z].isomorphism` | 基点を加えた円板・球面対の整数相対ホモロジーから Thom 商の被約ホモロジーへの同型 |
| `Collar.Cohomology[M, z].isomorphism` | 任意の整数加群係数・整数次数での逆向きのコホモロジー同型 |
| `Over.For.With.Contraction.equivalence` | 円板束と底空間のホモトピー同値 |
| `Over.For.With.FiniteBase` | 底の有限 CW 複体を円板束のモデルにする `diskType` と、各セルの引き戻し束の自明化 |

計量変更の全空間写像は、零ベクトルを零へ、それ以外のベクトルを
\(v\mapsto \lVert v\rVert_h\lVert v\rVert_k^{-1}v\) へ送る。
`Quadratic.Over` は連続な正定値2次斉次ゲージに同じ構成を適用する。
ゲージには実数倍に関する2次斉次性を要求し、内積の二乗ノルムと円板積の最大値モデルを同じ API で扱う。
標準球面上の係数のコンパクトな局所有界性と `CompactAction` の tube lemma から、零ベクトルでの連続性も証明している。
複素の場合は既存の実化と実線形座標を使う。

直和の比較は \(\max(\lVert v\rVert^2,\lVert w\rVert^2)\leq1\) の円板積のモデルを経由する。
二つの境界を順に潰す商と、その和集合を一度に潰す商を `Thom.Iterated.homeomorphism` で比較する。
これは円板束上への引き戻しの相対 Thom 商の表示である。

`DiskSuspension[X, space, n]` は
\(((X\times D^n)\amalg\{*\})/(X\times\partial D^n\amalg\{*\})\)
という円板 suspension モデルである。
既存の `puppe_sequences.Suspension` の反復との形式的比較は未実装である。
相対特異理論の比較の始域は \((D(E)_+,S(E)_+)\) であり、追加した一点を除く \((D(E),S(E))\) との比較も未実装である。

## 例

[Examples.Real](src/Thom/Examples/Real.ref) と [Examples.Complex](src/Thom/Examples/Complex.ref) は、非コンパクトなスカラー直線を底として、B03 の動く埋め込みから作った計量と標準計量を比較する。
Thom 商の同相、球面境界の cofibration、実次元1・2の円板 suspension 表示を具体化する。
[Examples.Edges](src/Thom/Examples/Edges.ref) はランク0の球面束が空であることと、空の底の Thom 商のすべての点が基点に一致することを検査する。

## 残る証明

有限 CW 基底から得たセルごとの束自明化を、球面束を含む有限 CW 対のモデルと対のホモトピー同値へ組み上げる証明が必要である。
`FiniteBase.diskType` は円板束のモデルであり、有限 CW 対のモデルではない。
一般の有限 CW ホモトピー貼り合わせと必要な cellular approximation の API は、現行の依存パッケージには見つかっていない。
これは C02 の未実装範囲であり、処理系や体系による不可能性を主張するものではない。

検証記録は [C02 の記録](../../../benchmarks/records/c02-thom-spaces/README.md) を参照する。
