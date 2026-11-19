# Grassmannian の Schubert 座標と弱位相

B08 の途中実装である。
有限 CW 構造と向き付き Grassmannian の被覆は未実装であり、B08 は完了していない。
以下の定義と証明項を追加したが、型検査は時間上限に達しており、検証済みの API ではない。

## Schubert 記号と階段形

`Symbols[n, k].Symbol` は、0 始まりの狭義単調な pivot 列を持つ。
`Below` は成分ごとの順序で、反射性・推移性・反対称性を記述した。
`Free` は pivot ではない行のうち各列の pivot より手前にある成分を表す。
`realDimension` は \(\sum_i(p_i-i)\)、`complexDimension` はその2倍である。
`stabilize` は各 pivot を保ったまま周囲次元を1増やし、`stabilizationDimension` は上記の次元式が変わらないことを示す。
自由成分の個数と次元式の一致はまだ証明していない。

`Echelon[K, field, n, k, symbol].Carrier` は pivot 行が単位行列で、各列の pivot より後の成分が0である行列の集合である。
`linear` はその列の線形結合を取り、`coordinates` は pivot 行を読み出す。
`leftInverse` と `injective` は列の一次独立性を示す。
`containedUnique` は、同じ記号の二つの階段形について、一方の列空間が他方に含まれれば行列が等しいことを示す。
`Topological` は行列成分からの誘導位相と自由成分の連続性を提供する。

`Echelon.FreeCoordinates.fill` は任意の自由成分から階段形を構成する。
各成分について、自由成分・その列の pivot・残りの3場合を分けて値を定義し、既存の階段形の条件を満たすことを示す。
`readFill` と `fillRead` は自由成分の読み出しとの往復等式であり、`FreeCoordinates.Topological.homeomorphism` は積位相を持つ自由成分の空間との同相写像である。

`Real[n, k, symbol].parametrizationExists` と `Complex[n, k, symbol].parametrizationExists` は、既存の連続 Gram–Schmidt 法から直交射影族を作り、`grassmannians.Real.Model`・`Complex.Model` への連続単射を構成する。
`Parametrization.image` は、射影の固定部分空間と元の階段形の列空間が一致することを述べる。
連続な正規直交化の選択は存在量化し、呼び出し元には仮定させない。
`Real.Canonical`・`Complex.Canonical` は、直交射影が固定部分空間によって一意に決まることから正規直交化の選択に依存しない `map` を定義する。
`Canonical.cell` はその像であり、Grassmannian の部分空間位相を持つ。
`Canonical.Pivot` は pivot の標準座標平面とその基底を構成する。
`Canonical.Pivot.homeomorphismExists` は、その基準点での既存のグラフ座標を用いて、自由成分の空間からセルへの同相写像を構成する。
逆写像は、グラフ座標の正規化された列を読み出す写像であり、連続性も記述した。
任意の Grassmannian の点がいずれかの記号のセルに含まれることは未実装である。

## 周囲次元の包含

`AmbientReal[n, k, m]`・`AmbientComplex[n, k, m]` は、末尾に \(m\) 個の零座標を加える標準包含を階数 \(k\) のまま構成する。
既存の安定化の終域の階数 \(0+k\) を `RankTransportReal`・`RankTransportComplex` で \(k\) に移送し、行列成分と連続性が移送で保たれることを示す。
元のブロックへの制限が元の射影を復元することから単射性を示す。
`ClosedEmbedding` はコンパクト性と Hausdorff 性から像への同相写像と像の閉性を構成し、各 `Ambient` がこれを適用する。
これらの包含とセルの付着写像との比較は未実装である。

## 弱位相と有限段階化

`WeakUnion[X, stages, spaces]` は、各段階が同じ集合の部分集合として与えられた場合の弱位相を構成する。
開集合は、すべての段階への制限が開である集合である。
`Universal.continuous` は、この空間からの写像が連続であることと各段階への制限が連続であることを同値にする。

`Compact[ascending, exhaustive, separated].finiteStage` は、段階が増大し、全体を覆い、それぞれ T1 であるとき、弱位相に関するコンパクト集合がある段階に含まれることを述べる。
証明項では、どの段階にも収まらない集合から第 \(n\) 段階の外にある点 \(x_n\) を選ぶ。
各尾部 \(\{x_i:i\geq n\}\) と固定した段階との交わりは有限集合なので閉であり、その補集合が開被覆になる。
有限部分被覆は十分後ろの \(x_i\) を覆えず、コンパクト性に反する。

`Maps.boundedImage` はコンパクトな空間からの連続写像の像を有限段階に収める。
`Maps.Embedded[induced].exists` は、段階の位相が全体からの部分空間位相と一致する場合に、連続な有限段階への因子分解を返す。
`Spheres[d, induced].sphereMap` と `sphereHomotopy` は、それぞれ \(S^d\) と \([0,1]\times S^d\) のコンパクト性を使った特殊化である。
ホモトピー全体を一つの段階に収める。
この一般補題を Grassmannian の安定化極限に適用する具体的な集合・包含・位相比較は未実装である。

## B08 の残り

1. 自由成分の有限列挙と次元式の一致、任意の Grassmannian の点の階段形表示、異なる記号のセルの非交叉を証明する。
2. 各セルの閉円板からの特性写像を構成し、境界が低次元セルへ入ることを証明して、既存の `algebraic_topology.CW.FiniteComplex` を構成する。
3. 標準包含の胞体性と、向き付き Grassmannian の被覆に対する持ち上げた CW 構造を証明する。
4. 安定化の具体的な直極限を構成し、各有限段階の埋め込みを証明して有限段階化補題を適用する。

## 検査

提出時点の全ソースの構文検査は終了コード0。
型検査は初期実装に対して共有キャッシュ `libs/refcache` を使って実行し、300秒で終了要求、5秒の終了猶予後に強制停止された（終了コード137）。
合否判定と JSON レポートは得られていない。
その実行後に追加した有限段階化・自由座標の同相・包含の証明項も含め、提出時点の型検査は未完了である。
自由座標の同相・包含を追加した追補では、型検査を実行していない。

```sh
target/release/cli libs/geometry/grassmannian_cells --parse-only --diagnostics compact
timeout --signal=TERM --kill-after=5s 300s target/release/cli libs/geometry/grassmannian_cells --cache-dir libs/refcache --memory-mib 8192 --diagnostics compact --time-limit-seconds 300
```
