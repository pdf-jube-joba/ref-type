# Grassmannian の Schubert セルと CW 構造

B08 の要件に対応する定義と証明項を記述した。
実・複素の有限 CW 構造、標準包含による骨格の比較、実の向き付き被覆と持ち上げた有限 CW 構造、安定化極限と有限段階化を含む。
2026-11-20 に B08 本体の225モジュールと依存閉包7,852モジュールの型検査が成功した。
検証対象コミット、実検査とキャッシュ再利用の内訳、全体検査の結果は[検証記録](../../../work/b08-type-check/README.md)に記載する。

## Schubert 記号と階段形

`Symbols[n, k].Symbol` は、0 始まりの狭義単調な pivot 列を持つ。
`Below` は成分ごとの順序で、反射性・推移性・反対称性を記述した。
`Free` は pivot ではない行のうち各列の pivot より手前にある成分を表す。
`realDimension` は \(\sum_i(p_i-i)\)、`complexDimension` はその2倍である。
`stabilize` は各 pivot を保ったまま周囲次元を1増やし、`stabilizationDimension` は上記の次元式が変わらないことを示す。
`FreeCount.exists` は自由成分全体と \(\mathrm{Fin}(\sum_i(p_i-i))\) の全単射を構成する。
`FreeCount.cardinality` は任意の有限列挙の要素数がこの次元に等しいことを述べる。

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
`Reduction` は最大の非零行を選び、列の入れ替えと三角同型でその行を正規化して、階数を1減らす帰納法を記述する。
得られた pivot 列を並べ替え、元の単射線形写像と像が一致する階段形を返す。
`DecompositionReal`・`DecompositionComplex` は各射影の階数の基底にこれを適用し、セルの網羅性を与える。
`Echelon.Comparison` は像の包含から pivot 集合の包含を導き、有限順序集合の剛性から記号の一致を示す。
`DecompositionReal.disjoint`・`DecompositionComplex.disjoint` は異なる記号のセルの非交叉を述べる。
`Symbols.Enumeration` は記号の集合の有限性と重複しない列挙の存在を記述する。

## 周囲次元の包含

`AmbientReal[n, k, m]`・`AmbientComplex[n, k, m]` は、末尾に \(m\) 個の零座標を加える標準包含を階数 \(k\) のまま構成する。
既存の安定化の終域の階数 \(0+k\) を `RankTransportReal`・`RankTransportComplex` で \(k\) に移送し、行列成分と連続性が移送で保たれることを示す。
元のブロックへの制限が元の射影を復元することから単射性を示す。
`ClosedEmbedding` はコンパクト性と Hausdorff 性から像への同相写像と像の閉性を構成し、各 `Ambient` がこれを適用する。
`AmbientReal.CW`・`AmbientComplex.CW` は標準包含の骨格に関する `cellular` と `reflects`、および対応するセル上の `cellHomeomorphism` を公開する。
`CWReal.With.filtrationEquals`・`CWComplex.With.filtrationEquals` によって、この骨格が実際に構成した有限 CW 構造の骨格であることを比較する。

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
`StableReal[k]`・`StableComplex[k]` は、有限射影行列を自然数で添字付けた無限行列へ零で延長した像の合併を構成する。
`AmbientReal.Entries`・`AmbientComplex.Entries` は、この表示が標準包含と可換であることを示す。
各有限段階の逆写像は有限行列部分の読み出しから連続になり、`FiniteStage.homeomorphism` は元の有限 Grassmannian との同相を与える。
`weakTopology` は開集合を有限 Grassmannian への引き戻しで特徴付ける。
`WeakUnion.CommonTopology` により各段階が弱位相からも部分空間位相を持つことを示し、`Maps.exists`・`Spheres.sphereMap`・`Spheres.sphereHomotopy` は実際の有限 Grassmannian への連続な因子分解を返す。

## 有限座標と閉じたパラメータ空間

`FiniteIndex` は有限集合の相異なる列挙を有限添字集合との全単射へ変換する。
`Symbols.FreeEnumeration` は自由成分の有限性を、`Symbols.Column.indexExists` は第 \(j\) 列の自由な行と \(\mathrm{Fin}(p_j-j)\) の全単射を構成する。
`FiniteComplement` は単射の像を除いた有限集合の要素数を鳩の巣原理から計算する。
`Canonical.FiniteCoordinates.exists` はセルと有限個の実座標または複素座標との同相を返し、複素の場合の `realExists` は実次元を二倍にした座標との同相を返す。

`Symbols.Widen` と `Echelon.Widen` は標準包含に沿った記号と階段形を構成する。
`AmbientReal.Cells`・`AmbientComplex.Cells` の `agrees` は射影の包含とセル座標の可換性を、`homeomorphism` は対応するセル全体への同相を記述する。

`Reflection` は直交射影の像で符号を反転するユニタリ変換と、二つの反射を合成した連続な半球上の回転を構成する。
`Rotations` は自由成分を各列の閉球に制限し、これらの回転を順に合成する。
`diagonal`・`above` は合成後のフレームの階段状の支持を記述し、`boundaryPivot` は閉球の境界で対応する主成分が零になることを示す。
`Canonical.Characteristic.map` はそのユニタリ変換で座標平面の射影を共役した連続写像である。
`Characteristic.diskExists` はこのパラメータ空間と標準円板の同相を返し、境界と内部の条件を両方向に保存する。
`StandardDisk.map` はこの同相を既存の連続写像へ合成する。
`StandardDisk.interiorImage` は内部の像が対応するセルであることを、`interiorHomeomorphism` は内部への制限の同相を記述する。
`StandardDisk.cellLaws` は、閉円板のコンパクト性と Grassmannian の Hausdorff 性を使って既存の `CW.CellLaws` を構成する。

## 標準円板と内部の代数

`FinitePartition` は有限個の相異なるラベルの各ファイバーの全単射を足し合わせる。
`Symbols.FreeCount` はこれを各列の自由成分に適用する。
`FiniteCoordinates.Data.dimensionFormula` と複素の場合の `RealData.dimensionFormula` は、任意の要素数ではなく Schubert 次元との等式を返す。
`schubertExists` と `realSchubertExists` は、この次元を明示した同相を公開する。

`Rotations.Parameters` は自由成分を残りの成分が零である行列へ延長し、列のノルムの最大値をゲージとする。
`FiniteMaximumReal` は最大値の上界、最小性、到達、連続性と非負のスカラー倍を扱う。
`GaugeDisk` は既存の `thom_spaces.Thom.Quadratic` の動径変換と `Levels` を用い、正定値の二次同次ゲージの単位閉球を標準円板へ同一視する。
`Rotations.Parameters.Disk` はゲージの閉球と回転パラメータ空間との往復を構成する。
実の場合は自由成分の全単射、複素の場合はその実数化を用いて、`Characteristic.diskExists` の実次元をそれぞれ \(\sum_i(p_i-i)\) と \(2\sum_i(p_i-i)\) にする。

`Reflection.Hemisphere.Disk.Inverse` は半球の点から軸成分を引き、閉球への逆変換を構成する。
`TriangularGram` は既存の Gram–Schmidt の帰納法に階段状の支持と正の実主成分を加える。
`TriangularGram.At.Support` は、最大の非零係数を選ぶことで、像の支持より後の pivot に対応する係数が零になることを述べる。
`FrameComparison` は同じ像に入る二つの正規直交フレームの支持と正の主成分から、それぞれの列が等しいことを示す。
`Rotations.FromFrame` はフレームの最初の列を半球として読み、対応する回転を取り除いて帰納的にパラメータを復元する。
`Rotations.FrameInjectivity` は回転から得たフレームの一致からパラメータの一致を示す。
`Characteristic.interiorSurjective` は各セルの点に内部の原像を与え、`injectiveInterior` は内部での単射性を述べる。

## 境界と有限 CW 構造

`TriangularGram.At.FlagComparison` は、階段状の支持を持つ単射フレームを階段形へ変換した際、その pivot 列が元の記号以下になることを記述する。
最初の \(j+1\) 列がより高い pivot を持つと仮定し、その係数を最初の \(j\) 座標へ制限した単射を作ると、`Reduction.rankBound` に反する。
`EchelonComparison` と `FrameComparison` は、元のセルに戻った場合にはすべての主成分が正であり、パラメータが内部にあることを示す。
これにより境界では記号が真に小さくなる。
`Symbols.Dimensions.strict`・`complexStrict` は pivot の成分ごとの比較から総次元の狭義減少を導く。
`Characteristic.boundaryLower` は境界の各点に、その点を含む低次元のセルを返す。

`CompactCell` はコンパクトな標準閉円板から Hausdorff 空間への写像について、内部での単射性と内部の点のファイバーが内部にある条件から `CW.CellLaws` と内部の同相を構成する。
逆写像の連続性には、円板内の開集合の補集合の像が閉であることを使う。
`FiniteCW` は有限個のこのような特性写像から弱位相の条件を示す。
`CWReal.exists`・`CWComplex.exists` は Schubert 記号の有限列挙と特性写像を合わせ、仮定なしで既存の `algebraic_topology.CW.FiniteComplex` の存在を述べる。
内部の網羅性、非交叉、低次元の境界、弱位相をすべてこの構造へ渡す。

## 向き付き実 Grassmannian

`OrientedReal[n, k].Orientation` は、同じ平面の各正規直交フレームに対する符号の割り当てである。
`Change` は二つのフレームの座標変換を直交群の元として構成し、既存の `lie_groups.OrthogonalOrientation.determinantSign` を使う。
割り当ての整合条件は、フレームの変更に伴いこの行列式の符号を掛けることである。
`fromFrame` は一つのフレームと符号から割り当てを構成し、`reconstruct` はその逆を示す。
符号は \(\{+1,-1\}\) を用い、このモデルは階数0でも二つの符号の選択を保持する。

`Atlas` は既存の連続な局所正規直交フレームを用い、そのフレームでの符号の評価と基底への射影から位相を生成する。
`TransitionFamily.continuous` は変更行列の成分の連続性と既存の行列式の連続性を接続する。
`Atlas.In.homeomorphism` は各局所領域の逆像を領域と符号の積へ同一視する。
`covering` は既存の `covering_spaces.Projection.Covering`、`twoSheets` は各ファイバーと二つの符号との全単射の存在である。
異なる基点は基底の Hausdorff 性で、同じ基点上の二つの点は局所フレームでの符号で分離する。

`Lift` は閉円板上で連続な回転フレームを使い、各 Schubert 特性写像を符号ごとに持ち上げる。
`Lift.Cell` はその内部の同相と `CW.CellLaws` を構成する。
`OrientedReal.CW.exists` は記号と符号の有限列挙から持ち上げた有限 CW 構造を返す。
各セルの次元は基底のセルと同じであり、`CW.With.projects` は特性写像と被覆の射影の可換性を述べる。
`filtrationEqualsPreimage` は向き付き空間の各骨格が基底の同じ骨格の逆像であることを述べる。

## 型検査

ソースコミット `5deadd6563878d1a010b9b628b7e9d68229a9cfe` で B08 本体と依存閉包の検査が成功した。
最終ソースの通常 CLI は、依存込み1,206モジュールを正規キャッシュから受理した。
その後の新規ドライバー実行は依存閉包7,852モジュールを正規キャッシュを使用して検証し、すべて成功した。
最終ソースの全体実行でも B08 全225モジュールを実検査し、成功した。
新しい公理宣言や未証明のための置き換えは追加していない。

B08 単独の libs 全体検査は11,895 / 15,749モジュールを確認し、既知の G06 `tubular_neighborhoods` の名前解決エラーで停止した。
残る3,854モジュールは、この B08 単独の実行では未確認である。
G06 のソース修正を加えたローカル一時統合では13,276 / 15,750モジュールを確認した。
全体検査は容量不足で停止し、同一入力での再開後も別パッケージの証明でメモリ制限近くの処理が続いたため中断した。
残る2,474モジュールは未確認であり、一時統合でも libs 全体の成功は確認していない。

実行コマンド、ローカル一時統合のコミットと件数、最初の診断、圧縮した生の report とログは[検証記録](../../../work/b08-type-check/README.md)にまとめた。
