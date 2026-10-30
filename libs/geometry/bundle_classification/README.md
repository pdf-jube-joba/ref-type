# 束の分類写像と安定化（B06）

コンパクト Hausdorff 空間上の有限階数実・複素ベクトル束を、有限次元の射影族から分類する。
[B03](../bundle_complements/README.md) の有限埋め込みと像射影、[B04](../bundle_homotopy/README.md) の束のホモトピー不変性、[B05](../grassmannians/README.md) の有限 Grassmannian と普遍束を使う。
新しい公理は追加していない。

## 分類写像

入口は `Classification`。
`Over` は実・複素に共通する構成で、スカラーの引数は既存の `vector_bundles` と同じである。

| API | 内容 |
| --- | --- |
| `Over.For.AtRank.exists` | コンパクト性、Hausdorff 性、階数 \(k\) の証拠から有限次元の分類データと比較同型を構成する |
| `Real.From` / `Complex.From` | 分類データから B05 の `Model.Carrier` への連続写像と、普遍束の引き戻しへの束同型を構成する |
| `Over.For.Graded.exists` / `From` | 階数が底空間の成分で変わる束の分類写像を構成する |
| `Over.ProjectionSpace` | 一つの有限次元空間内の全階数の直交射影の空間と普遍像束 |
| `RealGeometry.Finite` / `ComplexGeometry.Finite` | Grassmannian への連続写像を射影表示へ送る |
| `RealGeometry.Between` / `ComplexGeometry.Between` | 同型な階数 \(k\) の射影像束から、固定階数の有限 Grassmannian 内の安定化ホモトピーを作る |

`AtRank.HasRank` は各ファイバーが \(k\) 次元であるという条件であり、連続な大域枠の存在は要求しない。
階数が変わる場合は `Graded` を使う。
有限次元空間内の全階数の射影を対象とし、一定階数の場合には B05 の Grassmannian へ写る。

## 選択独立性と全単射

`Over.On[X, baseSpace].Between[p, q].Witness` は、周囲次元を二つの表示の次元の和に増やし、\(p\) を左ブロック、\(q\) を右ブロックに零成分で埋めた射影族を結ぶ連続な射影ホモトピーである。
`Witness.start` と `end` は実際の射影行列の一致を述べる。
束同型を関係の定義に使っていない。

同型が与えられたときは二つの埋め込みを
\[
 v\longmapsto ((1-t)e(v),t f(v))
\]
で結び、各像への直交射影を取る。
二つの係数の和が1なので各時刻で単射になる。
逆向きは B04 の射影族のホモトピー不変性を使う。
したがって `On.Compact.criterion` は、この安定化ホモトピーと束同型の存在の同値を与える。
有限段階の固定された周囲次元での分類や、二つの束自体を安定同型で同一視する主張とは区別する。

`On.Compact.toBundles` と `fromBundles` は、安定化ホモトピー類と B03 の束同型類の間の全単射である。
`leftInverse`、`rightInverse` が両方向の往復を証明する。
`On.Compact.For.classification` と `classCriterion` は分類写像や埋め込みの選択によらない同型判定を与える。

## 向き付き束と枠付き束

`Oriented` は実束の行列式余接線束 \(\Lambda^k E^*\) の開いた正の半直線を向きとして扱う。
`Orientations.Laws` は非零性、各ファイバーでの存在、正負の分離、正のスカラー倍と同一半直線の条件を含む。
`Oriented.For.With.exists` は与えられた向きを分類射影の像束へ移し、向きを保つ比較同型も返す。
`With.Compare.independent` が分類データの選択独立性を証明する。

`Oriented.On.Compact.Between.Homotopy` は、階数一定の射影ホモトピー、円筒上の連続な向き、零成分による両端の標準埋め込みとの向きの一致からなる。
`criterion` はこのホモトピーと向きを保つ束同型の存在の同値である。
`Classes` と `BundleClasses` の全単射には、通常の束の場合と同じ `toBundles`、`fromBundles`、両逆写像の証明を用意した。
向きの不変性は B04 の円筒上の同型と、非零の行列式余接ベクトルの連続経路に沿って正負が変わらない `Orientations.Path.endpoints` から示す。

`Over.Frames[n, k]` は \(k\) 個の独立な列ベクトルの有限 Stiefel 空間である。
`Over.Framed.For` は大域枠を備えた束からこの空間への連続写像と、枠を保つ比較同型を構成する。
`Framed.Between.concordance`、`homotopy`、`leftFormula`、`rightFormula` は任意の二つの枠族の安定化ホモトピーを与え、`preservesFrame` は対応する同型が枠を保つことを示す。
大域枠付きの階数 \(k\) の束の同型類と安定化 Stiefel ホモトピー類はいずれも一つであり、`Framed.uniqueClass` が後者を証明する。

## 自然性と例

- 通常の分類では `On.Compact.Pullback`、`On.Compact.Hausdorff.Sum.naturality`、`Hausdorff.Stabilization.For.naturality` が引き戻し、直和、自明束の付加との可換性を与える。
- 向き付き分類の引き戻しは `Oriented.On.Pullback` と `Oriented.On.Compact.Pullback` が扱い、行列式の半直線も輸送する。
- 枠付き分類では `Framed.Pullback`、`FrameSum`、`FrameStabilization` が枠行列の合成、ブロック直和、恒等枠の付加を構成する。
- Grassmannian の直和・周囲次元安定化・階数安定化の連続写像と普遍束比較は B05 の `Model.DirectSum` と `Model.Stabilization` もそのまま使える。

[最小利用例](src/Classification/Examples/BoolLine.ref) は二点離散空間上の実線束を分類する。
[自明束の例](src/Classification/Examples/Trivial.ref) は任意の底空間と次元で、有限分類写像、普遍束との同型、枠族の安定化ホモトピーを検査する。

```ref
\import bundle_classification.Classification[].Examples[].BoolLine[] \as Example;
```

通常検査の記録は [検査記録](../../../benchmarks/records/bundle-classification/README.md) にまとめる。
