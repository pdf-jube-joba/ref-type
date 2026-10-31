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

`Framed.For.class` は枠付き束の分類クラスを公開し、`classification` と `independent` は埋め込みから得た有限表示が同じクラスを定めることを示す。
有限表示との比較同型と枠の保存は従来どおり `For.FromEmbedding.isomorphism` と `preservesFrame` にある。
`Framed.Addition.add` は `FrameSum.presentation` を商に降ろした直和で、`onClasses` は有限行列による表示との一致を証明する。
`Framed.Addition.For.naturality`、`Framed.Stabilization.For.naturality`、`Framed.For.Pullback.naturality` は束の分類クラスからこれらの有限表示への可換性を与える。
枠付き束の分類クラスは一つなので、これらの商写像の well-definedness には既証明の `uniqueClass` を用いる。

`Oriented.WhitneySum` は階数 \(k,l\) の二つの実束の向きから、直和束の標準の積向き `orientation` を構成する。
向きの入力は二つの因子の向きであり、直和全体の向きは構成の結果である。
この構成に底空間のコンパクト性や大域枠は必要ない。
`Oriented.Trivial.orientation` は座標の正規化された最高次形式で定める標準の向きで、`Oriented.StandardStabilization.orientation` はこの自明束を付加する積向きである。
階数0も同じ定義と証明で扱う。

有限次元の比較 `DeterminantProduct.product` は、\(\alpha\in\Lambda^k E^*\)、\(\beta\in\Lambda^l F^*\) から、左右の引数に対して
\[
 (\alpha\mathbin{\boxtimes}\beta)((u_1,0),\ldots,(u_k,0),(0,v_1),\ldots,(0,v_l))
 =\alpha(u_1,\ldots,u_k)\,\beta(v_1,\ldots,v_l)
\]
を満たす唯一の最高次形式を構成する。
既存の `FiniteCoordinates.Top` の正規化・一次元性と、引数の制限の補題から存在と一意性を示す。
`independent` は基底の選択独立性、`Laws` は双線形性と非零性、`Mapping.naturality` は線形写像に沿う引き戻しとの可換性を与える。
`Blocks.blockDeterminant` は、正規化された最高次形式で定めるブロック対角写像の行列式が二つの因子の行列式の積になることを証明する。

直和の正の半直線は、正の因子形式二つの積の集合として定義する。
`WhitneySum.Open.open` は、階数に合う局所自明化の上で正の局所形式を延長し、連続な係数の積による正の開半直線を貼り合わせて開性を証明する。
非零性、各ファイバーでの存在、正負の分離、正のスカラー倍、同一半直線の条件も証明して `Orientations.Orientation` を構成する。
`WhitneySum.Pairing.continuous` は二つの行列式束のファイバー積上で、この双線形な積そのものが連続であることを証明する。
局所自明化で最高次形式の全座標が基底での評価に等しいことを示し、積の座標を二つの連続な係数の積として構成する。

| API | 標準の積向きに対する整合性 |
| --- | --- |
| `WhitneySum.Mapping.With.preserves` | 因子の向きを保つ二つの束同型の直和が、構成した積向きを保つ |
| `WhitneySum.Pullback.naturality` | 引き戻した二つの向きの積と、積向きの引き戻しが標準の束比較で一致する |
| `WhitneySum.Classifying.WithSum.naturality` / `homotopy` | 因子の有限分類を行ってから直和する構成と、元の向き付き直和の分類のクラスが一致し、実際の向き付きホモトピーで結ばれる |
| `Classifying.WithSum.Changing.independent` / `ChangingSource.independent` | 因子と直和束の有限分類データの選択によらない |
| `StandardStabilization.Classifying.WithSum.naturality` / `homotopy` | 標準の向き付き自明束の付加と分類の可換性 |

`WhitneySum.classificationExists` と `StandardStabilization.classificationExists` は、コンパクト Hausdorff 底空間で必要な有限分類データが存在することも公開する。

`Oriented.Sum.With` は、二つの通常の有限分類データ、元の直和束に与えた行列式の向き、およびその直和束の分類データを受け取る。
因子の分類束の直和への比較同型 `Sum.comparison` を構成し、`targetOrientation` は与えた向きをこの同型に沿って輸送する。
`determinantNaturality`、`isomorphism`、`naturality` は、向きの輸送と分類との可換性を、行列式の等式、向きを保つ同型、分類クラスの等式として公開する。
向きを保つことを入力の仮定には要求しない。
`With.Changing.independent` は因子の分類データを変更しても分類クラスが一致することを証明する。
`Oriented.Stabilization.With.naturality` は自明束を付加する場合の同じ比較である。
これらの API の向きの入力は直和束全体の向きである。
標準の積向きを構成する場合は上記の `WhitneySum` と `StandardStabilization` を使う。

[最小利用例](src/Classification/Examples/BoolLine.ref) は二点離散空間上の実線束を分類する。
[自明束の例](src/Classification/Examples/Trivial.ref) は任意の底空間と次元で、有限分類写像、普遍束との同型、枠族の安定化ホモトピーを検査する。
同じ例の `Naturality.sumNaturality` と `stabilizationNaturality` は、枠付きの分類 API に対する直和・安定化の自然性の利用例である。
`Naturality.Oriented.volumePositive`、`sumNaturality`、`stabilizationNaturality` は、標準の向き付き自明束を用いた同じ整合性の利用例である。

```ref
\import bundle_classification.Classification[].Examples[].BoolLine[] \as Example;
```

通常検査の記録は [検査記録](../../../benchmarks/records/bundle-classification/README.md) にまとめる。
