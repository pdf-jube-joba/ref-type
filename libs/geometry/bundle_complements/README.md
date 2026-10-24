# 束の計量・直交補束と同型類

入口は `bundle_complements.Complements.Over[K, field, conjugation, scalar]`。
スカラーは [vector_bundles](../vector_bundles/README.md) の実・複素の実装を渡し、線形演算は [bundle_operations](../bundle_operations/README.md)、正規直交化と行列族の連続性は [hermitian_frames](../../algebra/hermitian_frames/README.md) を使う。

## 計量と有限埋め込み

`For[X, F, bundle].embeddingExists` は、コンパクト Hausdorff 底空間上の局所自明化に従属する有限分割を構成する。
`Weighted` は重み付き局所座標を台の外で零延長し、`build` は座標を連結する。
`FromPartition` は重みの和が1であることから核が零であることを証明する。
既存の `PartitionOfUnity` と `ZeroExtension` により、零延長の連続性も証明する。
周囲次元は有限個の局所次元の和であり、底の連結性や一定ランクを仮定しない。

`Embedding` は次元、連続な束写像、各ファイバー上の単射性をまとめる。
`FromEmbedding.metric` は標準内積を引き戻した正定値な実・Hermitian 計量で、直和束の全空間上の評価の連続性を持つ。
`metricExists` はこの構成を有限埋め込みに適用する。
`CoordinateEmbedding` は連続な単射行列族を、自明束間の実際の連続な束写像にする。

## 射影の像と直交補束

`Finite.ImageBasis[map, idempotent]` は一般の冪等な線形写像の列を順に処理し、その像を張る正規直交枠を構成する。
`Finite.ProjectionBasis` はこの共通構成を Hermitian 射影に適用し、座標による射影の再構成を導く。

| API | 構成と証明 |
| --- | --- |
| `Finite.ProjectionBasis.basisExists` | 射影された標準基底を順に正規直交化して像の有限基底を構成する。 |
| `Projection[X, n, baseSpace, P, regular].bundle` | 連続な直交射影の像の束。誘導位相と局所自明化の両方向の連続性を持つ。 |
| `Projection.Around` | 中心で恒等となる行列 \(P(x)P(a)+(I-P(x))(I-P(a))\) と連続な逆行列から局所座標を作る。一定階数の追加入力は不要。 |
| `Projection.inclusion` / `projectMap` | 像から自明束への包含と、自明束から像への射影。 |
| `Projection.Complement` | \(I-P\) の像の束、直交性、\(\operatorname{im}P\oplus\operatorname{im}(I-P)\cong X\times K^n\) と両逆。 |
| `For.FromEmbedding.Image` | 埋め込みの像への一意な連続直交射影と、元の束から射影の像の束への比較同型。 |
| `For.FromEmbedding.Complement` | 元の束の直交補束と、その直和から有限次元自明束への同型。 |

射影の一意性は `Finite.Range.unique`、行列族と局所逆座標の連続性は L01・L03 の API から導く。

## 集合による表示と自然性

`Representations[X, baseSpace].Presentation` は有限の周囲次元と連続な直交射影の組である。
`Realize[p].bundle` が像の束を構成する。
`Equivalent p q` はその二つの束の同型の存在であり、周囲次元が異なる場合も許す。
反射・対称・推移律を証明し、既存の `std.Set.Quotient` から同型類の集合 `Classes` を作る。
`classCriterion` は同型類の等式と束同型の存在の同値を与える。

`Of[F, original, same].class` はコンパクト Hausdorff 底空間上の一般の束の同型類である。
`Of.classification` は射影表示の実現との比較を、`Comparison.criterion` は一般の二つの束の同型と同型類の等式の同値を証明する。
類の定義はすべての同型な射影表示からなる部分集合で、埋め込みや枠の選択によらない。

`Projection.Pullback.isomorphism` は射影を合成した像の束と像の束の引き戻しを比較する。
包含・射影・補射影・直和同型の両方向についてファイバー上の可換性を証明する。
`For.Pullback.metric` は任意の連続な計量の引き戻しである。
`FromEmbedding.Pullback` は埋め込みを引き戻し、計量の評価式と像への射影の一致を証明する。
`Representations.Pullback.map` は同型類の集合への引き戻し写像、`onClass` は代表上の式、`Of.naturality` は一般の束の同型類との可換性を与える。

## 利用例

[Moving](src/Complements/Over/Examples/Moving.ref) は L03 の列 \((1,z)\) を再利用し、計量・直交補束・自明束への直和同型を構成する。
周囲次元1と2の表示が同じ類を定めること、二乗写像による引き戻し、計量・射影・類の自然性も使う。
[FiniteBases](src/Complements/Over/Examples/FiniteBases.ref) は二点離散空間のコンパクト Hausdorff 性を証明し、ランク0と1の束、零束、空の底上の束に有限埋め込みと計量の存在定理を適用する。
[Examples](src/Complements/Examples.ref) は実数・複素数のスカラーで具体化する。

## 検証

B03 は [PR #41](https://github.com/pdf-jube-joba/ref-type/pull/41) で main `6bf92837` に統合済みである。
復元コミット `5d993911` について、残存した元の55ソースと二つの manifest は Git blob hash まで一致することを確認した。
当時の環境切断の根本原因は不明である。

K06 では `Finite.ImageBasis` を切り出し、一般の冪等写像と Hermitian 射影で基底構成を共用した。
コミット `e3aecc2e` の B03 package と全依存閉包の再検査は終了コード0で、4,345 module をすべてキャッシュから再利用した。
ソース再検査・worker 復旧・重複・再実行・失われたステップ・保存失敗はすべて0である。
Rust の変更はない。

```sh
target/debug/cli libs/geometry/bundle_complements --memory-mib 8192 --cache-stats
```

K06 の workspace 全体の検査と再開情報は [spectral_splitting の引き継ぎ欄](../../algebra/spectral_splitting/README.md#検証と再開) にまとめる。
B03 に続く実装候補は B04・B05・B09・K01 である。
