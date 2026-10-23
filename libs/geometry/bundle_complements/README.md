# 束の計量と射影表示（B03、進行中）

入口は `bundle_complements.Complements.Over[K, field, conjugation, scalar]` である。
[vector_bundles](../vector_bundles/README.md)、[bundle_operations](../bundle_operations/README.md)、[hermitian_frames](../../algebra/hermitian_frames/README.md) を再利用する。

`For[X, F, bundle].embeddingExists` はコンパクト Hausdorff 性から有限従属分割を構成し、重み付き局所座標の零延長と連結によって有限次元自明束への連続な単射を与える。
`FromPartition` は明示した有限分割にも適用でき、和が1であることから核が零であることを導く。
`For.metricExists` と `For.FromEmbedding.metric` は標準内積を引き戻した正定値な実・Hermitian 計量で、内積の全空間上の連続性を証明する。

`Finite.ProjectionBasis.basisExists` は射影された標準基底を順に正規直交化して像の有限基底を構成する。
`Projection[X, n, baseSpace, P, regular].bundle` は任意の連続な直交射影の像の束である。
`Around` は中心で恒等となる比較行列と連続な逆行列から局所自明化を作り、一定階数の追加仮定を使わない。
`inclusion` と `projectMap` は自明束への包含と自明束からの射影である。

`For.FromEmbedding.Image.projection` は埋め込みの像への一意な直交射影で、局所的な連続 Gram–Schmidt から行列族の連続性を証明する。
`Image.isomorphism` は元の束と射影の像の束を比較する。
`Finite.InverseFamily` は局所 Gram 座標と逆座標の族の連続性を与える。

## 検証と再開

実行環境の切断により、このブランチは未完了の退避スナップショットである。
会話に記録された書き込み内容から55個のソースファイルを復元しており、元の作業ディレクトリとのバイト単位の照合と、復元後の型検査は未実施である。

切断前には計量・有限分割の範囲で22 module・205ステップ、有限基底と射影の一意性で15 module・121ステップ、射影の像の束で24 module・244ステップの通常検査が受理された。
最後の比較同型を含む検査は55 module のソース検査完了を記録した後に終了処理へ入り、その最終結果を取得する前に環境が利用不能になった。

再開時の検査範囲は次のとおり。

```sh
target/debug/cli libs/geometry/bundle_complements --memory-mib 8192 --cache-stats
target/debug/cli libs --module bundle_complements --memory-mib 8192 --cache-stats
target/debug/cli libs --memory-mib 8192 --cache-stats
```

直交補束と自明束への直和同型、異なる周囲次元を含む束同型の同値関係と同型類の集合、引き戻しに対する自然性、実・複素の利用例、最終検証と完了時のロードマップ更新が残っている。
B03 の計画は未完了として保持している。
