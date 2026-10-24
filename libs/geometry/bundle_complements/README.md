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

復元コミット `5d993911` をリモートから取得し、残存した元の55ソース、package manifest、workspace 登録の57ファイルが Git blob hash まで一致することを確認した。
元の作業は stash に保存し、復元コミットへ fast-forward した。
環境切断の根本原因は不明である。

検証済みコミットは `1fd5d9f6`。
`target/debug/cli libs --module bundle_complements --memory-mib 8192 --diagnostics compact --report-json work/b03-resume-restored.json --cache-stats` は終了コード0、535 module を共有キャッシュから再利用して受理された。
切断前の比較同型を含む検査の受理済みレポートも残存したが、今回の終了コード付き再検査を確認の基準とする。
直交補束と自明束への直和同型の検査も終了コード0、58 checked・584ステップ・491 reused で受理された（同じコマンド、report は `work/b03-complement-check.json`）。
同型類の最初の検査は終了コード1（非公開 import alias の参照）となり、参照を修正して再検査中である。
同型類・自然性は構文参照を修正して再検査中である（先行検査は終了コード1）。
同型類・自然性・連続行列族からの埋め込み、および実・複素の動く直線、異なる周囲次元、零・空・可変ランクの利用例を追加した現在の変更は未検証である。

次は直交補束と自明束への直和同型を実装・検査し、同型類の集合、引き戻しの自然性、実・複素・零階数・空基底・可変階数の利用例を完成させる。
最終的に次を共有キャッシュで実行し、下流リンク・ロードマップを更新する。

```sh
target/debug/cli libs/geometry/bundle_complements --memory-mib 8192 --cache-stats
target/debug/cli libs --module bundle_complements --memory-mib 8192 --cache-stats
target/debug/cli libs --memory-mib 8192 --cache-stats
```
