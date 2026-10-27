# B05 再開手順

基点 main: bd8fd86d5368968ff22e06f81beb5469bc348623。
専用 worktree: /workspace/ref-type-b05、ブランチ: codex/b05-grassmannians。
実・複素の射影と既存の有限基底による階数から Grassmannian の台を定義する作業を開始した。

```sh
cd /workspace/ref-type-b05
/workspace/ref-type/target/debug/cli libs/geometry/grassmannians --module grassmannians --full-check-local --cache-stats --diagnostics compact --time-limit-seconds 300
/workspace/ref-type/target/debug/cli libs/geometry/grassmannians --cache-stats --diagnostics compact --time-limit-seconds 300
```

グラフ座標、位相的性質、普遍束と引き戻し比較、安定化、直和、直交補、射影空間は未実装。

既存 API: `hermitian_frames.Hermitian.Over.At.OnProjection.Rank.HasRank`、`OnProjection.complement`、`At.Blocks.projection`、`bundle_complements.Complements.Over.Projection` と `Projection.Pullback`。
射影族の連続性・階数の局所一定性・グラフ座標を構成し、像束の API と接続する。
`topology/homotopy/src/Euclidean/Dimension/Compactness.ref` に実有限次元のコンパクト性があり、再利用可能性の調査が必要。

検査対象 commit `08599c12` の対象検査と依存込み検査は accepted。
詳細は benchmarks/records/grassmannians/README.md と JSON を参照。

射影の行列成分から誘導位相を定義し、成分の連続性から既存の射影像束へ接続した。Real モジュールの個別検査は成功。Complex と全体の検査、残る位相・座標・自然性の証明を続ける。

連続な局所正規直交フレーム、直交補束、階数1の射影空間・標準線束と補束、零次元の実・複素の具体的な点を追加した。各追加は通常検査で accepted。グラフ座標、コンパクト Hausdorff 性、安定化・直和・直交補の写像と引き戻し同型を継続する。

任意の連続写像について、普遍束の引き戻しと合成射影族の像束の同型を既存 API から公開し、通常検査は accepted。

連続な一定階数の射影族から Grassmannian への連続写像 `Family.map` とその連続性を証明し通常検査に成功。workspace の package 登録と公開一覧を追加した。

直和のブロック射影と、基底の直和による階数の加法を実・複素用に実装した。実の `grassmannians.Real.Sum` は通常検査で accepted。複素側・直和写像の連続性と束の比較を続ける。
