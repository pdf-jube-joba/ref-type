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

直和写像の連続性を実装中。`Real.DirectSum` の個別検査を work/b05-directsum.log に実行し、終了コードと診断を確認してから修正する。実・複素ともこの段階では未検証。

直和写像 `Real.DirectSum` の連続性は個別検査で accepted。複素側、全体、直和束の比較は未検査・未完了。

80281272 の対象 full-check-local は accepted。workspace 全体の通常検査は300秒で未完了。対象依存閉包の通常検査を別途行った。グラフ表示を記述する Graph の途中実装を追加し、個別検査で診断を確認する。

Graph は基準点近傍での正規化、像の復元、グラフ項が基準像に直交することを証明。実側の個別検査は accepted、複素側と全体の再検査が必要。Graph の逆写像と位相同型、直和束の比較、直交補と安定化、コンパクト Hausdorff 性が残る。

Graph の基準座標・直交グラフ項・復元に加え、正規化行列とグラフ項の連続性を追加し、実側個別検査は accepted。複素側と全対象を再検査する。

グラフ項を線形写像 `graphMap` として公開し、値の式と連続性を実側で検査済み。複素側と全体の検査を続ける。

射影の内部レコードの等値性を避けるため `Real.Model` / `Complex.Model` に、明示的な写像データと射影・階数の条件から成る別表現を追加した。`entriesInjective` は行列成分が点を区別することを証明する。実側個別検査は accepted。既存の公開表現との統合と Hausdorff 性・コンパクト性の証明が必要。

行列成分が点を分離する表現について、スカラー空間の Hausdorff 性から点の分離を導く証明を追加中。実側の個別検査を `work/b05-hausdorff.log` に実行中で、終了・診断を確認する。`uniform_approximation` の既存の連続写像による分離補題を利用する。

明示的写像データを台とする Model について、行列成分による単射性、スカラーの Hausdorff 性からの分離、および実・複素双方の Hausdorff 性を実装した。実分離モジュールと複素 Model の個別検査は accepted。これらは従来の Grassmannian とは別の型であり、API の統合と元の束・写像の移行が必要。

Model に普遍束・補束と元の型への連続写像、元の型からの連続写像、Model に戻る合成の恒等性を追加し、実側個別検査で accepted。元の型に戻る合成の等式は未証明。

直和を Model 上に移し、元の直和と二方向の連続写像を合成して連続性を証明した。実 Model.DirectSum の個別検査は accepted。階数1の射影空間は Model を台とするよう切り替えた。複素側と全体の検査が必要。

8054ce96 の対象 full-check-local は accepted（28 module、464 steps）、対象依存閉包は accepted（578 module 再利用）。キャッシュ保存失敗0。

Examples に任意次元の恒等射影の点を追加し、階数1の実・複素射影空間の具体的な点を個別検査で確認した。

Model に任意の連続写像による普遍束の引き戻し同型と、開近傍上の連続な直交グラフ表示・像復元を接続した。実側の個別検査は accepted。複素側と全体の検査を行う。グラフ座標の逆構成と同相性は未完了。

Model.Graph で、像を直交補への線形写像として表し、その連続性と単射性を Range.unique から証明した。実側個別検査は accepted。グラフからの逆写像・全射性・逆写像の連続性は残る。複素側と全体を再検査する。
