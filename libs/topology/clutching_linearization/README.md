# clutching の安定線形化（K07、実装中）

入口は `clutching_linearization.Linearization`。
`Blocks` は二つの複素ベクトル空間の直和上で上下の剪断写像を構成し、係数の加法則・係数0での恒等性・連続族の各点で使う逆写像の両逆を証明する。

## 検証と引き継ぎ

ブランチは `math/k07-clutching-linearization`、開始点は main `744d501e`。
GitHub 連携で #42〜#45 の統合を確認済み、open PR の検索結果は空であった。
`Blocks` の剪断写像・Schur 分解・可逆な経路と、実成分の共通誤差幅を扱う `Uniform` を実装した。
K07 の Laurent 近似ホモトピー・安定線形化・スペクトル束への比較・自然性・相互逆・利用例と登録は残作業である。
`work/k07-foundations.source.json` の対象 module と参照先は `work/k07-foundations.report.json` で検査・保存完了、終了0。
コマンドは `target/debug/cli libs/topology/clutching_linearization --source-snapshot work/k07-foundations.source.json --module clutching_linearization --memory-mib 8192 --cache-dir libs/refcache --cache-budget-mib 12288 --diagnostics compact --time-limit-seconds 1800 --report-json work/k07-foundations.report.json`。
最初は旧 CLI のオプション不一致で終了2、現行 CLI の通常ビルドは終了0。
構文修正と半径補題の存在命題への修正後、現在の数学ソースは上記 snapshot と一致する。
この検査は package 全依存閉包・下流・最終検証とは別である。
最後に対象検査が成功したコミットは `616f96d1`。
`ComplexBounds`・`MatrixNeighborhoods.Perturbation` の追加と依存登録も `work/k07-neighborhoods.source.json` の対象検査で保存完了・終了0。
後者のコマンドは上記の snapshot・report 名を `k07-neighborhoods` に置き換えて実行した。
以後の `ComplexBounds` の補題追加と `Perturbation.Nearby` の行列ホモトピーは未検証である。
次は構成した可逆性の共通誤差幅を Laurent 近似とそのホモトピーへ接続する。
