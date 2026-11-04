# 大域的な横断的押し込みの検査記録

数学ソースは `827da4f87550e523586407535211346eb2126e24` である。
G04 全体の完成を表すものではない。

通常 checker を `cargo build -p cli --release --locked` で再ビルドし、以下を固定ソースで順次実行した。
すべて終了コード 0、結果は accepted である。

| 検査 | 検証済み | 新規検査 | 再利用 |
| --- | ---: | ---: | ---: |
| `manifold_gluing --full-check-local` | 1,356 | 177 | 1,179 |
| `manifold_gluing` の再利用 | 1,356 | 0 | 1,356 |
| `boundary_manifolds` 回帰 | 1,081 | 0 | 1,081 |
| `smooth_partitions` 回帰 | 581 | 0 | 581 |
| `manifolds` 回帰 | 628 | 0 | 628 |
| 通常のリポジトリ全体検査 | 11,884 | 0 | 11,884 |

checker の SHA-256 は `8b62b74b30fdef253447ba04042e1492b4dd87cb9972a0fde399abb69829bcd7`、Rust は `rustc 1.99.1 (58cf8f9c3 2026-10-13)` である。
全体検査は `python3 scripts/check_all.py --state-dir work/g04-global/repository --initial-memory-mib 12288 --memory-mib 12288 --cache-budget-mib 12288 --min-free-mib 512` で実行した。
所要時間は 347.926 秒、最大 RSS は 1,402,504 KiB、最大仮想メモリは 2,117,836 KiB であった。
保存失敗、破損キャッシュ読み出し、worker 回復はすべて 0 件であった。
対象 package の全ローカル検査では保存済み checkpoint の読み出しを 2 回記録したが、worker 回復と再検査ステップの喪失は 0 件である。

対象 package と全体検査の source snapshot の全ファイルを、対象コミットの Git blob と比較した。
対象 package の検査前後、および全体検査前後の snapshot はそれぞれ同一であり、ソースとの不一致は 0 件である。
全体 snapshot の SHA-256 は `9679f95750347aa7d17ab78807cacc2b4e902db4ff41c09bd7bb42e66e8e554a` である。
通常の全体検査で再利用した 11,884 対象は、現在の checker と各対象のソース・依存関係に対して検証された結果である。

[summary.json](summary.json) に正確なコマンド、終了コード、各検査の資源使用量と snapshot の対応を保存した。
[verification-reports.json.gz](verification-reports.json.gz) に各対象の検査・再利用情報を含む報告をまとめた。
