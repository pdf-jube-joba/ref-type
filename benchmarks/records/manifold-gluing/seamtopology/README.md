# 境界貼り合わせの商の位相の検査記録

数学ソースは `aae620b4f93eefb6fa748407b329fee4d039744e` であり、G04 全体の完成を表すものではない。

`cargo build -p cli --release --locked` で通常 checker を再ビルドした。
固定ソースで次の検査を順次実行し、すべて終了コード 0、結果は accepted である。

| 検査 | 検証済み | 新規検査 | 再利用 |
| --- | ---: | ---: | ---: |
| `manifold_gluing --full-check-local` | 1,494 | 309 | 1,185 |
| `manifold_gluing` の再利用 | 1,494 | 0 | 1,494 |
| `boundary_manifolds` 回帰 | 1,081 | 0 | 1,081 |
| `smooth_partitions` 回帰 | 581 | 0 | 581 |
| `manifolds` 回帰 | 628 | 0 | 628 |
| 通常のリポジトリ全体検査 | 12,016 | 0 | 12,016 |

checker の SHA-256 は `8b62b74b30fdef253447ba04042e1492b4dd87cb9972a0fde399abb69829bcd7`、Rust は `rustc 1.99.1 (58cf8f9c3 2026-10-13)` である。
全体検査は `python3 scripts/check_all.py --state-dir work/g04-seamtopology/repository --initial-memory-mib 12288 --memory-mib 12288 --cache-budget-mib 12288 --min-free-mib 512` で実行した。
全体の所要時間は 376.136 秒、最大 RSS は 1,413,000 KiB、最大仮想メモリは 2,117,832 KiB であった。
全体の保存失敗は 0 件、破損キャッシュ読み出しは 0 件、checkpoint 再開は 0 回、worker 回復は 0 回である。

対象 package の検査前後、および全体検査前後の source snapshot はそれぞれ同一である。
snapshot の全ファイルを対象コミットの Git blob と比較し、不一致が 0 件であることを確認した。
全体 snapshot の SHA-256 は `0519f626a16429ff55787347eacbcbe67e3f4419bd48b60ae6f0272e0ee05819` である。

[summary.json](summary.json) に正確なコマンド、終了コード、各検査の資源使用量、source snapshot とコミットの対応を保存した。
[verification-reports.json.gz](verification-reports.json.gz) に対象ごとの検査・再利用情報を含む報告をまとめた。
