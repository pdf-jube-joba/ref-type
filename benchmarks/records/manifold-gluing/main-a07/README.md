# A07 を含む main との統合検査

A07 の PR #71 をマージした main `0eb04199d9470eb2bfbd0757192aeedfc99fd9e1` を G04 ブランチへ取り込んだ。
競合はなく、統合ソースは `c8b0a074d71c8f091edca1978668934ae88e1d19` である。
通常 checker を `cargo build -p cli --release --locked` で再ビルドし、固定ソースで以下の検査がすべて accepted・終了コード 0 となった。

| 検査 | 検証済み | 新規検査 | 再利用 |
| --- | ---: | ---: | ---: |
| G04 全ローカル検査 | 2,010 | 800 | 1,210 |
| G04 再利用 | 2,010 | 0 | 2,010 |
| G03 回帰 | 1,081 | 0 | 1,081 |
| G01 回帰 | 581 | 0 | 581 |
| manifolds 回帰 | 628 | 0 | 628 |
| A07 fourier_l2 回帰 | 992 | 201 | 791 |
| 通常のリポジトリ全体検査 | 12,529 | 0 | 12,529 |

checker SHA-256 は `8b62b74b30fdef253447ba04042e1492b4dd87cb9972a0fde399abb69829bcd7`、Rust は `rustc 1.99.1 (58cf8f9c3 2026-10-13)` である。
全体検査はメモリ上限・cache 予算とも 12,288 MiB、最小空き容量 512 MiB で実行した。
全体検査の所要時間は 383.341 秒、最大 RSS は 1,449,840 KiB、最大仮想メモリは 2,118,128 KiB である。
保存失敗 0 件、破損読み出し 0 件、worker 回復 0 件、checkpoint 再利用 0 件である。

`focused` は保存失敗 0 件、破損読み出し 0 件、worker 回復 0 件、checkpoint 再利用 3 件である。

`reuse` は保存失敗 0 件、破損読み出し 0 件、worker 回復 0 件、checkpoint 再利用 0 件である。

`regression-boundary_manifolds` は保存失敗 0 件、破損読み出し 0 件、worker 回復 0 件、checkpoint 再利用 0 件である。

`regression-smooth_partitions` は保存失敗 0 件、破損読み出し 0 件、worker 回復 0 件、checkpoint 再利用 0 件である。

`regression-manifolds` は保存失敗 0 件、破損読み出し 0 件、worker 回復 0 件、checkpoint 再利用 0 件である。

`regression-fourier_l2` は保存失敗 0 件、破損読み出し 0 件、worker 回復 0 件、checkpoint 再利用 1 件である。

対象検査と全体検査の前後の source snapshot はそれぞれ同一で、全ファイルが統合ソースの Git blob と一致した。
全体 snapshot SHA-256 は `ea0088dff29e2a918b780514894a15cdefff66c6f5f8bfc6a65b6d55ff96022a` である。
[summary.json](summary.json) に正確なコマンド・終了コード・資源使用量・ソース対応を、[verification-reports.json.gz](verification-reports.json.gz) に個々の検査対象と新規・再利用結果を保存した。
