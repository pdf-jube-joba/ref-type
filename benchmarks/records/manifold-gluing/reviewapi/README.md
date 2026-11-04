# 公開された貼り合わせ包含と接錐の整合性の検査記録

数学ソースは `6a86d795259f91141069aeec1904ae8fadff45fe` であり、G04 全体の完成を表すものではない。
通常 checker を `cargo build -p cli --release --locked` で再ビルドした。
固定ソースで次の検査を順次実行し、すべて終了コード 0、結果は accepted である。

| 検査 | 検証済み | 新規検査 | 再利用 |
| --- | ---: | ---: | ---: |
| `manifold_gluing --full-check-local` | 1,882 | 672 | 1,210 |
| `manifold_gluing 再利用` | 1,882 | 0 | 1,882 |
| `boundary_manifolds 回帰` | 1,081 | 0 | 1,081 |
| `smooth_partitions 回帰` | 581 | 0 | 581 |
| `manifolds 回帰` | 628 | 0 | 628 |
| `通常のリポジトリ全体検査` | 12,379 | 0 | 12,379 |

checker SHA-256 は `8b62b74b30fdef253447ba04042e1492b4dd87cb9972a0fde399abb69829bcd7`、Rust は `rustc 1.99.1 (58cf8f9c3 2026-10-13)` である。
全体検査は `python3 scripts/check_all.py --state-dir work/g04-reviewapi/repository --initial-memory-mib 12288 --memory-mib 12288 --cache-budget-mib 12288 --min-free-mib 512` で実行した。
全体の所要時間は 363.098 秒、最大 RSS は 1,439,812 KiB、最大仮想メモリは 2,118,128 KiB であった。
保存失敗、破損キャッシュ読み出し、worker 回復はいずれも 0 件である。

対象 package と全体検査の前後の source snapshot はそれぞれ同一で、全ファイルが対象コミットの Git blob と一致した。
全体 snapshot の SHA-256 は `1f8e43d238ebd3758e36e43613d01153e1ca66f8fc10f8c27ff4dd2f468b753e` である。

[summary.json](summary.json) に正確なコマンド・終了コード・資源使用量・ソース対応を保存した。
[verification-reports.json.gz](verification-reports.json.gz) に個々の検査対象と再利用の報告を保存した。
