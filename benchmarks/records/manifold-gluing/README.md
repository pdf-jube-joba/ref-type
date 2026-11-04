# G04 の局所基礎の検査記録

大域的な横断的押し込みの検査は [global/README.md](global/README.md)、半空間の局所逆写像を追加した後の検査は [halfspace/README.md](halfspace/README.md)、大域 collar 同相の検査は [embedding/README.md](embedding/README.md) にある。

この記録の数学ソースは `8b314683331496400104d0de8cb29f7c0a500f90` であり、G04 全体の完成を表すものではない。
基点は `ed1af945bfdfdc1849bf1919317e3ce422b1ac1f` である。

`cargo build -p cli --release --locked` で通常 checker を再ビルドした。
Rust は `rustc 1.99.1 (58cf8f9c3 2026-10-13)`、checker の SHA-256 は `8b62b74b30fdef253447ba04042e1492b4dd87cb9972a0fde399abb69829bcd7` である。
数学ソースを固定したまま以下を順次実行し、すべて終了コード 0 で完了した。

| 検査 | 検証済み | 新規検査 | 再利用 |
| --- | ---: | ---: | ---: |
| `manifold_gluing --full-check-local` | 1,221 | 60 | 1,161 |
| `manifold_gluing` の再利用 | 1,221 | 0 | 1,221 |
| `boundary_manifolds` 回帰 | 1,081 | 634 | 447 |
| `smooth_partitions` 回帰 | 581 | 428 | 153 |
| `manifolds` 回帰 | 628 | 291 | 337 |
| 通常のリポジトリ全体検査 | 11,767 | 11,247 | 520 |

全体検査は `python3 scripts/check_all.py --state-dir work/g04-final/repository --initial-memory-mib 12288 --memory-mib 12288 --cache-budget-mib 12288 --min-free-mib 512` で実行した。
全体の所要時間は 5,651.742 秒、最大 RSS は 10,436,744 KiB、最大仮想メモリは 12,424,536 KiB であった。
保存失敗と破損キャッシュの読み出しは 0 件、checkpoint の再開は 0 回、worker の回復は 1 回であった。
[worker-recovery.txt](worker-recovery.txt) に回復時のログの該当部分を保存した。
`compact_support_k` の worker で 285,212,688 bytes のメモリ割当が失敗し、checkpoint 36604 から再開して accepted になった。
各 package の終了コード、検査対象、再利用対象、回復の詳細は機械可読の記録に保存した。

対象 package の検査前後、および全体検査前後の source snapshot の全ファイルを、この数学ソースの Git blob と比較し、一致を確認した。
全体検査前後の source snapshot も同一である。
全体 snapshot の SHA-256 は `8ac18618910b4b036dd14df27acdc8d011129f0232ebaa81f0dab26583dcac1a` である。
現在の checker、各報告の checker、記録した checker の識別子も一致する。

[summary.json](summary.json) に正確なコマンド、終了コード、各計測値、snapshot とソースの対応を保存した。
[verification-reports.json.gz](verification-reports.json.gz) は各検査の報告をまとめた gzip 圧縮 JSON であり、個々の検査対象と検査済み・再利用の対応を含む。
