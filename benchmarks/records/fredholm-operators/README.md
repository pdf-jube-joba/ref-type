# A11 Fredholm 作用素と指数の検査記録

A11 は未完了であり、具体的な作用素への特殊化時の型エラーでブロックされている。
指数の四つの法則は未実装である。

## ソースと処理系

- 検査ソース commit: `b947d8824e6de71444da94515bb889364720a352`。
- 基点 main: `cfca188e66f15dfe8c354b18861a9920d12f83d5`。PR #59 の改善後の全体検査を含む。
- release CLI SHA-256: `96e9f70c1924311a06c667b21dda6b71e3c0ad85299d570ee586b66d1f2d2820`。
- A11 の `.ref`・manifest・workspace manifest の SHA-256: `1ed190475fc26ba166c1357c240e8932ec889e9ffbb83bf5b26636b15ef14ed3`。
- ソースハッシュは辞書順の `path + NUL + contents + NUL` を連結して計算した。
- 処理系ソースには最終差分がない。調査中の変更候補は戻した。

## 対象と関連回帰

| 範囲 | 結果 / 終了コード | 経過秒 | 最大 RSS MiB | 再検査 module | 再利用 module |
| --- | --- | ---: | ---: | ---: | ---: |
| A11 全体 | rejected / 1 | 7.211 | 1059.7 | 55 | 616 |
| 具体的な利用例 | rejected / 1 | 6.182 | 1044.6 | 37 | 614 |
| 汎用 Fredholm 補題 | accepted / 0 | 8.254 | 1009.0 | 35 | 609 |
| 有限階数トレース | accepted / 0 | 6.369 | 997.1 | 27 | 552 |
| 有限次元基底 | accepted / 0 | 5.813 | 986.4 | 10 | 520 |
| A19 回帰 | accepted / 0 | 9.725 | 558.3 | 165 | 296 |

全コマンド、入力一覧、実行統計は [targeted-summary.json](targeted-summary.json) に保存した。
失敗の診断は [target-failure.txt](target-failure.txt) と [examples-failure.txt](examples-failure.txt) に保存した。
汎用の補題範囲の `accepted` は、具体的な作用素への適用の成功や A11 全体の完了を示さない。

各コマンドは `target/release/cli <package> --module <module> --full-check-local --diagnostics compact --cache-stats --time-limit-seconds 300 --report-json <report>` である。
`--full-check` は使っていない。
workspace の `libs/refcache/` を共有し、対象の宣言を再検査し、適合する依存先のキャッシュを再利用した。
各 CLI は worker 1、既定のメモリ上限、300 秒上限で実行した。
全体検査とは別プロセスで並行したため、時間は性能比較に使用しない。
表の時間は各プロセスの起動から終了までの経過時間であり、ビルド時間や作業全体の時間を含まない。
対象検査中の意図的停止はなく、保存失敗・不正なキャッシュ読み込み・worker 復旧はすべて 0 だった。

## 通常全体検査

```sh
source /workspace/ref-type-env.sh && cargo build -p cli --release --locked && python3 scripts/check_all.py
```

Cargo 表示のビルド経過時間は 1 分 33 秒だった。
通常全体検査は **failed、ドライバ終了コード 2** だった。
A11 の子検査が `rejected`、終了コード 1 で停止した。
資源不足による停止ではなく、最後の汎用公開案 `Space.Operators.Hilbert.atkinson` の特殊化に関する型エラーである。

| 指標 | 結果 |
| --- | ---: |
| 列挙した対象 | 9854 |
| 検査を確認した対象 | 6433 |
| 新規検査 / 再利用 | 6284 / 149 |
| 未確認の対象 | 3421 |
| Python ドライバの経過秒 | 1484.012 |
| 各子プロセスの最大 RSS MiB | 3031.0 |
| 各子プロセスの最大仮想メモリ MiB | 3608.2 |
| checkpoint 再開 / worker 復旧 | 0 / 0 |
| 保存失敗 / 不正キャッシュ読み込み | 0 / 0 |

既定の初期 4608 MiB、最大 6144 MiB、worker 1 で実行した。
コンテナのメモリ上限は 16 GiB で、CLI の仮想メモリ上限とは別である。
子プロセスの最大値は同時点の全プロセスの合計ではない。
最終検査に意図的な停止時間はなく、同じ処理系とソースのまま実行した。

集計は [repository-summary.json](repository-summary.json)、失敗診断は [repository-failure.txt](repository-failure.txt) に保存した。
完全なローカル記録は `/workspace/ref-type/work/repository-check/20261030T134704.549450Z/report.json` にある。
source snapshot SHA-256 は `d7ed5aa982f4de7ebf3eddefdedcbc9e1672cf1e9cce57c69dfbda3fd94adba9` である。
型エラーで停止したため、同じソースで再試行しても資源制限の復旧にはならない。
原因を修正した後、同じ標準コマンドを実行すれば適合するキャッシュと checkpoint を検証して再開できる。

## 阻害要因と未検証範囲

零 Hilbert 空間の恒等作用素に `fredholmOfParametrix` を適用すると、特殊化後の定義本体の検査で元の抽象的な `Fredholm(V, space, norm, W, target, targetNorm, f)` が残る。
`structure` から論理積への変更、型引数の明示、定理を汎用モジュールへ移す回避を試した。
最後の移動案は `Space.Operators.Hilbert.atkinson` だが、この案の検査も型エラーになる。
開発中に独立したキャッシュでも直接 API の同じ失敗を確認した。

核・像・余核、有限次元の構成、parametrix と Fredholm 性の汎用証明、整数指数 API、有限階数トレースの補題を実装した。
具体的な公開 API の適用は未検証であり、失敗例を登録したままにしている。
指数の合成則・直和則・コンパクト摂動不変性・ノルム連続族の局所定数性は未実装である。
型検査の回避や定理の弱化はしていない。
再現例と最後の回避案は [gaps.md](../../../gaps.md#fredholm-性の具体的な作用素への特殊化) に記載した。
