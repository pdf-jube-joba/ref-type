# B05 検査記録

検査対象の実装 commit: `f95b954edfc59eb2616b977863e49bd3e43606ea`。基点 main: `bd8fd86d5368968ff22e06f81beb5469bc348623`。
処理系 SHA-256: `6ad1ed33c8ada906086b47d9367becfe019fc4631522ee4d7bc4fb5594e57630`。
対象の `.ref` と manifest の SHA-256: `442cb6e9fe8eefc3e567caaef0e8aa99707983450296a241cb08580541424363`。
入力ハッシュはパスの辞書順で `path + NUL + contents + NUL` を連結して計算した。

専用 worktree の `libs/refcache/` を共有し、既定の3072 MiB制限、worker 1、各300秒上限で実行した。
対象の全宣言を `--full-check-local` で再検査し、依存閉包は入力を照合したキャッシュを利用した。
束基盤の回帰検査も同じキャッシュ運用で実施した。

| 検査 | 結果 | 再検査 module | ソースステップ | 再利用 module | 経過秒 | 最大 RSS MiB |
| --- | --- | --- | --- | --- | --- | --- |
| 対象 full-check-local | accepted | 90 | 1433 | 621 | 25.625 | 2056.9 |
| 対象依存閉包 | accepted | 0 | 0 | 711 | 3.607 | 661.3 |
| bundle_complements 回帰 | accepted | 109 | 1337 | 511 | 19.430 | 1578.5 |

三検査とも終了コード0、キャッシュ保存失敗・worker 復旧・重複実行・再実行・失われたステップは0。
生の記録は [対象](final-target.json)、[依存閉包](final-closure.json)、[束回帰](final-bundle.json)。

```sh
/workspace/ref-type/target/debug/cli libs/geometry/grassmannians --module grassmannians --full-check-local --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/b05-finish-target.json
/workspace/ref-type/target/debug/cli libs/geometry/grassmannians --module grassmannians --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/b05-finish-closure.json
/workspace/ref-type/target/debug/cli libs/geometry/bundle_complements --module bundle_complements --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/b05-finish-bundle.json
```

開発中にはソース変更を検出した依存検査の中断、複素側の名前衝突・型推論エラーがあり、修正して最終検査で再検査した。
workspace 全体を対象にした通常検査は300秒上限で未完了だったため、対象依存閉包の結果と区別する。
Rust 処理系は変更しておらず、Rust テストは未実行。
他の履歴 JSON は各時点の中間検査である。
