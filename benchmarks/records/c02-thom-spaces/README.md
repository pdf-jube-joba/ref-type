# C02 の検証記録

C02 全体は未完了である。
証明済みの API と残る数学的範囲は [パッケージ README](../../../libs/topology/thom_spaces/README.md) に記載する。
この記録は以下の固定ソースに実装されている定義・証明の検証である。

- 基点 main: `7650fb3593d6a6cc6960055670db15dfed73b000`。
- 検証したソース: `593ccb55762d93914886c608a5db39e5b289e8ee`。
- 検査器: `target/release/cli`、SHA-256 `cceb5138a86aa7863476ffe7e0c152d18526e074b65c4f870b5751b68dcf623e`。
- 検査器は main の Rust ソースから `cargo build -p cli --release --locked --offline` でビルドし、終了0。
- 検証対象コミットまでの Rust・Cargo・検査ドライバの変更はない。
- cgroup は16 GiB・4 CPU、検査の initial/max はともに12 GiB、キャッシュ予算は12 GiB。

## 固定ソースの結果

| 検査 | 終了 | 新規 module | 再利用 module | 保存失敗 |
| --- | --- | --- | --- | --- |
| `--module thom_spaces --full-check-local` | 0 | 75 | 1466 | 0 |
| 通常 `scripts/check_all.py libs` | 0 | 10428 | 646 | 0 |

通常全体検査は 11,074 対象すべてを受理した。
破損キャッシュ読み取り 0、worker 復旧 1、最大 RSS 約 10129 MiB、約 2677.2 秒である。
source 検査ステップ、重複・再実行・失われたステップと各実行の詳細は `focused-report.json.gz`、`whole-report.json.gz`、`attempts.json` に保存した。
`compact_support_k` は285,212,688バイトの allocation failure 後に checkpoint 35076 から復旧し、最終的に終了0となった。
同 scope の失われた計算ステップは3,202、再実行ステップは0、storage の checkpoint resume は1である。
全体ドライバの `checkpoint_resumes` は別の `checking.checkpoint_hits` を集計するため0となっている。
生の復旧結果は `recovery-compact_support_k.json.gz`、エラー抜粋は `summary.json` に保存した。
割り当て失敗を起こした OS・allocator の正確な制限までは特定していない。
既存の約6 GiBの `libs/refcache` を維持し、処理系の通常のソース・依存・manifest 照合を使用した。
cold run との速度比較は行っていない。

依存パッケージの回帰検査と新パッケージの通常キャッシュ検査は、同じ全体検査内の次の root scope である。
各 root は子 module と参照先を含む。

| root scope | 終了 | 新規 | 再利用 | 保存失敗 |
| --- | --- | --- | --- | --- |
| `bundle_complements` | 0 | 0 | 648 | 0 |
| `bundle_homotopy` | 0 | 0 | 887 | 0 |
| `puppe_sequences` | 0 | 202 | 350 | 0 |
| `thom_spaces` | 0 | 0 | 1541 | 0 |

## ソースと対象の対応

全体 snapshot の 9,875 ファイルを Git の検証コミットの blob と照合し、内容の一致を確認した。
`source-files.json.gz` は相対パスと各ファイルの SHA-256、`targets.json.gz` は順序を含む全検査対象である。

| 対象 | 開始 SHA-256 | 終了 SHA-256 |
| --- | --- | --- |
| 対象 package の snapshot | `6b55496a4e274f8731f3d36d1d367013d349a99649c103d5c2c921156223b1a1` | `6b55496a4e274f8731f3d36d1d367013d349a99649c103d5c2c921156223b1a1` |
| workspace の snapshot | `364703011020d90341a726b92fc95f4ef5365b0aba2d2cebdc0458eb8f06d239` | `364703011020d90341a726b92fc95f4ef5365b0aba2d2cebdc0458eb8f06d239` |

開始・終了 snapshot の JSON 内容はそれぞれ一致した。
全体ドライバは終了時に対象リストの一致と全対象の coverage も確認した。
検査器の SHA-256 は各呼び出しと終了時に照合した。
全体の対象リストの SHA-256 は `e876d082aa293b635d5c436e18043132832e45301b56896938c67da5863e3b88`、ドライバの SHA-256 は `b0b7159aa8440dd12d090fdb29cc61df4d7db29c8e58b11c335e8126b7e9ef9f`。

```sh
target/release/cli libs/topology/thom_spaces --module thom_spaces --full-check-local --memory-mib 12288 --cache-budget-mib 12288 --cache-stats --save-source-snapshot work/c02/final-focused-source.json --report-json work/c02/final-focused.json
python3 scripts/check_all.py libs --binary target/release/cli --state-dir work/c02/final-whole --memory-mib 12288 --initial-memory-mib 12288 --cache-budget-mib 12288
```

対象 package の終了 snapshot 照合の初回コマンドは `--module` と `--parse-only` の併用が拒否された。
そのサブコマンドの終了コードは個別採取していない。
`--module` を外した `--parse-only --save-source-snapshot` は終了0で、開始 snapshot との一致を確認した。
この間にソースは変更していない。

開発中の予備検査は変更中のソースを対象とし、最終検証とは別である。
初回の広い予備検査は明示的に SIGINT で中断し終了130、以後の型・構文エラーは実装中に修正した。
予備実行の outcome・新規/再利用・保存失敗は `preliminary-runs.json` に記録する。
記録を追加するコミットでは proof ソースと manifest を変更しない。
