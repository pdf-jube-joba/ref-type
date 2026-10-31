# A06 実装途中の検査記録

A06 は未完了である。
この記録は現在の実装ソースの型検査を記録する。
Schwartz 可積分性、各 Fourier 交換公式、Schwartz 保存、Gaussian と反転公式の証明が残っている。
体系・処理系の致命的制限は確認されていない。

検査ソースは `d4d302ed7bd51d3f72aad6c16a03d120cb55f5c2`、開始時 main は `7650fb3593d6a6cc6960055670db15dfed73b000`。
通常 release checker は現在の Rust ソースからビルドし、SHA-256 は `a92c84f2ffd0ab3f333a01de0301f647e347a2ec774f30cbba85c062c4346726` である。
既存の約 6.0 GiB のキャッシュを保持し、通常のソース・依存・処理系照合を使用した。

通常全体検査は 11029 対象全てを受理した。
新規検査 4252、再利用 6777、保存失敗 0、破損読み取り 0、終了コード 0。
開始・終了 snapshot と対象一覧の一致、checker バイナリの不変性を検査スクリプトが確認した。
コンテナの cgroup 上限は 16 GiB、検査上限は初期・最大ともに 12 GiB。

対象パッケージの `--full-check-local` は 30 モジュールを新たに検査し、607 モジュールを再利用して受理した。
A05 `lp_spaces` と G01 `smooth_partitions` の通常回帰検査も終了コード 0。
各検査の開始・終了 snapshot は一致し、全ての読み込みソースは全体検査の固定ソースと一致する。

予備 main 全体検査は 8642 対象の検証後、終了コード 130 で安全に中断した。
予備実行の公開済みキャッシュを保持し、新パッケージ登録後の最終固定ソースで通常全体検査を完走した。
予備実行と最終実行の新規・再利用数は [verification.json](verification.json) に区別して記録する。

完全な対象一覧は [targets.json.gz](targets.json.gz)、通常全体検査の完全な報告は [repository-report.json.gz](repository-report.json.gz) に保存した。

```sh
cargo build -p cli --release --locked
python3 scripts/check_all.py --initial-memory-mib 12288 --memory-mib 12288 --state-dir work/a06-final --min-free-mib 512
```
