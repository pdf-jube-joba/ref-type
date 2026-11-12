# G05 コンパクト埋め込みの検査記録

数学ソースは `e89608bf7e5bafd8d2af80752529bdf10c83892d` である。
通常 checker を `cargo build -p cli --release --locked` でビルドした。
`--full-check` は用いず、通常キャッシュと対象 package の依存閉包を使った。
Rust は `rustc 1.99.1 (58cf8f9c3 2026-10-13)` である。

`compact_embeddings` 全体、neat embedding 存在定理、その具体的な閉区間への適用を検査した。
依存回帰は `manifolds`、`boundary_manifolds`、`smooth_partitions`、`inverse_implicit`、`manifold_gluing` である。
いずれも終了コード 0、結果は `accepted` である。
存在定理には有限チャートの選択、double、collar の潰し写像、法線微分、厳密な collar 積の式の証明を含む。

集約検査の実行コマンド:

```sh
python3 scripts/check_all.py --state-dir /tmp/g05-full --cache-dir libs/refcache \
  --initial-memory-mib 12288 --memory-mib 14336 --cache-budget-mib 12288 --min-free-mib 512
```

[summary.json](summary.json) はコマンド、終了コード、対象数、資源使用量、checker の SHA-256 とソース照合結果を記録する。
[verification-reports.json.gz](verification-reports.json.gz) は package と集約検査の機械可読レポートで、個別モジュールの検証・再利用の記録を含む。
集約検査で使った不変 snapshot の全 12,682 ファイルを Git blob と比較し、すべて数学ソースのコミットと一致した。

最終の全体検査は全13,990対象を受理し、終了コード0で完了した。
新規検査7,343、再利用6,647、所要時間3,016.542秒、最大RSS11,181,432 KiBである。
キャッシュ保存失敗と破損読み取りは0件である。
`k_theory_thom` は割り当て上限到達後に checkpoint 45654 から一度復旧し、最終結果は受理された。
最終実行ではスコープ単位のメモリ上限終了は0件である。

停止指示で中断した初回実行は、アーカイブの `interrupted_aggregate` と `interrupted_workers` に区別して保存した。
初回の資源上限・自動分割と最終実行の復旧について、[worker-recovery.txt](worker-recovery.txt) に該当ログを残した。
数学ソース固定後の変更は README と検査証跡のみである。
