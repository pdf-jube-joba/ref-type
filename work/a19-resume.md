# A19 作業の再開

基点 main: bd8fd86d5368968ff22e06f81beb5469bc348623。
専用 worktree: /workspace/ref-type-a19。
ブランチ: codex/a19-complex-hilbert。

A19 に該当する既存 PR・ブランチ・パッケージがないことを確認した。
複素線形空間の実スカラー制限、複素ノルムと実ノルムの接続、Hermitian 内積の実部による実 Hilbert 構造を実装中。
現段階のソースは未検査。
Riesz 表現、随伴、射影、直交補と商、有限階数、コンパクト作用素に関する計画の定理は未実装。

```sh
cd /workspace/ref-type-a19
/workspace/ref-type/target/debug/cli libs/analysis/complex_hilbert --module complex_hilbert --cache-stats --diagnostics compact --report-json work/a19-target.json > work/a19-target.log 2>&1
```

workspace の libs/refcache を共有する。
処理系が必要なら `CARGO_TARGET_DIR=/workspace/ref-type/target cargo build -p cli --locked --offline` でビルドする。
