# A19 作業と再開手順

基点 main: bd8fd86d5368968ff22e06f81beb5469bc348623。
専用 worktree: /workspace/ref-type-a19。
ブランチ: codex/a19-complex-hilbert。

A19 の計画要件を実装した。
複素 Hilbert 空間、Riesz 表現、有界随伴、閉部分空間の射影、直交補と商、有限階数作用素、コンパクト作用素の和・前後合成・ノルム極限・随伴による閉性、恒等作用素のコンパクト性から有限次元性を証明した。
有限次元は恒等写像の有限個の複素座標を通る線形因子分解として表す。
コンパクト作用素と有限階数近似の同値も証明した。

ソース commit 8f29c194 の対象 full-check-local、依存先、functional_analysis.Metric.Geometry と metric_spaces.MetricSpace.Compactness の回帰検査はいずれも accepted、終了コード 0、キャッシュ保存失敗 0。
結果と実行条件は benchmarks/records/complex-hilbert/README.md を参照。
既存のキャッシュは workspace の libs/refcache を共有する。

再検査する場合は、先に対象ソースと再開手順を commit・push し、同じ対象の検査プロセスがないことを確認する。
```sh
cd /workspace/ref-type-a19
/workspace/ref-type/target/debug/cli libs/analysis/complex_hilbert --module complex_hilbert --full-check-local --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/a19-complete-target.json
/workspace/ref-type/target/debug/cli libs/analysis/complex_hilbert --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/a19-complete-dependencies.json
/workspace/ref-type/target/debug/cli libs/analysis/functional --module functional_analysis.Metric.Geometry --full-check-local --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/a19-complete-geometry.json
/workspace/ref-type/target/debug/cli libs/topology/metric --module metric_spaces.MetricSpace.Compactness --full-check-local --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/a19-complete-metric.json
```
処理系が必要なら `CARGO_TARGET_DIR=/workspace/ref-type/target cargo build -p cli --locked --offline` でビルドする。
