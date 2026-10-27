# B05 検査と再開

基点 main: `bd8fd86d5368968ff22e06f81beb5469bc348623`。
専用 worktree: `/workspace/ref-type-b05`、ブランチ: `codex/b05-grassmannians`。
検査対象 commit: `f95b954edfc59eb2616b977863e49bd3e43606ea`。

実・複素の `Model.Carrier`、コンパクト Hausdorff 性、各点のグラフ座標、普遍束・補束、直和・安定化・直交補の写像と引き戻し同型、射影空間と具体例を実装した。
対象 full-check-local、依存閉包、bundle_complements 回帰はいずれも accepted、終了コード0、キャッシュ保存失敗0。
workspace 全体の通常検査は中間実行で300秒の時間上限に達し未完了。
詳細と検査 JSON は `benchmarks/records/grassmannians/README.md` を参照。

```sh
cd /workspace/ref-type-b05
/workspace/ref-type/target/debug/cli libs/geometry/grassmannians --module grassmannians --full-check-local --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/b05-finish-target.json
/workspace/ref-type/target/debug/cli libs/geometry/grassmannians --module grassmannians --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/b05-finish-closure.json
/workspace/ref-type/target/debug/cli libs/geometry/bundle_complements --module bundle_complements --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/b05-finish-bundle.json
```
