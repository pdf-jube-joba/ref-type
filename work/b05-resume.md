# B05 再開手順

基点 main: bd8fd86d5368968ff22e06f81beb5469bc348623。
専用 worktree: /workspace/ref-type-b05、ブランチ: codex/b05-grassmannians。
実・複素の射影と既存の有限基底による階数から Grassmannian の台を定義する作業を開始した。

```sh
cd /workspace/ref-type-b05
/workspace/ref-type/target/debug/cli libs/geometry/grassmannians --module grassmannians --full-check-local --cache-stats --diagnostics compact --time-limit-seconds 300
/workspace/ref-type/target/debug/cli libs/geometry/grassmannians --cache-stats --diagnostics compact --time-limit-seconds 300
```

グラフ座標、位相的性質、普遍束と引き戻し比較、安定化、直和、直交補、射影空間は未実装。
