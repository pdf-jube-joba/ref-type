# 束のホモトピー不変性と clutching（B04）

[B03 の計量・有限埋め込み・射影の像束](../bundle_complements/README.md)、[K06 の近接射影比較](../../algebra/spectral_splitting/README.md)と区間の局所から大域への原理、[B02 の束演算](../bundle_operations/README.md)を再利用する。
実・複素の両方のスカラーを扱う `Homotopy.Over` に構成を置く。

## 公開 API

入口は `bundle_homotopy.Homotopy[].Over`。

| API | 構成・証明 |
| --- | --- |
| `Cylinder.endpointIsomorphismExists` | コンパクト Hausdorff 空間と区間の積上の束の両端を比較する |
| `For.Pullbacks.Along` / `Relative` | ホモトピックな引き戻しを比較し、固定部分集合での恒等性を示す |
| `For.Extensions` / `To` | cofibration に沿う自己同型・二束間同型の相対延長 |
| `For.Contractible` / `Disks.Triviality` | 収縮可能なコンパクト空間・閉円板上の任意の束を自明化する |
| `Clutching.With` / `Pullback` | 二開集合の遷移関数から束を作り、引き戻しとの比較同型を構成する |
| `Clutching.Homotopy` / `With.Sum` / `With.Stabilize` | 遷移関数のホモトピー、ブロック直和・安定化を束の同型へ送る |
| `Disks.Hemispheres.Cover` | 二円板の pushout と球面の実際の同相・閉半球での貼り合わせ |
| `Disks.Clutched` / `Homotopy` | 境界球面の GL 値関数による clutching と円板制限の自明化 |
| `Disks.Clutched.Comparison.diskGaugeCriterion` | 両円板上の連続 gauge の境界での両立条件と束同型の存在の同値 |
| `Homotopy.Examples.Mobius` / `CircleLine` | 実の符号遷移・複素単位円遷移による具体的な線束 |

[実線束の例](src/Homotopy/Examples/Mobius.ref) は二点の境界上の符号を用いて円周上の束を作る。
[複素線束の例](src/Homotopy/Examples/CircleLine.ref) は単位円の複素座標を用いて二次元球面上の束を作る。
それぞれ実際の `Fiber` と `bundle` を公開する。

`Clutching.With.Pullback` と `With.Sum` の `alignedIsomorphismExists` は、比較同型と局所枠での可換式 `alignment` をまとめて与える。
比較の条件は \(h_-g=g' h_+\) である。
実の場合も同じ API を用いるため、同型の判定には両円板上の gauge を明示している。

## 検証と再開

ブランチは `math/b04-bundle-homotopy`、[PR #43](https://github.com/pdf-jube-joba/ref-type/pull/43)。
実装ソースの最終変更は `2f786058`、最後に package 検査が成功したコミットは `ca2a13df`（差分は文書のみ）。
最新 snapshot の `work/b04-package-current` は対象・依存閉包4,728 module、キャッシュ保存完了・終了0。
53,943ソース検査ステップ、最大 RSS 約4,415 MiB、worker 1、復旧・重複・再実行・失われたステップ・保存失敗は0。
実・複素の利用例、直和・安定化、円板の自明化、gauge の同型判定、比較同型の局所枠での可換式も含む。

- `cargo test --workspace --locked`：383件成功・終了0。
- `cargo test -p cli --locked --offline`：時間制限条件の lint 修正後に8件成功・終了0。
- `cargo clippy --workspace --all-targets --locked --offline -- -D warnings`：終了0。
- `python3 tests/tests.py --command /workspace/ref-type/target/debug/cli`：401件成功・終了0。
- 変更した Rust 10ファイルの `rustfmt --edition 2024 --check`、通常ビルド：終了0。

処理系では scratch cache の記録を有界にし、連続した lambda 適用の一括置換と透明な定義の比較を改善した。
不正な捕捉引数の型・個数を拒否する検査を含む78件の kernel テストを実施した。
修正前の確保失敗・時間制限は解消し、途中で中断した検査は終了130・未完了として区別した。
一時的に `exec-server transport disconnected` となったが、同じ作業領域へのアクセスが戻り、保存処理の終了0も確認できた。
接続切断の根本原因は不明である。

残作業は、影響する下流を含む workspace 全体の検査、最終差分・CI の確認、PR のマージと main の確認。
文書・計画の完了処理後の snapshot を `work/b04-workspace-snapshot.json` に保存し、次を実行する。

```sh
target/debug/cli libs --parse-only --save-source-snapshot work/b04-workspace-snapshot.json
target/debug/cli libs --source-snapshot work/b04-workspace-snapshot.json --memory-mib 10240 --cache-budget-mib 12288 --time-limit-seconds 3600 --diagnostics compact --report-json work/b04-workspace.json --cache-stats
```
