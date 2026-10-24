# 束のホモトピー不変性と clutching（B04、実装中）

計画は [_plans/math/b04-bundle-homotopy.md](../../../_plans/math/b04-bundle-homotopy.md)。
B03 の計量・有限埋め込み・射影の像束、K06 の近接射影比較と区間の局所から大域への原理、B02 の束演算を再利用する。
実・複素の両方のスカラーを扱う `Homotopy.Over` に構成を置く。

## 公開 API（最終検証中）

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

`Clutching.With.Pullback` と `With.Sum` の `alignedIsomorphismExists` は、比較同型と局所枠での可換式 `alignment` をまとめて与える。
比較の条件は \(h_-g=g' h_+\) である。
実の場合も同じ API を用いるため、同型の判定には両円板上の gauge を明示している。

## 検証と再開

基点は K06 統合済み main `75e87a4c`、ブランチは `math/b04-bundle-homotopy`、[draft PR #43](https://github.com/pdf-jube-joba/ref-type/pull/43)。
最後に B04 全スコープの検査が成功したコミットは `5168604a`（以降は文書のみ変更）。
`libs --module bundle_homotopy` は874 module・1,031ソース検査ステップ、キャッシュ保存完了・終了0で成功した（`work/b04-scope-first`）。
復旧・重複・再実行・失われたステップ・キャッシュ保存失敗は0。
`Clutching.Homotopy` は依存先を含む744 module、キャッシュ保存完了・終了0で成功した（`work/b04-reused-endpoint`）。
両端比較、ホモトピック・相対引き戻し、cofibration に沿う同型の延長、開集合の clutching と引き戻し、円板 pushout と球面の同相、連続なブロック直和は、それぞれ以前の対象検査が終了0で成功している。
直和・安定化、円板上の任意の束の自明化、円板 gauge と束同型の対応、実・複素の利用例も対象スコープの検査が成功した。
package 全体・依存先・影響箇所・workspace の最終検査、文書・下流依存リンク・ロードマップの完了処理が残る。

処理系では scratch cache の記録を有界にし、連続した lambda 適用を一括置換し、透明な定義を使われる捕捉引数から比較する。
`cargo test -p kernel --lib` は不正な引数の型・個数の拒否を含む78テスト成功・終了0、通常ビルドも終了0。
追加した cost / allocation stack 計測は通常の型検査規則を変えない。
`cargo test --workspace --locked` は最初の実行が依存取得時の proxy 接続失敗で終了101。
ネットワークを有効にした再実行 `work/b04-rust-workspace-tests2` は383テスト成功・終了0。
`cargo clippy --workspace --all-targets --locked --offline -- -D warnings` は CLI の時間制限条件の `nonminimal_bool` 1件で終了101（`work/b04-clippy`）。
同値な `is_none_or` 条件へ修正後、clippy の再実行は終了0、CLI テスト8件・通常ビルドも終了0（`work/b04-clippy2`、`work/b04-cli-tests`、`work/b04-cli-final-build`）。
`python3 tests/tests.py --command /workspace/ref-type/target/debug/cli` は401件成功・終了0（`work/b04-acceptance`）。
標準の `rustfmt`・`clippy` component を導入した（終了0）。
変更した Rust 10ファイルの `rustfmt --edition 2024 --check` は終了0。

修正前は `Cache::insert` の scratch write 記録の4 GiB確保失敗（終了2・memory-limit）、型変換の時間制限（終了2）を確認した。
`work/b04-cache-fixed*`、`work/b04-beta`、`work/b04-captures-final`、`work/b04-conversion-profile` は改善・計測の切り替え時に中断した（終了130・未完了）。
端点の同じ clutching 束を二重に構成せず、引き戻しの構成を再利用して遷移式を示す修正後、対象検査は成功した。
環境・端末・ファイル操作は利用できる。

検査は `target/debug/cli <input> --parse-only --save-source-snapshot work/<name>-snapshot.json`、続いて `target/debug/cli <input> --source-snapshot work/<name>-snapshot.json --memory-mib 8192 --cache-budget-mib 16384 --time-limit-seconds 900 --diagnostics compact --report-json work/<name>.json --cache-stats` を用いる。
対象を絞る場合は `--module <scope>` を付ける。
`libs/geometry/bundle_homotopy` 全体の依存閉包4,728 module の初回検査 `work/b04-package-first` は3,124 module の完了後、本体の未検証箇所を先に確認するため約770秒で中断した（終了130・未完了）。
共有キャッシュを保持し、同じ保存済み snapshot で package 全体を `work/b04-package-final` に再開する。
Rust 全体テストのビルドでディスク使用量が増えたため、CLI のキャッシュ保持上限を12 GiB（`--cache-budget-mib 12288`）に下げる。
引き戻し・直和の比較同型と局所枠での可換式を公開する `alignedIsomorphismExists` を追加した（未検証）。
次は package 全体の終了を確認し、追加 API を新しい snapshot で検査してから、影響する下流を含む workspace 全体を検査する。
B01 の逆同型存在、B02 の同型の合成・直和存在、pushout の帰納法を追加したため、それらと下流も最終検査に含める。
