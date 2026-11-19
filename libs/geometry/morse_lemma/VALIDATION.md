# 検査記録

2026-11-19、main の `6e2106dfaf0a5370e84213a1c60fccf126d359a4` を基点とする変更を検査した。
この基点は `dce3d353e75972c507928253d6c33420f6f55a0f` を含む。
Rust と checker のソースへの変更はない。
ビルド済み checker を現行ソースから再構築し、Rust 1.100.0 の release build を使った。
機械可読な集計・入力と結果の SHA-256・生の記録の保存先は [verification.json](verification.json) にある。

## 対象と依存閉包

`--full-check-local` により `morse_lemma` の **137 module 全てを再検査し、accepted** になった。
通常版・パラメータ版の最上位存在定理、指数との接続、局所定数性、全ての独立例を含む。
対象を限定した検査から読み込む依存閉包全体も検証対象である。

| 指標 | 結果 |
| --- | --- |
| 対象 module の再検査 | 137 / 137 |
| 依存閉包を含む検証済み module | 1,926 |
| 新たに検査した module（依存を含む） | 142 |
| 整合する検証結果を再利用した module | 1,784 |
| source steps | 1,952 |
| 所要時間 | 36.49 秒 |
| 最大 RSS | 1,936,868 KiB |
| worker 復旧・重複・再実行・欠落ステップ | 全て 0 |
| キャッシュ破損・保存失敗 | 共に 0 |

README の使用例も独立 package から検査し、accepted になった。
追加の公理宣言・未証明箇所はない。
既存の関数・集合の外延性を使う。

## ライブラリ全体

`python3 scripts/check_all.py libs` による全体検査は **failed** である。
111 package、15,524 target を列挙し、68 scope・7,522 target まで accepted になった後、既存の `euclidean_sobolev` で停止した。
実行全体の所要時間は 461.73 秒、最大 RSS は 2,167,828 KiB である。
キャッシュの破損・保存失敗・worker の復旧はいずれも 0 だった。

停止箇所は [Euclidean/Order/Weight.ref:14](../../analysis/euclidean_sobolev/src/Euclidean/Order/Weight.ref#L14) の `Reciprocal` module 引数内にある `positiveNonzero _ (positive x)` である。

```text
Resolution Error: module arguments do not allow inference holes (`_` or `?`)
```

このファイルの内容は基点 main と同一であり、SHA-256 は `c98df52b2a9936e8e6ac7d5760e45ce4264498fe13fa6308d9a5b485ec23c802` である。
全体の全 source と target 一覧が実行前後で同一であることを追加確認し、対象検査に含まれる 1,738 source が全体検査の snapshot と一致することも確認した。

残り **8,002 target は全体 driver では未検証** である。
この数には失敗した scope と、その後に未到達の scope が含まれる。
G13 の全対象・依存閉包の成功は、上記の独立した対象再検査による。
全体検査の成功は主張しない。

## Rust の検査

`cargo test --workspace --locked -j 4` は accepted、34 suite で **384 passed / 0 failed / 0 ignored** だった。
対象コードの変更は数学ライブラリとその登録・文書だけであり、Rust の検査対象ソースは検査時から変化していない。
`git diff --cached --check` も通過した。

## 再現コマンドと範囲

```sh
cargo build -p cli --release --locked -j 4
target/release/cli libs/geometry/morse_lemma --full-check-local --memory-mib 4096 --cache-stats --time-limit-seconds 1800 --report-json /tmp/g13-target.json
python3 scripts/check_all.py libs --memory-mib 4096 --cache-budget-mib 12288 --min-free-mib 512 --time-limit-seconds 3600 --state-dir /tmp/g13-repository-check
cargo test --workspace --locked -j 4
```

整合性を確認した workspace 共有キャッシュを使用した。
依存先の証明をキャッシュ無効で全て再検査する cold check は実行していない。
全体 driver の停止後の scope も未実行であり、上記の既存エラーが全体完了の阻害箇所である。
