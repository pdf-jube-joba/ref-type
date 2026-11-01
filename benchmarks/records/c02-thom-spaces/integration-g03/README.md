# G03 統合後の検査

main `5e77aab88122f9f3e4f18743fbc474c83b3f8e9a` を C02 ブランチへ取り込んだ commit `8a67ce751dec5ff9901f47edbfc0a67ff82cf44e` を検査した。
共有の `libs/ref.toml` と `libs/README.md` は競合なくマージでき、`boundary_manifolds` と `thom_spaces` の登録をともに保持した。
G03 のソース・計画・記録は main と一致し、C02 の証明ソースと package manifest は統合前 `8cd3a8699dbb92990074eee00e6dcf39bb8c2645` と一致する。
main との差分は C02 の package・計画・記録・共有登録に限られる。
C02 の全要件は実装済みで、[API・例](../../../../libs/topology/thom_spaces/README.md) から有限 CW 対モデルと実際の円板・球面対の相対理論比較を利用できる。
この後の commit では検査記録と Markdown の説明だけを更新し、検査入力のソースは変更していない。

## ビルドと資源

通常の release checker を `cargo build --release -p cli --locked --offline` でビルドし、終了コード0だった。
Rust ソース・Cargo manifest/lock・`scripts/check_all.py` は main から変更していない。
`target/release/cli` SHA-256 は `cceb5138a86aa7863476ffe7e0c152d18526e074b65c4f870b5751b68dcf623e` であり、ビルド後・各検査・全体検査終了時で一致する。
コンテナ16 GiB、初期・最大検査メモリ12 GiB、キャッシュ予算12 GiBで実行した。
既存キャッシュを保持し、通常のソース・依存入力・バイナリ照合を使った。
cold 実行との比較は行っていない。

## 個別回帰

新規・再利用は各 CLI report の実測計数、検証済みは module path 集合の件数である。
各開始・終了 snapshot が一致し、全入力が後述の全体 snapshot と一致する。
C02 の検証済み集合は自身の388 moduleを、G03 は自身の189 moduleを含む。

| 検査 | 新規 | 再利用 | 検証済み | 終了コード |
| --- | ---: | ---: | ---: | ---: |
| `focused` | 0 | 2012 | 2012 | 0 |
| `bundle_complements` | 0 | 648 | 648 | 0 |
| `bundle_homotopy` | 0 | 887 | 887 | 0 |
| `puppe_sequences` | 0 | 427 | 427 | 0 |
| `singular_cellular` | 0 | 2063 | 2063 | 0 |
| `singular_excision` | 0 | 1000 | 1000 | 0 |
| `singular_cohomology` | 0 | 927 | 927 | 0 |
| `bundle_extension` | 0 | 1008 | 1008 | 0 |
| `boundary_manifolds` | 309 | 892 | 1081 | 0 |
| `wide` | 0 | 6746 | 6746 | 0 |

## 通常全体検査

```sh
python3 scripts/check_all.py libs --binary target/release/cli --state-dir work/c02/integration-g03-whole --memory-mib 12288 --initial-memory-mib 12288 --cache-budget-mib 12288
```

全 **11,576対象** を受理し、終了コード0だった。
新規0件・再利用11,576件、98回の package 検査はすべて終了コード0だった。
保存失敗・破損キャッシュ読取り・worker 復旧・lost steps・duplicate/replayed source steps はすべて0だった。
所要時間は202.461秒、最大RSSは1,369,888 KiB、最大仮想メモリは2,117,836 KiBだった。

開始・終了 source snapshot と対象一覧は一致する。
含まれる **10,344ファイルすべて** が検査対象 commit の Git blob と一致する。

- source snapshot SHA-256: `1a0d868d5e4b2894489127aa04ac094a03af51a5249acd526b2d76f36983c652`。
- 対象一覧 SHA-256: `43b8522212c68611677dfb9deddc9417cc0ddb6c52333b451ccd1b78634cb0fa`。
- [summary.json](summary.json): commit、main の保全、コマンド、終了コード、実測計数、バイナリ・driver・snapshot の digest。
- [regression-runs.json](regression-runs.json) と `regression-*.json.gz`: 個別回帰のコマンドと CLI report。
- [whole-report.json.gz](whole-report.json.gz)、[attempts.json](attempts.json): 全体検査の対象・検証済み・新規・再利用の集合と各実行の記録。
- [source-files.json.gz](source-files.json.gz)、[targets.json.gz](targets.json.gz): ソースの相対パス・SHA-256・Git blob ID と全対象一覧。
- [build.txt](build.txt): 通常 release build の完了記録。

[C02 完成時の記録](../completed/README.md) にある `compact_support_k` の確保失敗と自動復旧1回は、統合前の別実行の結果である。
今回の固定ソースの実行では復旧は発生していない。
