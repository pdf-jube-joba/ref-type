# C02 完了時の検証

C02 の全要件を実装したソース `3649971dbd9579b830cbd3f90279156e786cb792` を検査した。
実装の未完項目はない。
有限 CW 対モデルには、指定部分空間を保つ両方向の写像と両側のホモトピーが含まれる。
API・例・構成は [thom_spaces](../../../../libs/topology/thom_spaces/README.md) を参照する。
この記録に続く commit で変更するのは検査記録と Markdown の索引説明であり、検査入力のソースは変更していない。

## バイナリと環境

- 基底 commit: `7650fb3593d6a6cc6960055670db15dfed73b000`。
- 通常の release checker を `cargo build --release -p cli --locked --offline` で再ビルドし、終了コード0。
- `target/release/cli` SHA-256: `cceb5138a86aa7863476ffe7e0c152d18526e074b65c4f870b5751b68dcf623e`。
- Rust ソース・Cargo manifest/lock・検査 driver は基底から変更していない。
- cached 環境の既存キャッシュを保持し、通常のソース・依存入力・バイナリ照合で検証した。
- コンテナ16 GiB、初期・最大検査メモリ12 GiB、キャッシュ予算12 GiB。
- cold 実行との比較は行っていない。

## 最終固定ソースの結果

| 検査 | 新規 | 再利用 | 終了コード |
| --- | ---: | ---: | ---: |
| `thom_spaces --module thom_spaces` | 0 | 2012 | 0 |
| `thom_spaces` と読み込んだ全依存 | 0 | 6746 | 0 |
| 通常の `scripts/check_all.py libs` | 5865 | 5522 | 0 |

対象検査は自身の388 module と参照先を含む2,012 moduleを受理した。
依存全体の一括検査は6,746対象を受理した。
通常全体検査は **11,387対象すべて** を受理し、97回の package 検査はすべて終了コード0だった。
通常全体検査は 122,826 source steps、所要時間 2116.198 秒、最大RSS 10,338,448 KiB、最大仮想メモリ 12,424,344 KiBだった。
全最終検査で保存失敗と破損キャッシュ読取りは0件だった。

全体検査の `compact_support_k` では285,212,688 bytesの確保失敗が1回あり、supervisor が checkpoint 35076 から自動復旧した。
最終結果は受理であり、worker recoveries は1、lost steps は3,202、duplicate/replayed source steps はともに0だった。
生の計数は [復旧時の report](recovery-compact_support_k.json.gz) と [ログ抜粋](recovery-compact_support_k.txt) に保存した。

依存回帰も同じ最終ソースで、各開始・終了 snapshot の一致を確認した。

| パッケージ | 新規 | 再利用 | 終了コード |
| --- | ---: | ---: | ---: |
| `bundle_complements` | 0 | 648 | 0 |
| `bundle_homotopy` | 0 | 887 | 0 |
| `puppe_sequences` | 0 | 427 | 0 |
| `singular_cellular` | 0 | 2063 | 0 |
| `singular_excision` | 0 | 1000 | 0 |
| `singular_cohomology` | 0 | 927 | 0 |
| `bundle_extension` | 0 | 1008 | 0 |

## 対応関係と保存物

全体検査の開始・終了 snapshot は一致し、含まれる **10,178ファイルすべて** が検査対象 commit の Git blob と一致する。
開始・終了の対象一覧も一致し、バイナリの digest は全体検査開始時・終了時・再ビルド後で同じだった。

- source snapshot SHA-256: `e195e603b8dc1449aa2263bb2c2d1035e5996917b8e693e1700da5a58ff28a43`。
- 対象一覧 SHA-256: `44a22bc2eefe65ebf4754e69a6bab5492b70df00c9689f9c497aff6e20b2326e`。
- [summary.json](summary.json): 正確なコマンド、commit、終了コード、計数、snapshot・driver・binary の digest。
- [whole-report.json.gz](whole-report.json.gz)、[attempts.json](attempts.json): 全対象、検証済み対象、新規・再利用の集合と実行記録。
- [source-files.json.gz](source-files.json.gz)、[targets.json.gz](targets.json.gz): ソース照合用の相対パス・SHA-256・Git blob ID と対象一覧。
- `focused-report.json.gz`、`wide-report.json.gz`、`dependency-*.json.gz`: 対象・一括・依存回帰の CLI report。
- [build.txt](build.txt): 通常 release build の完了記録。

## 開発途中の結果

[preliminary-runs.json](preliminary-runs.json) と `preliminary-*.json.gz` は最終検査と区別して保存した。
全 API 実装直後の開発検査は416新規・1,624再利用、4,970 source stepsで受理された。
以前の依存全体の検査では `sphere_maps.Circle.Powers.Actions.DegreeZero` の import に `definition local context is outside reference scope` が出た。
最終ソースの通常全体検査と同じ入口の依存全体検査はいずれも受理された。
この間に `sphere_maps` や処理系のソースは変更していない。
以前のソースに対する全体検査・途中の未完成状態は [継続時](../continuation/README.md) と [CW 基盤](../cw-foundations/README.md) の記録に残している。
