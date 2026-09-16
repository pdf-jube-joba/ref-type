# 型検査遅延の再現例

[report.md](report.md) の調査時に作成した独立した例を、会話に残っていた作成パッチから復元した。
元の `/tmp/ref-type-investigation.kNxbKp` は現在存在しない。
ここで復元したのは再現例のソースであり、当時のログ・計測用処理系・実験用分岐ではない。

| ファイル | 内容 | 調査時の未修正処理系での結果 |
| --- | --- | --- |
| [minimal.ref](minimal.ref) | 対の型を深さ10まで入れ子にした射影の等式 | 成功するが、深くなるほど遅い |
| [minimal12.ref](minimal12.ref) | 同じ例を深さ12まで拡張 | debugで数分かけて成功 |
| [minimal14.ref](minimal14.ref) | 深さ14の射影の等式のみ検査 | releaseでも約5分後に正規化上限で失敗 |
| [common-head.ref](common-head.ref) | 共通headの適用を比較する例（深さ14まで） | 成功するが、深くなるほど遅い |
| [common-head20.ref](common-head20.ref) | 同じ例を深さ20まで拡張 | debugで約37秒、最大RSS約787MiB |
| [refined-function.ref](refined-function.ref) | refinementに包んだ恒等関数の適用 | `identityBeta` が型不一致で失敗 |

どの `.ref` も `lib/` や他の再現例のimportは不要。リポジトリのルートで、例えば：

```sh
cargo run -p cli -- _plans/minimal.ref
cargo run -p cli -- _plans/common-head.ref
cargo run -p cli -- _plans/refined-function.ref
```

大きい例は時間・メモリを消費するため、必要なものを個別に実行する。
特に `minimal14.ref` はdebugでは非常に長くなりうる。

```sh
cargo run -p cli -- _plans/minimal12.ref
cargo run -p cli --release -- _plans/minimal14.ref
cargo run -p cli -- _plans/common-head20.ref
```

レポートの `REF_PROFILE`、`REF_KERNEL_PROFILE`、`REF_EXPERIMENT_*` は当時の診断用コピーに
追加した環境変数であり、現在の本体には実装されていない。これらを指定するだけでは
計測や修正後との比較はできない。上表の時間・メモリ量も当時の観測値で、今回の再計測値ではない。

復元時の確認（2026-09-16）：`cargo build --offline -p cli` 後、debugのCLIで
`minimal.ref` と `common-head.ref` の成功、および `refined-function.ref` の
`identityBeta` における `ty, inferred_ty not convertible` エラーを確認した。
大きい3例（`minimal12.ref`、`minimal14.ref`、`common-head20.ref`）は今回再実行していない。
