# C02 継続実装の検証記録

C02 全体は未完了であり、残る要求は球面束を含む有限 CW 対模型と対のホモトピー同値である。
この記録は、初回の3項目の未実装から、既存の反復懸垂との比較と相対特異理論の付加点除去を実装した後の固定ソースを検証する。
[パッケージ API](../../../../libs/topology/thom_spaces/README.md) と [計画](../../../../_plans/math/c02-thom-spaces.md) に正確な範囲を記載する。
[初回記録](../README.md) は別のソースに対する結果として保持する。

- 基点 main: `7650fb3593d6a6cc6960055670db15dfed73b000`。
- 検証したソース: `edd974ca8f1645c1cead3f45217c123d85faf979`。
- 検査器: `target/release/cli`、SHA-256 `cceb5138a86aa7863476ffe7e0c152d18526e074b65c4f870b5751b68dcf623e`。
- 検査器は初回に main の Rust ソースから通常の `cargo build -p cli --release --locked --offline` でビルドし、終了0。
- その後の Rust・Cargo・検査ドライバの変更はなく、同じバイナリのハッシュを検査前後に確認した。
- cgroup は16 GiB・4 CPU、検査 initial/max は12 GiB、キャッシュ予算は12 GiB。
- 既存の検証済みキャッシュを維持し、処理系の通常のソース・依存・manifest 照合を使った。
- cold run との速度比較は行っていない。

## 固定ソースの検査

| 検査 | 終了 | 新規 module | 再利用 module | 保存失敗 |
| --- | --- | --- | --- | --- |
| `--module thom_spaces --full-check-local` | 0 | 88 | 1473 | 0 |
| 通常 `scripts/check_all.py libs` | 0 | 0 | 11087 | 0 |

所有88モジュールをソースから再検査した後、通常の全体検査は 11,087 対象すべてを受理した。
全体検査の破損キャッシュ読み取りは 0、worker 復旧は 0、最大 RSS は約 1290 MiB、所要時間は約 193.3 秒である。
source 検査ステップ・重複・再実行・失われたステップと checkpoint の実数は `focused-report.json.gz`、`whole-report.json.gz`、`attempts.json` に保存した。
全体検査は初回記録と異なり worker 復旧がない。

次の依存回帰と所有パッケージの通常キャッシュ検査を、同じ全体検査内の root scope で実行した。
各 root は子 module と参照先を含む。

| root scope | 終了 | 新規 | 再利用 | 保存失敗 |
| --- | --- | --- | --- | --- |
| `topological_algebra` | 0 | 0 | 278 | 0 |
| `bundle_complements` | 0 | 0 | 648 | 0 |
| `bundle_homotopy` | 0 | 0 | 887 | 0 |
| `puppe_sequences` | 0 | 0 | 427 | 0 |
| `thom_spaces` | 0 | 0 | 1561 | 0 |

## 対象・ソース・バイナリの対応

全体 snapshot の 9,888 ファイルの内容を、検証コミットの Git blob と1件ずつ照合して一致を確認した。
`source-files.json.gz` はその相対パスと SHA-256、`targets.json.gz` は順序を含む全対象の記録である。

| snapshot | 開始 SHA-256 | 終了 SHA-256 |
| --- | --- | --- |
| 所有 package と依存 | `939b10ce817e4178f65264e402feed058deebbe6ecf82a2b11aaf3d4a994f8fd` | `939b10ce817e4178f65264e402feed058deebbe6ecf82a2b11aaf3d4a994f8fd` |
| workspace | `5d52264fd735b32c3d9ecab181ab0117c20f6f32d328baf1e9584c077f6571f2` | `5d52264fd735b32c3d9ecab181ab0117c20f6f32d328baf1e9584c077f6571f2` |

開始・終了 snapshot の JSON 内容はそれぞれ一致した。
全体ドライバは終了時に対象リストの一致と全対象の coverage も確認した。
対象リストの SHA-256 は `756c2d15f1316bac717fad945d3a036679a12b2bf45e4b6ecff22dbbd612da3d`、ドライバの SHA-256 は `b0b7159aa8440dd12d090fdb29cc61df4d7db29c8e58b11c335e8126b7e9ef9f` である。
所有 package の終了 snapshot 採取は `--parse-only --save-source-snapshot` で終了0であり、今回は失敗や再試行はない。

```sh
target/release/cli libs/topology/thom_spaces --module thom_spaces --full-check-local --memory-mib 12288 --cache-budget-mib 12288 --cache-stats --save-source-snapshot work/c02/continuation-focused-source.json --report-json work/c02/continuation-focused.json
python3 scripts/check_all.py libs --binary target/release/cli --state-dir work/c02/continuation-whole --memory-mib 12288 --initial-memory-mib 12288 --cache-budget-mib 12288
```

開発中の実行は `preliminary-runs.json` に終了コードと結果・新規/再利用・保存失敗・エラーを記録した。
これらは編集途中のソースに対する結果であり、固定ソースの検証とは区別する。
再帰的な大きな型を直接生成する試みは処理系に受理されなかったが、比較には任意の懸垂表示の列に関する帰納的定理を使い、この表現上の問題を回避した。
この問題を有限 CW 対の未実装理由にはしていない。

有限 CW 対の残る証明では、セルごとの束自明化から球面束のセルを貼るだけでは、セル境界が低次元骨格に入るという CW の条件は導けない。
現行の `FiniteBase.diskType` は円板束と底との同値であり、球面束を含む対の模型ではない。
一般の cellular approximation と有限ホモトピー貼り合わせを含む構成を完成できておらず、有限 CW 対の完成や処理系・体系の致命的制限は主張しない。
環境・権限・ネットワークによる拒否は発生していない。

この記録を追加するコミットでは proof ソースと manifest を変更しない。
