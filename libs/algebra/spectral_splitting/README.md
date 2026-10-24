# 連続なスペクトル分離（K06、実装中）

計画は [_plans/math/k06-spectral-splitting.md](../../../_plans/math/k06-spectral-splitting.md)。
[根群](../complex_polynomial_roots/README.md)、[多項式線形代数](../polynomial_linear_algebra/README.md)、[Hermitian 局所枠](../hermitian_frames/README.md)、[束の補空間](../../geometry/bundle_complements/README.md) を再利用する。

## 検証と再開

基点は main `6bf92837`、作業は `math/k06-spectral-splitting`、[draft PR #42](https://github.com/pdf-jube-joba/ref-type/pull/42)。
開始時にリモートの既存ブランチ・open PR と4計画を確認し、重複する作業がないことを確認した。
Bézout 射影と独立性、Cayley–Hamilton による評価和の逆行列、Horner 評価の連続性、共通根がない場合の互いに素性、単位円内外の根因子の分離を構成した。
以下は保存処理を含むプロセスの終了を確認した範囲である。

| コミット | 検査範囲 (`spectral_splitting.Spectral` 以下) | module 数（新規＋再利用） | 終了コード |
| --- | --- | --- | --- |
| `17f58311` | 当時の package 全体（逆行列による射影まで） | 464 | 0 |
| `267739bb` | `At.Families` | 510 | 0 |
| `742fb3de` | `Coprime` | 474 | 0 |
| `999005ab` | 当時の `Circle` | 507 | 0 |

その後の並び方に依存しない因子、局所根群との比較、有限係数演算・行列式の係数写像・特性多項式の係数と連続性は未検証である。
最後に終了を確認した検査は `18a49375` の `Coefficients` で終了コード1、`Families.constantAddition` の証明引数の型推論で失敗した。
`2266e494` で引数の型を明記し、同範囲を再検査中である。
型の再帰での大きな除去は固定長ベクトルで回避した。

検査コマンドは以下を基準とする。
実行時には `--source-snapshot` で検査対象を固定し、`--report-json` も指定している。
生成 snapshot・JSON・ログは追跡しない。

```sh
target/debug/cli libs --parse-only --save-source-snapshot /tmp/k06-sources.json
target/debug/cli libs --module spectral_splitting.Spectral.Coefficients \
  --source-snapshot /tmp/k06-sources.json --memory-mib 8192 --diagnostics compact --cache-stats
```

次は実行中の検査の終了コードを確認し、残る型エラーを修正する。
その後 `At.Weights`、`Circle`、`At.Characteristic` を検査し、局所的な連続評価を逆行列によるスペクトル射影へ接続する。
残作業は連続射影・基底変更の自然性、束への貼り合わせ・像の局所自明化・ホモトピー比較、具体例、公開 API の整備と全依存・下流・workspace の最終検査である。
K06 は未完成であり、B04・K01・K04 には着手していない。
