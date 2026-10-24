# 連続なスペクトル分離（K06、実装中）

計画は [_plans/math/k06-spectral-splitting.md](../../../_plans/math/k06-spectral-splitting.md)。
[根群](../complex_polynomial_roots/README.md)、[多項式線形代数](../polynomial_linear_algebra/README.md)、[Hermitian 局所枠](../hermitian_frames/README.md)、[束の補空間](../../geometry/bundle_complements/README.md) を再利用する。

## 射影の構成

特性多項式を単位円の内側の根因子 \(p\) と外側の根因子 \(q\) に分ける。
共通根がないことから Bézout 係数 \(up+vq=1\) を構成し、Cayley–Hamilton を適用して \(P=v(T)q(T)\)、\(R=u(T)p(T)\) による分解を得る。
この射影は Bézout 係数の選び方に依存しない。
評価和 \(M=p(T)+q(T)\) の逆を分解上で構成すると、同じ射影は \(P=q(T)M^{-1}\) と書ける。
連続性にはこの逆行列の式を使う。
根の並べ方によらない因子を K05 の局所的な連続因子と比較し、Horner 評価と逆行列の連続性を接続する。

| 公開入口 | 内容 |
| --- | --- |
| `Spectral.Action.With` | Bézout 射影・補射影、核での計算、独立性 |
| `Spectral.At.Characteristic` | 有限係数表示、最高次係数1、係数族の連続性 |
| `Spectral.Circle.At` | 根の順序に依存しない内外の因子と互いに素性 |
| `Spectral.At.Splitting.Separated` | 単位円上に根がない行列の射影、冪等性、核への包含 |

連続な族・基底変更・像束の追加 API は検査中である。

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
| `6c38873e` | `Coefficients`（有限係数演算・連続性） | 481 | 0 |
| `cc4979b4` | `At.Characteristic`（最高次係数・連続性） | 525 | 0 |
| `cc4979b4` | `At.Splitting --module-only`（可逆性まで） | 555 | 0 |
| `696c8da2` | `At.Splitting.Separated`（射影の法則） | 557 | 0 |

その後の並び方に依存しない因子、局所根群との比較、行列式の係数写像・特性多項式の係数と連続性、連続射影・自然性は package 全体として未検証である。
最後に終了を確認した全体検査は `fd9434df` で終了コード1、`At.Characteristic.leading` の推論で失敗した。
有限多重和に渡す関数を明記した `2c6931cb` の全体検査は22分後に診断のため中断し、終了コード130を確認した。
worker 2、checkpoint からの再開1回、最後の module は `At.Splitting.Separated`、未保存ステップ638であり、検証未完了である。
再開の原因はこの記録だけでは確定していない。
それ以降に `bundle_complements.Finite.ImageBasis` の切り出し、一般の冪等射影の像束・引き戻し比較、スペクトル像束への包含・射影を追加した。
これらの追加は構文解析のみ成功し、型検査は未実施である。
`696c8da2` では逆行列の法則を明示する証明へ変更し、同じ射影の法則が保存処理・正常終了まで完了した。
型の再帰での大きな除去は固定長ベクトルで回避した。

検査コマンドは以下を基準とする。
実行時には `--source-snapshot` で検査対象を固定し、`--report-json` も指定している。
生成 snapshot・JSON・ログは追跡しない。

```sh
target/debug/cli libs --parse-only --save-source-snapshot /tmp/k06-sources.json
target/debug/cli libs --module spectral_splitting.Spectral.Coefficients \
  --source-snapshot /tmp/k06-sources.json --memory-mib 8192 --diagnostics compact --cache-stats
```

次は `REF_TYPE_PROFILE_PROGRESS=1` で module 進捗を記録し、`bundle_complements` の `Finite.ImageBasis`・`ProjectionBasis` を検査する。
その後 `At.Continuous`・`Comparison` と package 全体を検査する。
残作業は追加済みの連続射影・自然性・像束の検証、一般の束の局所構成の貼り合わせ・ホモトピー比較、具体例、公開 API の整備と全依存・下流・workspace の最終検査である。
K06 は未完成であり、B04・K01・K04 には着手していない。
