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
K06 は実装中であり、B04・K01・K04 には着手していない。
最新の変更は WIP として commit・push し、リモートの HEAD を照合して保存している。

| コミット | 保存終了まで確認した検査範囲（`spectral_splitting.Spectral` 以下） | module 数 | 終了コード |
| --- | --- | --- | --- |
| `696c8da2` | `At.Splitting.Separated` | 557 | 0 |
| `696c8da2` | B03 の `Finite`（共通化した基底構成） | 445 | 0 |
| `a1f16544` | `At.Continuous`（連続射影と自明な周囲束内の像束） | 675 | 0 |
| `89233a89` | `Comparison`（行列の intertwiner 自然性） | 564 | 0 |
| `0b10d2dc` | `FiniteSpace`（枠によらない一意な射影） | レポート参照 | 0 |
| `15a2b0b2` | `At.Eigenvalues`（固有値条件との同値性） | 577 | 0 |
| `16a4a25f` | `InFrame`（スペクトル条件の枠変更を含む） | 602 | 0 |

Bézout 分解、Horner 評価、単位円内外の根因子と係数の連続性も、各対象と参照依存先の検査で終了コード0を確認した。
最後の全体検査は未完了であり、上表を package 全体の成功とは扱わない。

追加した `Idempotents.Comparison`・`Gap`・`Homotopy`・`IntervalRelations` と `BundleCoordinates`・`BundleImage`・`BundleEndomorphism`・`FiniteSpace.On.Naturality` は、構文解析のみ成功し、型検査は未完了である。
`Idempotents.Comparison` の線形写像構造体指定と制限されたファイバー上の法則は、検出した型エラーを修正した。
`Homotopy` の最後の検査は終了コード1（`Isomorphism` の時間パラメータの型不一致）であり、明示した時間引数・ファイバー族に修正して再検査中である。
以前の全体検査の終了コード130は診断のための中断である。
worker の checkpoint 再開が1回あったが、その原因は確定していない。
逆行列の法則を明示する証明に変更後、該当する `Separated` は保存処理と正常終了まで確認できた。

検査は次の形式で共有キャッシュとソース snapshot を使う。
生成 snapshot・JSON・ログは追跡しない。

```sh
target/debug/cli libs --parse-only --save-source-snapshot work/k06-sources.json
REF_TYPE_PROFILE_PROGRESS=1 target/debug/cli libs \
  --module spectral_splitting.Spectral.Idempotents.Homotopy \
  --source-snapshot work/k06-sources.json --memory-mib 8192 \
  --time-limit-seconds 300 --diagnostics compact --cache-stats \
  --report-json work/k06-check.json
```

次は `Idempotents.Homotopy` の再検査の終了結果を確認し、通常の型エラーを修正する。
続いて `BundleCoordinates`、`BundleImage`、`FiniteSpace.On.Naturality`、`BundleEndomorphism` を順に型検査する。
残作業は、一般の束の貼り合わせ・自然性とホモトピー比較の検証、引き戻し比較、具体例、公開 API・下流リンクの整備、対象・全依存閉包・影響する下流・workspace の最終検査である。
