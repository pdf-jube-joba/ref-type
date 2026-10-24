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

`Spectral.At.Eigenvalues` はこの条件と「単位円上の固有ベクトルは零」を相互に導く。
`Spectral.InFrame` と `FiniteSpace.On` は有限枠を通して射影を移し、枠によらない一意な写像を選ぶ。

## 連続な族と束（追加部分は検査中）

| 公開入口 | 内容 |
| --- | --- |
| `At.Continuous` / `Bundle` | 連続な射影、内側と補側の像束、包含・射影、直和分解 |
| `Comparison` / `FiniteSpace.On.Naturality` | intertwiner と射影の可換性 |
| `Idempotents.Image` | 自己共役性を仮定しない連続冪等射影の像束 |
| `Idempotents.Comparison` / `Gap` | 近接する冪等射影の像の比較同型と可逆領域の開性 |
| `Idempotents.Homotopy` / `At.Homotopy` | コンパクトな底空間上のホモトピーの両端の像束の同型 |
| `BundleCoordinates` | 束写像の局所行列と係数の連続性 |
| `BundleImage` / `Pullback` | 束の冪等写像の像の局所自明化と引き戻し比較 |
| `BundleEndomorphism` / `Naturality` / `Pullback` | スペクトル射影の貼り合わせ、像の部分束、自然性 |

近接比較には \(H=QP+(I-Q)(I-P)\) を用いる。
\(Q=P\) では恒等写像であり、可逆な範囲で \(HP=QH\) から像束の同型を得る。
コンパクトな底空間では tube lemma で時間の共通近傍を取り、区間の細分で両端の比較同型を合成する。
一般の束の像の局所自明化は、元の束の枠でこの行列の構成を適用し、開部分空間のチャートを底空間へ持ち上げて作る。

## 利用例（検査中）

`Examples.Empty` は零次元の射影を構成する。
`Examples.MovingNilpotent` は \(T_a=\begin{pmatrix}0&a\\0&0\end{pmatrix}\) を複素平面上で動かし、\(T_a^2=0\) からスペクトル条件を導いて像束を構成する。
その `Homotopy` は区間上の族にも適用し、両端の像束の比較を使用する。

## 検証と再開

基点は main `6bf92837`、作業は `math/k06-spectral-splitting`、[draft PR #42](https://github.com/pdf-jube-joba/ref-type/pull/42)。
K06 は実装中であり、B04・K01・K04 には着手していない。
最新の変更は WIP として commit・push し、リモートの HEAD を照合して保存している。

| コミット | 保存終了まで確認した検査範囲（`spectral_splitting.Spectral` 以下） | module 数 | 終了コード |
| --- | --- | --- | --- |
| `696c8da2` | `At.Splitting.Separated` | 557 | 0 |
| `696c8da2` | B03 の `Finite`（共通化した基底構成） | 445 | 0 |
| `a1f16544` | `At.Continuous`（当時の連続射影と像束） | 675 | 0 |
| `89233a89` | `Comparison`（行列の intertwiner 自然性） | 564 | 0 |
| `0b10d2dc` | `FiniteSpace`（枠によらない一意な射影） | レポート参照 | 0 |
| `15a2b0b2` | `At.Eigenvalues`（固有値条件との同値性） | 577 | 0 |
| `11c2c7e2` | `FiniteSpace.On.Naturality`（任意の有限枠間の自然性） | 642 | 0 |
| `b35d1902` | `BundleImage`（局所自明化・包含・射影・引き戻し比較） | 721 | 0 |
| `4e69b3ce` | `BundleCoordinates`（局所行列と係数の連続性） | 606 | 0 |
| `8d8d09ab` | `Idempotents.Homotopy`（像束比較・近接比較・区間の細分） | 655 | 0 |
| `16a4a25f` | `InFrame`（スペクトル条件の枠変更を含む） | 602 | 0 |

Bézout 分解、Horner 評価、単位円内外の根因子と係数の連続性も、各対象と参照依存先の検査で終了コード0を確認した。
最後の全体検査は未完了であり、上表を package 全体の成功とは扱わない。

`Idempotents.Comparison`・`Gap`・`Homotopy`・`IntervalRelations` は上表の検査で成功した。
`BundleCoordinates` と `BundleImage` は上表の検査で成功した。
`BundleEndomorphism`（自然性・引き戻し比較を含む）と具体例、および補射影・直和分解の追加は構文解析のみ成功し、型検査は未完了である。
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

次は `BundleEndomorphism` と具体例・直和分解を型検査する。
残作業は、一般の束の貼り合わせ・自然性とホモトピー比較の検証、引き戻し比較、具体例、公開 API・下流リンクの整備、対象・全依存閉包・影響する下流・workspace の最終検査である。
