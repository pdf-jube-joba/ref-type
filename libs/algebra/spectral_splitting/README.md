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
| `BundleHomotopy` | コンパクト Hausdorff 底上で、一般の束のスペクトル像の両端を比較 |

近接比較には \(H=QP+(I-Q)(I-P)\) を用いる。
\(Q=P\) では恒等写像であり、可逆な範囲で \(HP=QH\) から像束の同型を得る。
コンパクトな底空間では tube lemma で時間の共通近傍を取り、区間の細分で両端の比較同型を合成する。
一般の束の像の局所自明化は、元の束の枠でこの行列の構成を適用し、開部分空間のチャートを底空間へ持ち上げて作る。
一般の束のホモトピーでは、円柱上の像束に B03 の有限埋め込みを適用し、射影族の比較を埋め込み像との同型と合成する。
行列族では底のコンパクト性を使い、一般の束では有限埋め込みの存在にコンパクト Hausdorff 性を使う。

## 利用例（検査中）

`Examples.Empty` は零次元の射影を構成する。
`Examples.MovingNilpotent` は \(T_a=\begin{pmatrix}0&a\\0&0\end{pmatrix}\) を複素平面上で動かし、\(T_a^2=0\) からスペクトル条件を導いて像束を構成する。
その `Homotopy` は区間上の族にも適用し、両端の像束の比較を使用する。
`Examples.MixedRanksHomotopy` はランク0と1の二つの成分を持つ束を円柱へ引き戻し、零自己準同型のスペクトル像に一般の束の比較を適用する。

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
| `e3aecc2e` | B03 package と全依存閉包 | 4345 | 0 |
| `fea0e38e` | K06 package と全依存閉包（専用 snapshot） | 4765 | 0 |
| `ca460cb5` | `Examples.MixedRanksHomotopy`（ランク0・1の成分を持つ束） | 791 | 0 |
| `7c24d715` | `BundleHomotopy`（一般のスペクトル像束の両端比較） | 944 | 0 |
| `a67dc066` | `EmbeddedCylinder`（埋め込み像・引き戻し・両端の比較） | 771 | 0 |
| `b7470b9c` | `Examples`（零次元・動く冪零行列・両端比較・直和分解） | 781 | 0 |
| `e0ac5797` | `BundleEndomorphism`（貼り合わせ・不変部分束・自然性・引き戻し） | 758 | 0 |
| `11c2c7e2` | `FiniteSpace.On.Naturality`（任意の有限枠間の自然性） | 642 | 0 |
| `b35d1902` | `BundleImage`（局所自明化・包含・射影・引き戻し比較） | 721 | 0 |
| `4e69b3ce` | `BundleCoordinates`（局所行列と係数の連続性） | 606 | 0 |
| `8d8d09ab` | `Idempotents.Homotopy`（像束比較・近接比較・区間の細分） | 655 | 0 |
| `16a4a25f` | `InFrame`（スペクトル条件の枠変更を含む） | 602 | 0 |

Bézout 分解、Horner 評価、単位円内外の根因子と係数の連続性も、各対象と参照依存先の検査で終了コード0を確認した。
K06 package と全依存閉包の検査は上表の範囲で成功した。

`Idempotents.Comparison`・`Gap`・`Homotopy`・`IntervalRelations` は上表の検査で成功した。
`BundleCoordinates` と `BundleImage` は上表の検査で成功した。
`BundleEndomorphism` の貼り合わせ・不変部分束・自然性・引き戻し比較は上表の検査で成功した。
具体例、`At.Homotopy` の接続、直和分解も上表の範囲で検査が成功した。
`PullbackIsomorphism` と `EmbeddedCylinder` も上表の範囲で検証済みである。
`BundleHomotopy` は上表の範囲で検証済みである。
`Examples.MixedRanksHomotopy` も上表の範囲で検証済みである。
追加した構成はそれぞれ上表の対象検査を通過した。
package 全体・全依存閉包の最終検査は終了コード0を確認した。
4,437 module のキャッシュを再利用し、328 module・4,196ステップを検査した。
最大 RSS は5,259,356 KiB、worker は1、復旧・重複・再実行・失われたステップ・保存失敗は0である。
影響する B03 package と全依存閉包も終了コード0を確認した。
workspace 全体の最終検査は未実施である。
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

終了コード0を確認した検査は `target/debug/cli libs/algebra/spectral_splitting --source-snapshot work/k06-package-snapshot.json --memory-mib 8192 --time-limit-seconds 1800 --diagnostics compact --report-json work/k06-package.json --cache-stats` である。
次は `target/debug/cli libs --source-snapshot work/k06-workspace-snapshot.json --memory-mib 8192 --time-limit-seconds 1800 --diagnostics compact --report-json work/k06-workspace.json --cache-stats` を実行し、プロセスの終了と終了コードを確認する。
別環境では同じ package を `--parse-only --save-source-snapshot` で保存し直してから実行する。
残作業は、対象・全依存閉包・影響する下流・workspace の最終検査、公開 API・下流リンク・ロードマップの完了更新と PR の最終確認である。
