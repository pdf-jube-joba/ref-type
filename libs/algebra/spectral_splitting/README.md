# 連続なスペクトル分離

K06 の公開入口は `spectral_splitting.Spectral`。
実装済み単位の一覧は [ロードマップ](../../../_plans/math/_roadmap.md) を参照する。
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

## 連続な族と束

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

## 利用例

`Examples.Empty` は零次元の射影を構成する。
`Examples.MovingNilpotent` は \(T_a=\begin{pmatrix}0&a\\0&0\end{pmatrix}\) を複素平面上で動かし、\(T_a^2=0\) からスペクトル条件を導いて像束を構成する。
その `Homotopy` は区間上の族にも適用し、両端の像束の比較を使用する。
`Examples.MixedRanksHomotopy` はランク0と1の二つの成分を持つ束を円柱へ引き戻し、零自己準同型のスペクトル像に一般の束の比較を適用する。

## B09 向けの射影回復と共役

`Circle.At.domainOff` は、単位円を避ける領域の点から `OffSpectrum` を得る。
`At.Neighborhood.open` は、行列空間内で単位円上のスペクトルを避ける領域が開であることを与える。
`At.ProjectionRecovery[P, idempotent]` は \(2(I-P)\) の行列、単位円を避ける証明、スペクトル射影を \(P\) に戻す `recovers` を公開する。
`Conjugation.At.On[A, off, real].natural` は、実行列の作用と座標ごとの共役が可換なら、そのスペクトル射影も共役と可換であることを示す。
これらは [B09](../../geometry/bundle_extension/README.md) の実・複素束の近傍延長に用い、追加分の検証記録は同 README にまとめる。

## 検証と再開

K06 の構成・証明・自然性・比較・利用例は完了した。
K06 統合時の数学コードは `1b012836`、workspace の最終検証は `cdc57da7` と同一の数学入力であった。
ブランチは `math/k06-spectral-splitting`、統合状態は [PR #42](https://github.com/pdf-jube-joba/ref-type/pull/42) を参照する。
Rust の変更はない。

| 検査（いずれも共有キャッシュ） | module 数 | 終了コード |
| --- | ---: | ---: |
| `target/debug/cli libs/algebra/spectral_splitting --memory-mib 8192 --cache-stats` | 4,765（328 checked、4,437 reused） | 0 |
| `target/debug/cli libs/geometry/bundle_complements --memory-mib 8192 --cache-stats` | 4,345 reused | 0 |
| `target/debug/cli libs --memory-mib 8192 --cache-stats` | 7,441 reused | 0 |

実行時には入力ごとの `--parse-only --save-source-snapshot` でソースを固定し、同じ入力位置に `--source-snapshot`・`--diagnostics compact`・`--report-json` を指定した。
生成 snapshot・JSON・ログは追跡しない。
K06 と全依存の検査は4,196ステップ、最大 RSS は5,259,356 KiBであった。
各プロセスの終了と終了コード0を確認し、worker は1、復旧・重複・再実行・失われたステップ・キャッシュ保存失敗はすべて0である。
B03 の基底構成の共通化、全依存、下流の接束・法束などの利用箇所も含む。

次の手順は PR #42 の差分・CI・統合状態と main への反映を確認し、最新 main 上で B04 の計画とこの公開 API を読むことである。
B04・K01・K04 の実装は、この K06 の作業には含めていない。
