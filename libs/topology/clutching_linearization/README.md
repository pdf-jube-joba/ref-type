# clutching の安定線形化（K07、実装中）

入口は `clutching_linearization.Linearization`。
K04 の Laurent 近似、K06 のスペクトル分離、K01 の束の同型類と K0 を再利用する。

| API | 構成・証明 |
| --- | --- |
| `Blocks` | 上下の剪断写像、両逆、Schur 補元の分解、可逆な経路 |
| `Uniform` / `MatrixNeighborhoods.Perturbation` | 行列の開近傍の共通誤差幅、コンパクト底上での可逆性の余裕 |
| `On.Matrices.exists` / `Result` | 連続可逆行列族の Laurent 近似、可逆なホモトピー、両端の等式、連続な逆行列と両逆 |
| `LaurentNormal.exists` / `finiteExists` | 負の冪を払った多項式と有限係数表示 |
| `LaurentNormal.Matrices.commonExists` / `finiteMatrixExists` | 全成分に共通の shift・次数・有限係数配列 |
| `Coordinates.At.frame` / `Families` | 有限個の座標ブロックの比較同型と族の連続性 |
| `Companion.FromRow.Eigen` | 固有ベクトルから多項式の核への写像、単位円固有値の不在の判定 |
| `Companion.Families.Separated` / `KClass` | 連続な companion 行列、スペクトル像束とその K0 の差の定義 |
| `On.SpectralIndex.Pullback.naturality` / `Sum.Difference.additivity` | スペクトル束の差の引き戻し自然性と直和加法性 |
| `On.SpectralHomotopy.invariant` | 単位円との分離を保つ行列族の両端の K0 の差の一致 |
| `On.Matrices.Clutched.Scaling` / `Normalized.With.Shifted.Leading.Clutching` | 定数倍・正規化時の摂動による clutching 束比較 |
| `CanonicalProjection.recovered` / `loopRecovery` | 射影から作る行列 \(c(1-P)\) のスペクトル射影・標準ループの復元 |
| `On.CanonicalIndex.recovery` / `ScalarChoice.independent` | 元の像束とスペクトル像束の同型、K0 の復元、補助スカラーの選択独立性 |
| `On.SpectralIndex.Canonical.invariant` / `Examples.Nilpotent.canonicalInvariant` | スペクトル族の標準モデルと具体的な \(c=2\) の利用例 |
| `On.Matrices.Construction.Clutching.shiftedComparisonExists` | 自明束を加えた shifted loop からスペクトル標準形への比較（検証済み） |

`algebra.Polynomial.Over.Finite` は任意の可換環上の有限係数表示・演算・padding を公開する。
既存の体上の `galois` の係数演算と `polynomial_linear_algebra.Field.Representatives.exists` もこの実装を共用する。
K04 の `Circle.Coefficients.valueContinuous` を公開し、評価の連続性を利用する。

## 検証と引き継ぎ

作業は `math/k07-clutching-linearization` / [draft PR #46](https://github.com/pdf-jube-joba/ref-type/pull/46)、基点は main `744d501e`。
退避 head `060c0616` から再開し、数学ソース `95809e5d` まで検証した。
共有キャッシュは `libs/refcache`。

再開後、射影ループのテンソル像束との同型と K0 の積公式を構成した。
`ProjectionBundle.Clutching.With.isomorphismExists`、同 `KClass.comparison`、`SpectralMotion.Normal.Clutched.Product.productFormula` と冪零行列の例は `2626b4f1` までの個別検査で accepted・終了0・保存失敗0。
`d3ff4937` の K07 全対象検査も 1,323 modules、accepted・終了0・保存失敗0。
`83b5da62` では剪断回転を使う安定積経路の連続性と端点等式まで検査済み（`clutching-product.json`、accepted・終了0・保存失敗0）。
積の clutching と直和の安定束同型、被約 K0 の積加法性、円周の冪の帰納公式、ランク \(nk\) による Laurent shift 補正を検証した。
`7b0f8033` の `Leading.KClass.Pullback.reconstruction` は、Laurent clutching を線束の差と引き戻したスペクトル逆クラスの積として復元する（`spectral-reconstruction.json`、accepted・終了0・保存失敗0）。
`d8d4074b` の K07 全対象検査は 1,356 modules、accepted・終了0・保存失敗0・lost steps 0（`reconstruction-full.json`）。
元の近似前のループに対する `Construction.Reconstruction.reconstruction` も含めて検証済み。
一般の選択独立性に向け、`TriangularFamily.With.Additivity.additivity` による三角ブロックのスペクトル K0 加法性を `20544514` まで検証した。
`Companion.FromRow.Factor` は一次因子の多項式等式、状態空間の線形同型、三角作用への共役、単位円上の核の消滅を実装し、`44dab674` の個別検査が accepted・終了0・保存失敗0（`factor-gap.json`）。
`Companion.RowFamilies.Factor` の連続な拡大族、`ProjectionBundle.Into.With.map` の像束への制限、`On.SpectralIndex.Similarity.With.invariant` の連続相似不変性は `85a3762a` までの個別検査が accepted・終了0・保存失敗0。
`b4bbd912` の K07 と全依存閉包は 5,720 modules、accepted・終了0・保存失敗0（`factor-full.json`、約1,047秒）。
`fcefcc54` までに一次因子の座標相似、両方向の連続性、K0 加法公式、内外の因子に対するランク補正後の不変性を検証した（`factor-correction.json`、accepted・終了0・保存失敗0）。
固定次数の行写像ホモトピー、円周上で等しい多項式表示の比較、一次因子の反復とランク補正後の不変性を `4666e415` まで検証した。
コンパクトな底全体の可逆性を保つ小さい正パラメータの選択は `de7503e8` で検証済み。
係数のゼロ拡張と完全な多項式の埋め込み、評価の共同連続性、非零最高次係数による連続正規化、正係数の補間を検証した。
`369d6519` までに小パラメータの外側因子と分母を払った \((1+\delta z)^k\) の評価公式を検証済み（`small-factor-family.json`、accepted・終了0・保存失敗0）。
正規化後の因子の復元、コンパクト底上の因子摂動と端点等式を `74fd5636` まで検査済み。
`20cb1ae7` の `RowOrders` は次数の等式に沿う評価・K0 の移送、任意に大きい共通次数への埋め込み、外側因子追加後の K0 不変性が accepted・終了0・保存失敗0（`common-padding.json`）。
`8a43548e` までに共通次数の係数補正と可逆な因子摂動、正の最高次係数による正規化、両端の monic 係数の復元、円周全体での核の消滅を接続した（`circle-correction.json`、accepted・終了0・保存失敗0）。
`a6d0c52f` の `RowOrders.DegreePair.Homotopy.With.invariant` は、共通次数の可逆な係数ホモトピーが結ぶ異なる次数の両端についてスペクトル K0 クラスの一致を証明する（`degree-homotopy.json`、accepted・終了0・保存失敗0）。
`58f2d50a` の保存済み snapshot に対する K07 と全依存閉包は 5,781 modules、accepted・終了0・保存失敗0、復旧・重複・lost steps 0（`degree-closure.json`、約1,078秒）。
`fea167b6` までの追加は、端点誤差の評価、正の重み付き補間、単位スカラーによる摂動幅の保存、Laurent 係数の再添字付けを個別検査済み（いずれも accepted・終了0・保存失敗0）。
`ab7421f3`（ローカル `6cc419af` と同一 tree）の正係数の多項式補間の K0 比較も検査済み（`degree-segment.json`、accepted・終了0・保存失敗0）。
Git CLI の push が認証エラーとなったため、以後は通常の GitHub 連携で既存ブランチを fast-forward 更新し、tree の一致とリモート head を確認して保存する。
`1f693be9`（ローカル `d6bb5b47` と同一 tree）の `RowOrders.DegreePair.LoopHomotopy.With.invariant` は、任意の連続可逆ループホモトピーが結ぶ monic 多項式のスペクトル K0 クラスの一致を証明する（`loop-homotopy.json`、accepted・終了0・保存失敗0）。
誤差を制御した Laurent 近似、両端の短い正係数多項式経路、零因子のランク補正を接続した。
`1061e488`（ローカル `c0ecae9e` と同一 tree）の `On.Matrices.ChoiceComparison.independent` は、任意の二つの `Parameters` のスペクトル逆クラスが一致することを証明する（`choice-comparison.json`、accepted・終了0・保存失敗0）。
各 monic 多項式を元のループへ結ぶ経路、共通 shift への零因子追加、ランク補正の交換を使用する。
`8fb650cf` の `On.Matrices.Inverse.value` と clutching 復元、`d2ed77a0` の任意の多項式経路表示からの回収、`047b9ffc` の `Inverse.Naturality` と `Inverse.Homotopy` を検証済み（各 accepted・終了0・保存失敗0）。
`54c90213` の `RowOrders.Monic.recovery` と `LinearPolynomial.Index.recovery` は、monic 多項式の逆クラス、特に一次の \(zI-A\) の逆クラスを元のスペクトル指数と同定する（`linear-polynomial.json`、accepted・終了0・保存失敗0）。
次は標準射影ループでの復元と、逆クラスの直和加法性を接続する。
次数の追加は外側の一次因子による companion の安定化、shift の変更は零固有値ブロックの追加、固定次数の補助選択はスペクトルホモトピーで比較する方針。
以下の全workspace結果は再開前の数学入力に対する記録。

| 対象 | 数学入力 | 結果 |
| --- | --- | --- |
| package 全依存閉包 | `a4ead646` | 5,638 module、accepted、終了0、保存失敗0 |
| 最新全workspace・依存閉包・影響先・例 | `0a2e29ec`（数学ソース `95809e5d`） | 7,878 module、accepted、終了0、保存失敗0 |
| 最新 K07 全対象・参照先・例 | `95809e5d` | 1,307 module、accepted、終了0、保存失敗0 |
| Rust workspace | 同一処理系 | 383 tests passed、終了0 |
| format / Clippy | 同一処理系 | 全workspace・全targets、警告をエラー化、終了0 |

結果は `/tmp/k07-resume/closure.json`、`workspace-resume.json`、`canonical.json`、`final.json`。
最新 K07 は約244秒、最大RSS 6,373,460 KiB、復旧・重複・lost steps は0。
Clutched・NormalForm・InverseFamily・bundle 比較、自然性・直和・標準モデルの復元と具体例を含む。
全workspace の初回は30分の時間上限で終了2となり、成功扱いせずキャッシュから再開した。
再開後は約728秒で正常終了したが、復旧1回、lost steps 4,740 の記録がある。
最新追加も含めた全workspaceの最終確認は約23秒、検証済みキャッシュの再利用で正常終了した。
この最終確認の復旧・重複・lost steps は0。

B04 `Clutching.Homotopy.Endpoint.at` を `Pullback.pulledG` の別名に整理し、同じ束の型を繰り返し展開する停滞を解消した。
処理系には `REF_TYPE_PROFILE_CONVERSION` の任意診断を追加したが、型判定規則は変更していない。

再検査コマンド（リポジトリのルートで実行）:

```sh
source /workspace/ref-type-env.sh
cargo build -p cli --locked
target/debug/cli libs --parse-only --save-source-snapshot /tmp/k07-resume/final.source.json
REF_TYPE_PROFILE_PROGRESS=1 target/debug/cli libs --source-snapshot /tmp/k07-resume/final.source.json --memory-mib 10240 --cache-dir libs/refcache --cache-budget-mib 12288 --diagnostics compact --time-limit-seconds 3600 --report-json /tmp/k07-resume/final.json
```

K07 だけを検査する場合は入力を `libs/topology/clutching_linearization` にし、snapshot をその入力から作り、`--module clutching_linearization` を加える。
`--module` を省略すると package 全依存閉包を検査する。
プロセス終了0、report の `outcome=accepted` と `storage.save_failures=0` を確認する。

## 完了に必要な数学的接続

`Construction.inverseClass` の一般の選択独立性は検証済み。
Laurent shift 補正と標準ループの積公式を結合した再構成等式は検証済み。
選択に依存しない逆クラスの公開 API・自然性・ホモトピー不変性・clutching 復元を検証済み。
残るのは標準射影ループ側の復元と、逆クラスの直和加法性の接続、および最新差分の全体検証である。
固定されたスペクトル族の自然性・直和・ホモトピー不変性、標準モデルの復元は検証済み。
一般の選択独立性を再構成の積公式だけから結論することはできないため、companion の一次因子追加と次数・shift の変更の比較を構成する。
workspace・公開一覧・下流リンク・ロードマップは実装中と表示している。
PR の ready 化と main へのマージは未実施。
