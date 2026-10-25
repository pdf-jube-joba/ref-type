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
| `On.Matrices.Construction.Clutching.shiftedComparisonExists` | 自明束を加えた shifted loop からスペクトル標準形への比較 |
| `On.Matrices.ChoiceComparison.independent` / `Inverse.value` | Laurent 近似・shift・次数・正規化の選択に依存しない逆クラス |
| `Inverse.Naturality.naturality` / `Inverse.Homotopy.With.invariant` | 連続写像による引き戻し自然性と可逆ループのホモトピー不変性 |
| `On.DirectSum.additivity` | 任意の二つの可逆行列ループの直和に対する逆クラスの加法性 |
| `Inverse.Reconstruction.reconstruction` | 元の被約 clutching クラスを線束の差と逆クラスの積で復元 |
| `On.ProjectionInverse.recovery` / `standardFormula` | 標準ループ \(zP+(1-P)\) の逆クラスが元の像束のクラスと一致 |
| `RowOrders.Monic.recovery` / `LinearPolynomial.Index.recovery` | 多項式表示の回収、特に \(zI-A\) とスペクトル指数の同定 |
| `Examples.Empty` / `Examples.Nilpotent` | 階数0、冪零行列、基本積公式と逆クラス・直和の具体例 |

`algebra.Polynomial.Over.Finite` は任意の可換環上の有限係数表示・演算・padding を公開する。
既存の体上の `galois` の係数演算と `polynomial_linear_algebra.Field.Representatives.exists` もこの実装を共用する。
K04 の `Circle.Coefficients.valueContinuous` を公開し、評価の連続性を利用する。

## 証明の接続

monic companion の一次因子追加を三角ブロックとの連続相似で比較する。
零因子の追加はランク補正を増やし、単位円の外側の因子は補正後の指数を保つ。
一般の可逆ループホモトピーを誤差制御した Laurent 近似へ移し、両端の多項式表示を比較することで選択独立性を得る。
直和では共通 shift・次数の表示を構成し、多項式直和のスペクトル指数加法公式を適用する。
標準射影ループの回収と clutching の積公式が基本積定理の二方向の復元等式を与える。

## 検証と再開

作業ブランチは `math/k07-clutching-linearization`、[PR #46](https://github.com/pdf-jube-joba/ref-type/pull/46)。
共有キャッシュは `libs/refcache`。
GitHub 連携で既存ブランチを fast-forward 更新し、ローカルとリモートの tree の一致を確認して保存している。

| 検査 | 保存済み入力 | 結果 |
| --- | --- | --- |
| K07 全対象・参照先 | `bb2e4c2f` | 1,491 modules、accepted、終了0、保存失敗0 |
| K07 全依存閉包（以前の入力） | `58f2d50a` | 5,781 modules、accepted、終了0、保存失敗0 |
| 全workspace（以前の入力） | `0a2e29ec` | 7,878 modules、accepted、終了0、保存失敗0 |
| Rust workspace・format・Clippy | 同一処理系 | 383 tests passed、format と警告をエラー化した Clippy が終了0 |
| 外側因子による次数調整経路 | `073b61c3` | accepted、終了0、保存失敗0 |
| 行列直和経路・冪の加法則 | `13a479b9` | accepted、終了0、保存失敗0 |
| 多項式直和とブロック行列の同定 | `8bdb90ae` | accepted、終了0、保存失敗0 |

`1972b9e5` の `On.DirectSum.additivity` は accepted・終了0・保存失敗0。
一般の逆クラスの直和加法性まで検証済み。
追加例と最新入力の全workspace検証、CI・PR差分の確認、main へのマージが残る。

```sh
target/debug/cli libs --parse-only --save-source-snapshot /tmp/k07-resume/final.source.json
target/debug/cli libs --source-snapshot /tmp/k07-resume/final.source.json --memory-mib 10240 --cache-dir libs/refcache --cache-budget-mib 12288 --diagnostics compact --time-limit-seconds 3600 --report-json /tmp/k07-resume/final.json
```

K07 だけの場合は入力を `libs/topology/clutching_linearization` とし、`--module clutching_linearization` を加える。
`--module` を省略すると package 全依存閉包を検査する。
プロセス終了0、report の `outcome=accepted`、`storage.save_failures=0` を確認する。
