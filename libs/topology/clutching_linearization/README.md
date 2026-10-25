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
| `Companion.With.Eigen` | 固有ベクトルから多項式の核への写像、単位円固有値の不在の判定 |
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

| 対象 | 数学入力 | 結果 |
| --- | --- | --- |
| package 全依存閉包 | `a4ead646` | 5,638 module、accepted、終了0、保存失敗0 |
| 全workspace・影響先・例 | `eaa94ba7` | 7,871 module、accepted、終了0、保存失敗0 |
| 最新 K07 全対象・参照先・例 | `95809e5d` | 1,307 module、accepted、終了0、保存失敗0 |
| Rust workspace | 同一処理系 | 383 tests passed、終了0 |
| format / Clippy | 同一処理系 | 全workspace・全targets、警告をエラー化、終了0 |

結果は `/tmp/k07-resume/closure.json`、`workspace-resume.json`、`canonical.json`。
最新 K07 は約244秒、最大RSS 6,373,460 KiB、復旧・重複・lost steps は0。
Clutched・NormalForm・InverseFamily・bundle 比較、自然性・直和・標準モデルの復元と具体例を含む。
全workspace の初回は30分の時間上限で終了2となり、成功扱いせずキャッシュから再開した。
再開後は約728秒で正常終了したが、復旧1回、lost steps 4,740 の記録がある。
最新追加も含めた全workspaceの最終確認を次に実行する。

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

現在の `Construction.inverseClass` は選択した `Parameters` に対する候補であり、選択に依存しない逆写像の定義にはまだなっていない。
必要な接続は次のとおり。

- Laurent shift による円周の冪を K0 の自明束の差へ反映する一般の比較。
- 射影の標準ループの clutching と、像束の差を与える基本積構成との同定。
- 任意の shift・次数・正規化パラメータについての候補の選択独立性。
- 基本積定理に必要な相互逆の等式。

近似間の clutching 束同型、スペクトル族の自然性・直和・ホモトピー不変性、標準モデルの復元は検証済みだが、これらだけでは上記の一般の結論を導けていない。
体系・言語処理系による不可能性が確認されたわけではなく、必要な証明構成が未完成という状態である。
次の実装は標準ループと像束の基本積構成の比較から再開する。
workspace・公開一覧・下流リンク・ロードマップは実装中と表示している。
PR の ready 化と main へのマージは未実施。
