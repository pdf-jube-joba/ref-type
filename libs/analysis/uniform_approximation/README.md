# Stone–Weierstrass と Laurent 近似（K04、実装中）

計画は [_plans/math/k04-uniform-approximation.md](../../../_plans/math/k04-uniform-approximation.md)。
既存の多項式・Laurent 環、実数の連続演算とコンパクト性、束の有限埋め込みを再利用する。

## 検証と再開

基点は K01 統合済み main `f6c3dcfb`、ブランチは `math/k04-uniform-approximation`。
開始時に K04 / Weierstrass の既存ブランチ・PR・実装がないことを確認した。
最後に成功した対象検査は `35afb0ae` の `work/k04-finite`（終了0・キャッシュ保存完了）。
絶対値近似・実と複素 Stone–Weierstrass・連続係数関数環・Laurent 帰納法と評価・円周とコンパクト Hausdorff 底の積上の係数付き Laurent 近似まで検証した。
先行した検査の API 参照名と部分型の中間等式のエラー（終了1）は修正・再検証済み。
円周単独の近似を複素数係数の既存 Laurent 環へ翻訳する部分まで検証済み。
有限個の関数・行列成分の同時近似と引き戻しの自然性まで検証済み。
有限和・行列作用の成分誤差評価、射影による誤差増幅評価、行列式の一様な可逆性余裕は追加済み・未検証。
`work/k04-matrix-bounds` は参照名、以後の行列検査は暗黙型推論で終了1となり、中間式を明示して修正中。
B03 の座標族の束写像を `CoordinateFamily` に共通化し、有限埋め込みの分裂から自己準同型を行列へ移し、近似後に束へ戻す構成と誤差評価を追加した状態は未検証。
[draft PR #45](https://github.com/pdf-jube-joba/ref-type/pull/45) に途中保存する。
残作業は円周単独版の検証、有限成分評価・束自己準同型・可逆性、自然性・利用例・全体検証・完了文書・統合。
次は `cli libs --parse-only --save-source-snapshot` の後、`cli libs --source-snapshot … --module uniform_approximation --memory-mib 8192 --cache-budget-mib 12288 --time-limit-seconds 900 --report-json …` で対象を検査する。
検査の終了・キャッシュ保存完了が確認できるまでは成功と扱わない。
