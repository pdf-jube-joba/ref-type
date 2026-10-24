# Stone–Weierstrass と Laurent 近似（K04、実装中）

計画は [_plans/math/k04-uniform-approximation.md](../../../_plans/math/k04-uniform-approximation.md)。
既存の多項式・Laurent 環、実数の連続演算とコンパクト性、束の有限埋め込みを再利用する。

## 検証と再開

基点は K01 統合済み main `f6c3dcfb`、ブランチは `math/k04-uniform-approximation`。
開始時に K04 / Weierstrass の既存ブランチ・PR・実装がないことを確認した。
package・workspace 登録と一様誤差の基本定義は `79470328` の `work/k04-foundation` で保存完了・終了0。
コンパクト性と単調性から点ごとの上界近似を一様化する Dini 型の補題は `52a34f5f` の `work/k04-dini` で保存完了・終了0。
既存の多項式環の評価、絶対値用の反復多項式、1ステップの単調性・誤差因子分解・収縮評価は `3dad0eb1` の `work/k04-polynomial-step` で保存完了・終了0。
数値反復の非負性・上界・単調誤差、幾何級数による点ごとの近似、多項式評価との一致を追加した（未検証）。
[draft PR #45](https://github.com/pdf-jube-joba/ref-type/pull/45) に途中保存する。
残作業は絶対値の近似多項式、実・複素 Stone–Weierstrass、円周・積上の係数付き Laurent 近似、有限成分評価・束自己準同型・可逆性、利用例・全体検証・完了文書・統合。
次は対象スコープを snapshot 化し、共有キャッシュで型検査する。
検査の終了・キャッシュ保存完了が確認できるまでは成功と扱わない。
