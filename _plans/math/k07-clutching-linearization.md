# K07 clutching の安定線形化

## 要件

- 主な実装先は `clutching_linearization`。
- コンパクト Hausdorff 空間と円周の積上の clutching 自己同型を Laurent 多項式で近似し、ホモトピーを構成する。
- 自明束の追加とブロック行列操作による安定線形化を証明し、スペクトル分離による束の差へ変換する。
- 変換の選択独立性、直和との整合性、基本積定理の逆写像に必要な相互逆の等式を公開する。

## 依存するタスク

- [K04 Stone–Weierstrass と Laurent 近似](../../libs/analysis/uniform_approximation/README.md)
- [連続なスペクトル分離と像束の比較](../../libs/algebra/spectral_splitting/README.md)
- [B04 束のホモトピー不変性と clutching](../../libs/geometry/bundle_homotopy/README.md)
- [K01 束の Grothendieck 環と安定同型判定](../../libs/topology/k_theory/README.md)

## 作業引き継ぎ（2026-10-25）

ブランチは `math/k07-clutching-linearization`、開始点は最新 main `744d501e7ac1bcb762109195ad9f5a9a38df2d5c`。
`AGENTS.md`、`src/USAGE.md`、ロードマップ、K07・K02・B09・K03 の計画と依存先の公開 README を確認した。
K07 では Laurent 係数・行列近似、clutching ホモトピー、スペクトル射影、K0 の公開ソースも確認した。
リモートの heads と `refs/pull/*/head` には今回の4単位に対応する参照がなく、PR の参照は #45 までであった。

`git fetch origin` と `git pull --ff-only origin main` は終了0、main は開始点と一致した。
`gh pr list --repo pdf-jube-joba/ref-type --state all --limit 40 --json number,title,state,headRefName,mergeCommit` は終了1（GraphQL `Forbidden`）。
`gh api 'repos/pdf-jube-joba/ref-type/pulls?state=all&per_page=15'` も終了1（`Forbidden`）。
認証情報を送らない `curl --max-time 20 https://api.github.com/repos/pdf-jube-joba/ref-type/pulls` は終了56（`CONNECT tunnel failed, response 403`）。
Git 接続は成功するが API の許可を確認できず、既存 PR・CI・マージ状態の確認は未完了である。
環境の状態確認は connected / running、HTTP policy の観測状態は unknown であり、拒否の根本原因は確定していない。
クラウド環境の許可先に `api.github.com` を追加する設定の確認を依頼した。

数学実装・利用例・package 登録・新規 PR はまだない。
このブランチで成功を確認した型検査はなく、未検証の数学ソース変更もない。
前回の検証記録は [K04 の README](../../libs/analysis/uniform_approximation/README.md#利用例と検証・再開) にあり、今回の検証とは区別する。
次は API の接続設定反映後に既存 PR と #42〜#45 の統合状態を確認し、最新 main との差分を再確認して K07 の実装へ進む。
K07 の検証・PR・通常のマージと main への反映確認後、K02、B09、K03 を順番に実施する。
