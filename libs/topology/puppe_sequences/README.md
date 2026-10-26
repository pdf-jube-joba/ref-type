# CW cofibration と Puppe 列（K02、実装中）

入口は `puppe_sequences.Puppe`。
基点は K07 統合済み main `76e6084094f810eaf51e18663bb33d111dd409d7`、作業ブランチは `math/k02-cofibration-puppe`。

最初の証明義務は、既存の cylinder の貼り合わせへの retraction による cofibration の定義と、ホモトピー拡張性の逆方向の同値である。
`Cofibration.fromExtension` は貼り合わせ空間自体への拡張問題を使って retraction を構成する。
`5b7cbe2b` の個別検査は accepted・終了0・保存失敗0。
[PR #47](https://github.com/pdf-jube-joba/ref-type/pull/47) は draft。
`d50d55ce` の円板 scaling 評価、`0c83afde` の radial パラメータの正値性・区間評価、`2e3c2c89` の端点公式、`9f0e1abf` の円板 cylinder の底面・境界への写像は各 accepted・終了0・保存失敗0。
`e4fa67d7` の連続性、`a6aa2276` の閉集合貼り合わせ、`ec1c454d` の `Disk.Boundary.cofibration` と任意の対象へのホモトピー拡張性は各 accepted・終了0・保存失敗0。
`5e7595a2` の `CW.Cylinder.continuous` は accepted・終了0・保存失敗0。
ローカル `5f5def60` の部分複体の内部セルによる被覆・閉性も accepted・終了0・保存失敗0（`cw-subcomplex.json`、302 modules）。
部分複体の追加はリモート `cbd07bdc9cfb6af91678773c9197aae900fbb62a` に保存済み。
`Quotient.Descent` と `CW.Assembly` による骨格 cylinder 上の貼り合わせは accepted・終了0・保存失敗0。
`CW.Subcomplex.Extension` の空骨格とセル単位の拡張（初期値・低次骨格・部分複体上の指定値を保持）も accepted・終了0・保存失敗0。
`CW.Subcomplex.homotopyExtension` と `CW.Subcomplex.cofibration` は、セルの重なり・骨格への貼り合わせ・有限段の帰納法を含め accepted・終了0・保存失敗0（`cw-cofibration.json`）。
基点固定ホモトピー類 `Maps`、基点付き円錐 `ReducedCone`、mapping cone `Cone`、零ホモトピーからの延長と `Cone.Exactness.exact`（反変 Hom の基本三項）は accepted・終了0・保存失敗0（`cone-exactness.json`）。
reduced suspension と接続写像、対の写像による cone・suspension の誘導写像、接続写像との可換性も実装済み。
現時点の `puppe_sequences.Puppe` 全体は accepted・終了0・保存失敗0（`puppe-connecting-naturality.json`）。
比較証明用の `Coproduct.ProductUniversal`、`Pushout.Of.Families`、`RelationQuotient.Families`、`ReducedCone.Contraction` も個別検査 accepted・終了0・保存失敗0。
`Pair.equivalence` は cofibration のホモトピー拡張から商との比較写像の逆と基点固定の両側ホモトピーを構成する。
有限 CW 部分複体の `CW.Subcomplex.Pointed.equivalence` まで accepted・終了0・保存失敗0（`cw-pointed-comparison.json`）。
次は反復 cofiber と suspension の比較・Puppe 列全体、具体例・最終 workspace 検証へ進む。

次は有限 CW 部分複体への拡張、基点付き mapping cone・reduced suspension の比較、自然性・商との比較・反変 Hom の完全性を依存順に証明する。
共有キャッシュは `libs/refcache`。
