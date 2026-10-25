# CW cofibration と Puppe 列（K02、実装中）

入口は `puppe_sequences.Puppe`。
基点は K07 統合済み main `76e6084094f810eaf51e18663bb33d111dd409d7`、作業ブランチは `math/k02-cofibration-puppe`。

最初の証明義務は、既存の cylinder の貼り合わせへの retraction による cofibration の定義と、ホモトピー拡張性の逆方向の同値である。
`Cofibration.fromExtension` は貼り合わせ空間自体への拡張問題を使って retraction を構成する。
`5b7cbe2b` の個別検査は accepted・終了0・保存失敗0。
[PR #47](https://github.com/pdf-jube-joba/ref-type/pull/47) は draft。
`d50d55ce` の円板 scaling 評価、`0c83afde` の radial パラメータの正値性・区間評価、`2e3c2c89` の端点公式、`9f0e1abf` の円板 cylinder の底面・境界への写像は各 accepted・終了0・保存失敗0。
現在はこの写像の連続性を検査し、貼り合わせ空間への retraction に接続する。

次は円板境界の retraction と有限 CW 部分複体への拡張、基点付き mapping cone・reduced suspension の比較、自然性・商との比較・反変 Hom の完全性を依存順に証明する。
共有キャッシュは `libs/refcache`。
