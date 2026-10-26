# 相対 K 群（K03）

基点は B09 の統合済み main `bd8fd86d5368968ff22e06f81beb5469bc348623`、ブランチは `math/k03-relative-k`。
[計画](../../../_plans/math/k03-relative-k.md)の実装中で、完成・検証済みの単位ではない。

## 構成と再開

入口は `relative_k_theory.Relative`。
空の閉部分空間も扱うため、まず一点を付加してから閉部分空間とともに潰す。
共通の位相的補題は `Coproduct.Properties` と `Collapse.Closed` に配置する。
次に射影表示による束の三つ組とその関係、商空間の被約群との比較、負次数、完全列・切除・Mayer–Vietoris・外積、円板球面対への適用を構成する。

`Collapse.Closed` は対象検査 accepted・終了0・キャッシュ保存失敗0。
`Coproduct.Properties` は宣言順と開集合の輸送を修正中で、まだ検証済みではない。
束の三つ組、一点付加商、反復 suspension と負次数群は未検証の構成。
対象を保存した `work/k03-resume/foundations.source.json` を使い、各検査には `--source-snapshot` を指定する。
対象検査は `target/debug/cli libs --module topological_constructions.Coproduct.Properties --memory-mib 14336 --cache-dir libs/refcache --cache-budget-mib 16384 --diagnostics compact --report-json work/k03-resume/coproduct.json`。
`Collapse.Closed` も同じ共有キャッシュで検査し、検査結果と終了コードを `work/k03-resume` に保存する。
長い検査には固定 source snapshot を保存し、実行シェルで終了コードもファイルへ保存する。
