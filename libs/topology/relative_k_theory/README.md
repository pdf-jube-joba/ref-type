# 相対 K 群（K03）

基点は B09 の統合済み main `bd8fd86d5368968ff22e06f81beb5469bc348623`、ブランチは `math/k03-relative-k`。
[計画](../../../_plans/math/k03-relative-k.md)の実装中で、完成・検証済みの単位ではない。

## 構成と再開

入口は `relative_k_theory.Relative`。
空の閉部分空間も扱うため、まず一点を付加してから閉部分空間とともに潰す。
共通の位相的補題は `Coproduct.Properties` と `Collapse.Closed` に配置する。
次に射影表示による束の三つ組とその関係、商空間の被約群との比較、負次数、完全列・切除・Mayer–Vietoris・外積、円板球面対への適用を構成する。

`Collapse.Closed` は対象検査 accepted・終了0・キャッシュ保存失敗0。
`Coproduct.Properties` は宣言順と開集合の輸送を修正し、対象検査 accepted・終了0・キャッシュ保存失敗0。
束の三つ組の群表示、直和・合成・ホモトピー・全体に延長する同型の関係式、逆元の比較を追加した。
一点付加商、反復 suspension、負次数群と引き戻しも未検証の構成。
基点付きコンパクト空間の上位宇宙のパッケージは、K02 と同じ継続による表現へ修正した。
`Relative.Suspension` の対象と依存閉包は accepted・終了0・キャッシュ保存失敗0（共有キャッシュ436 module、追加検査4 module）。
一点付加商と負次数群 `Relative.Pair.Quotient` は対象検査 accepted・終了0・キャッシュ保存失敗0。
対の写像が誘導する商写像・負次数の引き戻しを追加した。
引き戻しの恒等則・合成則、B04 によるホモトピー不変性も構成し、これらと三つ組の群は未検証。
三つ組の eta 輸送不足を修正した全入口検査 `work/k03-resume/group-fixed` は accepted・終了0・キャッシュ保存失敗0（追加検査546 module、共有キャッシュ617 module）。
束の降下には、基点での座標と商の各ファイバー上の整合するベクトルを用いる。
そのベクトル空間、従属積の線形代数、基点でのみ値を保つ座標を追加した。
基点での座標空間との線形同型、基点外で元の束のファイバーとの線形同型も追加した。
従属積の最初の検査は親定義への直接参照の解決エラーで終了1となり、既存の `ring.add` 参照へ修正した。
降下のこれらの構成は未検証であり、次は `Relative.Descent` を固定 snapshot と共有キャッシュで検査する。
崩壊商の基点の補集合と元の閉部分空間の補集合の同相 `Collapse.Outside` を追加し、これも未検証。
検査には最新の `work/k03-resume/descent-fibers.source.json` を使う。
各検査には `--source-snapshot` を指定する。
作業の保存先は [Draft PR #50](https://github.com/pdf-jube-joba/ref-type/pull/50)。
対象検査は `target/debug/cli libs --module topological_constructions.Coproduct.Properties --memory-mib 14336 --cache-dir libs/refcache --cache-budget-mib 16384 --diagnostics compact --report-json work/k03-resume/coproduct.json`。
`Collapse.Closed` も同じ共有キャッシュで検査し、検査結果と終了コードを `work/k03-resume` に保存する。
長い検査には固定 source snapshot を保存し、実行シェルで終了コードもファイルへ保存する。
