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
降下のファイバー検査は基点判定の型注釈不足で終了1となり、注釈を補った。
次の検査は近傍の枠で親の `Fiber` 定義と import alias が衝突して終了1となり、alias を `FiberModel` へ変更した。
B09 の指定同型の近傍延長から、商の基点の開近傍とその上の枠を構成した。
一点付加商の基点の補集合と元の閉部分空間の補集合の同相も構成した。
降下のファイバー・近傍の枠 `Relative.Descent` と基点外の同相 `Relative.Pair.Quotient.Outside` は、`work/k03-resume/outside-batch-*` で accepted・終了0・キャッシュ保存失敗0。
束としての貼り合わせ、元の束との比較と商群比較はまだ未完成。
共通 API `Atlas.Using.Overlap` と `fromTransitions` を追加し、最初の検査で残っていた cocycle 用の参照名を修正した（終了1）。
基点外のファイバー比較を任意の代表点で使えるように整理し、近傍の座標の読み書きの連続性を追加した。
座標の読み書き `Relative.Descent` は `coordinates-batch-Descent` で accepted・終了0・キャッシュ保存失敗0。
座標変換の共通 API の検査は、基点の型が部分空間の要素であることを保持しきれず終了1となり、型を修正した。
商上の近傍の枠と基点外の元のチャートからなる開被覆を構成し、元の束の座標の読み書きの連続性を共通化した。
これらの新しい被覆と共通 API は未検証。
次は座標変換と `Relative.Descent` を固定 snapshot と共有キャッシュで順番に検査する。
崩壊商の基点の補集合と元の閉部分空間の補集合の同相 `Collapse.Outside` を追加し、これも未検証。
検査には最新の `work/k03-resume/descent-cover-regular.source.json` を使う。
各検査には `--source-snapshot` を指定する。
作業の保存先は [Draft PR #50](https://github.com/pdf-jube-joba/ref-type/pull/50)。
対象検査は `target/debug/cli libs --module topological_constructions.Coproduct.Properties --memory-mib 14336 --cache-dir libs/refcache --cache-budget-mib 16384 --diagnostics compact --report-json work/k03-resume/coproduct.json`。
`Collapse.Closed` も同じ共有キャッシュで検査し、検査結果と終了コードを `work/k03-resume` に保存する。
長い検査には固定 source snapshot を保存し、実行シェルで終了コードもファイルへ保存する。
