# C02 CW 基盤の途中検査

`preliminary.json` に通常のソース付きキャッシュ検証の計数を保存する。
最新の検査は `native-pairs-focused` であり、対応する数学ソースの commit を JSON に記録した。
実行コマンドは `target/release/cli libs/topology/thom_spaces --module thom_spaces --memory-mib 12288 --cache-budget-mib 12288 --cache-stats --diagnostics compact --report-json work/c02/cw/native-pairs-focused.json`。
ソースの編集はこの検査が終了してから再開した。
この検査は終了コード0で、336 module を検査し、1596 module を再利用した。
ソース段階は4214、キャッシュ保存失敗・破損・復旧・再実行・失われた段階は0である。

これは有限 CW 対の構成中の検査であり、C02 の完成後の全体検査を置き換えない。
旧ソースの通常全体検査は `../continuation/` に残している。
`--module` を指定しなかった途中検査 `sphere-global-package` は、依存先 `sphere_maps.Circle.Powers.Actions.DegreeZero` の12行で参照スコープのエラーとなった。
この依存 module を対象にした通常の検査は935 module を再利用して終了コード0となった。
数学ソースと処理系の修正は加えず、完成後の通常全体検査で再確認する。

各行の `checking` は検査全体の計数であり、`owned_new_log_lines` はログ上の `thom_spaces` の新規検査行数である。
`source_correspondence` が途中の作業木と記される古い module 検査には、独立した全入力 snapshot がない。
完成後の検査では対象・バイナリ・commit と開始終了 snapshot の一致を改めて記録する。
