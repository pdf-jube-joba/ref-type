# C03 基盤の checkpoint 検査

この記録は C03 全体の完了・統合判定ではなく、相対コホモロジーの演算と比較の checkpoint を対象とする。
数学ソース commit は `b31656016`。
検査後の記録追加では数学ソースを変更していない。

`cargo build --release -p cli --locked --offline` は終了コード0。
[入力とコマンド](inputs.json) に checker の SHA-256、追跡対象の数学ソースの集約 digest と実行コマンドを保存した。
[focused report](focused.json) は通常キャッシュを使った検査で `accepted`、終了コード0。
C03 の19 moduleをすべて検証済み集合に含み、139 source stepを新規検査、1553 moduleを再利用した。
worker は1、復旧・失われた step は0、最大 RSS は3143464 KiBだった。

最初の development 検査は既定の3 GiB制限に到達した。
12 GiBでの package 全体検査は C01 の外部積の依存範囲を処理中に中断し、その後、C03 と実際に参照する宣言を対象とした上記の focused 検査へ切り替えた。
package 全体検査と通常の repository aggregate 検査の合格を示す記録ではない。
