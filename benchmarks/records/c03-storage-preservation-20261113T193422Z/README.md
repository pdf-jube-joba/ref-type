容量保護で停止した C03 統合検査の保全記録です。

records.tar.gz は原報告・固定 source snapshot・受理済み scope 報告・停止 scope・checkpoint manifest を保持します。
manifest.json に各原ファイルの SHA-256、summary.json に archive と checker/source/driver の fingerprint を記録しています。
全項目を archive から読み戻してハッシュ一致を確認しました。
cache の object 本体と検証済み checker は元 workspace で保持しています。
展開先には空ディレクトリを使い、原ファイルへ上書きしないでください。
