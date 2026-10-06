# Ref Type library docs

`libs/` の宣言・署名・コメント・行番号付きソースを読むローカル HTML ブラウザー。
リポジトリのルートから起動する。

```sh
cargo run -p ref-docs
cargo run -p ref-docs -- --libs /path/to/libs --port 8080
```

既定の URL は <http://127.0.0.1:3030/>、`--port 0` は空きポートを選び URL を表示する。
既定のライブラリはビルドした checkout の `libs/` で、`--libs` の相対パスは作業ディレクトリを起点にする。
編集内容の反映にはサーバーを再起動する。

## ドキュメントコメント

宣言の直前の `/* … */` を Markdown として表示する。
連続するコメントは一つの文書にまとめる。

```ref
/* 恒等関数。

引数をそのまま返す。
*/
\definition identity(A: \Set)(x: A): A := x;
```

数式の `\(…\)` / `\[…\]` は TeX のコードとして表示する。
署名は元の source の表記であり、型推論や macro 展開は実行しない。
ファイル名・宣言名・署名・コメントで検索でき、README と外部 module にも移動できる。

起動時の snapshot だけを配信し、隠しファイル・symlink・`refcache/`・`target/`・`node_modules/` は取り込まない。
待ち受けは `127.0.0.1` に限定する。
HTML はエスケープし、画像は代替テキストとして表示する。

## 検証

リポジトリのルートで実行する。

```sh
cargo test -p ref-docs -p syntax --locked
python3 extensions/docs/tests/smoke.py
```

サーバーを起動し、Playwright と Chromium が使える環境では browser test も実行できる。

```sh
DOCS_URL=http://127.0.0.1:3030/ node extensions/docs/tests/browser.cjs
```

外部の Playwright は `PLAYWRIGHT_MODULE`、Chromium は `CHROMIUM_BIN`、画面の保存先は `DOCS_SCREENSHOT` で指定する。
