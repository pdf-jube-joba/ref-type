# Ref Type library docs

`libs/` のライブラリを探索し、宣言の署名、コメント、行番号付きソースをブラウザーで読めます。

## 起動

リポジトリのルートから実行します。

```sh
cd extensions/docs
cargo run
```

[http://127.0.0.1:3030/](http://127.0.0.1:3030/) を開きます。
ルートから `cargo run -p ref-docs` でも起動できます。
Ctrl+C で終了します。

```sh
cargo run -- --port 8080
cargo run -- --port 0
cargo run -- --libs /path/to/libs --port 3030
```

`--port 0` は空きポートを選択し、実際の URL を標準出力に表示します。
既定のライブラリはビルドした checkout の `libs/` で、作業ディレクトリには依存しません。
`--libs` の相対パスは実行時の作業ディレクトリから解釈します。
ポート使用中やディレクトリの読み込み失敗時は、対処方法を含むエラーを表示して終了します。

## ドキュメントコメント

既存の言語構文である `/* … */` を使います。
宣言の直前にあるブロックコメントが文書になります。
空白や改行だけで区切られた連続するコメントは、一つの文書として連結します。

```ref
/* 恒等関数。

引数をそのまま返します。
`A -> A` は関数の型です。

- 型パラメーター: `A`
- 数式の記法: \(\forall x \in A\)
*/
\definition identity (A: \Set): A -> A := \fun (x: A) => x;

/* 基本的な自然数の性質。 */
\module Basic;
```

見出し、段落、リスト、強調、コードブロック、表、リンクなどの Markdown を表示します。
Unicode はそのまま保持し、`\(…\)` と `\[…\]` の数式は TeX 記法を失わないコード表示にします。
TeX の組版エンジンは使用しません。
コメントの区切りも言語の lexer に従うため、開始・終了には上の例のように `/*` と `*/` を独立した記号として書きます。
`///` や `/** … */` はこの言語のドキュメントコメント構文ではありません。

型の表示は元のソースの署名です。
`_` はそのまま表示し、推論後の型やマクロ展開後の宣言を求める型検査は実行しません。
`syntax` の AST と span を使用して、definition、inductive、structure、module、import、macro を一覧にします。
inductive の constructor と structure の field は、型の宣言内に元の記法で表示します。
入れ子の module には目次と個別のアンカーがあり、外部 module は対応するファイルへ移動できます。
コメントのない宣言や空のファイルにも案内を表示し、構文エラーのあるファイルではエラーとソース参照を表示します。

## 探索と安全性

ディレクトリごとの `.ref` と `README.md` を表示します。
全体検索ではファイル名、宣言名、署名、コメントを検索でき、各ファイルにも絞り込みがあります。
複数の検索語はすべて含まれる項目を表示します。
JavaScript が無効でもページを探索でき、ブラウザーの検索を使えます。

起動時にライブラリ全体のスナップショットを作るので、編集後はサーバーを再起動してください。
HTTP の URL はスナップショットの ID を指定し、リクエストからファイルシステムを読みません。
シンボリックリンク、隠しファイル、`refcache/`、`target/`、`node_modules/` は取り込みません。
待ち受けは常に IPv4 loopback の `127.0.0.1` です。

HTML を含むコメントやソースはテキストとしてエスケープします。
Markdown のリンクは HTTP、HTTPS、mailto、ページ内アンカー、索引に含まれるローカルファイル・ディレクトリを対象にします。
ローカルファイルのリンクは対応する閲覧ページへ移動します。
画像は代替テキストとして表示し、外部スクリプトや画像を読み込みません。

## 検証

```sh
cargo test -p ref-docs -p syntax --locked --offline
cargo fmt --all -- --check
cargo clippy --workspace --all-targets --locked --offline -- -D warnings
cargo test --workspace --locked --offline
python3 extensions/docs/tests/smoke.py
```

上の検証コマンドはリポジトリのルートから実行します。
smoke test は `extensions/docs` 内で実際に `cargo run` を起動し、HTTP の探索、全リンク、エスケープ、ポート競合、不正なパスを検証します。

Playwright と Chromium が利用できる環境では、サーバーを起動して次も実行できます。

```sh
DOCS_URL=http://127.0.0.1:3030/ node extensions/docs/tests/browser.cjs
```

外部にインストールした Playwright を使う場合は `PLAYWRIGHT_MODULE`、Chromium の実行ファイルを指定する場合は `CHROMIUM_BIN` を設定します。
`DOCS_SCREENSHOT` を設定するとデスクトップ画面を PNG に保存します。
