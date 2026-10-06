# Ref Type エディタ拡張

`extensions/docs` は `libs/` の宣言、署名、ドキュメントコメント、ソースを探索するローカル HTML ブラウザーです。
`cd extensions/docs && cargo run` で起動し、`http://127.0.0.1:3030/` を開きます。
詳細は [docs/README.md](docs/README.md) を参照してください。

`extensions/playground` はブラウザでコードを編集し、診断と評価結果を確認する Web playground です。
`cargo run -p playground` で起動し、表示された URL を開きます。
詳細は [playground/README.md](playground/README.md) を参照してください。

`extensions/lsp` は `.ref` の診断、定義への移動、型のホバー表示、参照検索を提供します。
編集中の内容を検証し、保存前の変更も診断へ反映します。

```sh
cargo build -p ref-lsp
cd extensions/vscode
npm ci
npm run compile
```

リポジトリのルートから `code --extensionDevelopmentPath="$PWD/extensions/vscode"` で拡張を起動します。
リポジトリをワークスペースとして開くと `target/debug/ref-lsp` を使います。
別の配置では `ref-lsp` を PATH に置くか、`ref.server.path` に実行ファイルを指定します。
`ref.toml` を含むパッケージ、または `root.ref` を起点とするモジュール群を検証します。

## VSIX の作成とインストール

```sh
cd extensions/vscode
npm ci
npm run package
code --install-extension ../dist/ref-type-0.1.0-linux-x64.vsix
```

`npm run package` は現在の OS 向けに LSP サーバーをビルドして同梱し、`extensions/dist/` に VSIX を作成します。
生成されるファイル名の OS と CPU の部分は実行環境に応じて変わります。
インストール後は VS Code で `.ref` ファイルを開くと拡張が起動します。
