# Ref Type エディタ拡張

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
