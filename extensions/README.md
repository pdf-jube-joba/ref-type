# エディタとブラウザー

| 拡張 | 起動・機能 |
| --- | --- |
| [docs](docs/README.md) | `cargo run -p ref-docs`。ライブラリの署名・コメント・ソースを読む |
| [playground](playground/README.md) | `cargo run -p playground`。コードを編集して検査・評価する |
| [VS Code](vscode/README.md) / LSP | 診断、定義への移動、ホバー、参照検索。保存前の変更も検査する |

Cargo のコマンドはリポジトリのルートで実行する。

## VS Code の開発

```sh
cargo build -p ref-lsp
npm ci --prefix extensions/vscode
npm run compile --prefix extensions/vscode
code --extensionDevelopmentPath="$PWD/extensions/vscode"
```

リポジトリを開くと `target/debug/ref-lsp` を使う。
別の配置では PATH または `ref.server.path` でサーバーを指定する。
検査は `ref.toml` の package、または `root.ref` を起点にする。

## VSIX

```sh
npm ci --prefix extensions/vscode
npm run package --prefix extensions/vscode
code --install-extension extensions/dist/ref-type-0.1.0-linux-x64.vsix
```

package は現在の OS 向けの LSP を同梱して `extensions/dist/` に VSIX を作る。
生成されたファイル名に合わせてインストールする。
