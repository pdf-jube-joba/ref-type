# Ref Type playground

```sh
cargo run -p playground
```

表示された `http://127.0.0.1:…/` をブラウザで開きます。
ポートを固定する場合は `cargo run -p playground -- --port 3000` で起動します。

左側でコードを編集すると自動で検証し、右側に診断と `\infer`・`\check`・`\eval`・`\normalize` の出力を表示します。
実行ボタンまたは Ctrl+Enter（macOS は Command+Enter）でも検証できます。
コードはブラウザの localStorage に保存され、同じ URL を開くと復元されます。
検証対象はメモリ上の `root.ref` です。
サーバーはローカルホストで待ち受け、Ctrl+C で終了します。
