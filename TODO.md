## 大き目の機能
- [ ] 証明支援系として、 `?` のある `.ref` を受け取ってそれを埋めれるだけ埋めるツールを作る。
  - auto とかできればいい。
- [x] Cargo workspace のように、package 群のキャッシュを共有する（[利用方法](src/USAGE.md#検査とキャッシュ)）。

## 構文
- CType をせっかく polymorphic にしたのに使ってないので使えるようにしたい。
  - そもそも `\CType` がないらしい。まあ使うかと言われたら使わないかもしれないが。
- `((\fun (z: \Cast[\Pow B.Bool^] X) => z) x) \assign _1 = (((\fun (z: \Cast[\Pow B.Bool^] X) => z) y) \assign _2)` これはエラーが出て、 `Module Load Error: parse error: expected RParen, found Equal (544..545)` と `=` のところに出るので、 `\assign _n` はもっとどうにかならないか？
- あるファイルのパラメータが何なのか、そのファイルじゃなくて親のファイルを見ないといけなくてつらい。
- `\module()` じゃなくて `\module[]` だと思う。

## ライブラリ
- 実数の間の変換の定義
