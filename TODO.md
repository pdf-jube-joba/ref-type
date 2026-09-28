## 大き目の機能
- [ ] 証明支援系として、 `?` のある `.ref` を受け取ってそれを埋めれるだけ埋めるツールを作る。
  - auto とかできればいい。

## crate の分割

## 構文
- `\fix (x: A) (y: B);` と書けるようにする。
- CType をせっかく polymorphic にしたのに使ってないので使えるようにしたい。
  - そもそも `\CType` がないらしい。まあ使うかと言われたら使わないかもしれないが。
- `((\fun (z: \Cast[\Pow B.Bool^] X) => z) x) \assign _1 = (((\fun (z: \Cast[\Pow B.Bool^] X) => z) y) \assign _2)` これはエラーが出て、 `Module Load Error: parse error: expected RParen, found Equal (544..545)` と `=` のところに出るので、 `\assign _n` はもっとどうにかならないか？

## ライブラリ

## エラー表示周り

## コードのよくない点
- 関数定義で `\fun` が入れ子でインデントを入れすぎる。 300 行もあったり。
- block をそもそも全然使ってない。あと、 `\enough` も使ってない。
- Logic.And の入れ子も大量なので、 structure を使うようにする。
- ブロック内では `\takefrom x: A \by p;` を使うようにしたい。

## 未分類
- law 周りをもっとどうにかできないか？「record の subset で law が示せるもの」みたいな定義で入れ子になっているのを楽に書きたい。
- 再帰関数書くために state, ready, acc, prec, precmatch みたいなのを並べているのをどうにかしたい。
