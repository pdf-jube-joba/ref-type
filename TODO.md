## 大き目の機能
- [ ] `?` はもう要らんわ。あと、 `_n` も全然使ってなさそう。

## 構文
- CType をせっかく polymorphic にしたのに使ってないので使えるようにしたい。
  - そもそも `\CType` がないらしい。まあ使うかと言われたら使わないかもしれないが。
  - module レベルで VType があるので、それで済みそうな？
- `((\fun (z: \Cast[\Pow B.Bool^] X) => z) x) \assign _1 = (((\fun (z: \Cast[\Pow B.Bool^] X) => z) y) \assign _2)` これはエラーが出て、 `Module Load Error: parse error: expected RParen, found Equal (544..545)` と `=` のところに出るので、 `\assign _n` はもっとどうにかならないか？
- あるファイルのパラメータが何なのか、そのファイルじゃなくて親のファイルを見ないといけなくてつらい。
- `\module()` じゃなくて `\module[]` だと思う。

## ライブラリ
- 多項式周りは Program 側で定義していろいろ計算用に使えそう。

## その他
