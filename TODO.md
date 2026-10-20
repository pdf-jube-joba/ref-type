## 大き目の機能
- [ ] 証明支援系として、 `?` のある `.ref` を受け取ってそれを埋めれるだけ埋めるツールを作る。
  - auto とかできればいい。
- [x] Cargo workspace のように、package 群のキャッシュを共有する（[利用方法](src/USAGE.md#検査とキャッシュ)）。

## 構文
- CType をせっかく polymorphic にしたのに使ってないので使えるようにしたい。
  - そもそも `\CType` がないらしい。まあ使うかと言われたら使わないかもしれないが。
  - module レベルで VType があるので、それで済みそうな？
- `((\fun (z: \Cast[\Pow B.Bool^] X) => z) x) \assign _1 = (((\fun (z: \Cast[\Pow B.Bool^] X) => z) y) \assign _2)` これはエラーが出て、 `Module Load Error: parse error: expected RParen, found Equal (544..545)` と `=` のところに出るので、 `\assign _n` はもっとどうにかならないか？
- あるファイルのパラメータが何なのか、そのファイルじゃなくて親のファイルを見ないといけなくてつらい。
- `\module()` じゃなくて `\module[]` だと思う。

## ライブラリ
- 多項式周りは Program 側で定義していろいろ計算用に使えそう。
- `congr`, `congr2` をどうにかしたい。 `f a b = f c d` が `a = b`, `c = d` から出てくるのを `f a = f b` をもとに recursive に定義できないだろうか。
  - congr! のマクロで f a1 a2 a3 = f b1 b2 b3 を `congr!{A f a1 "=" b1 "in" A1 "by" p1 "and" a2 "=" b2 "in" A2 "\by p2 ...}` みたいに書きたい。
- Equality は、そもそも module parameter でいろいろ渡したほうがよかった気がする。

## その他
- `.md` に古いところが残っているかも: `\machine` に関数する記述とか。
