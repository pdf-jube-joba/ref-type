## 大き目の機能
- [ ] 証明支援系として、 `?` のある `.ref` を受け取ってそれを埋めれるだけ埋めるツールを作る。
  - auto とかできればいい。
- [ ] kernel にメタ変数を入れたほうがいいかも。
  - kernel にメタ変数を入れると kernel の信頼性が下がるが、さすがにあった方がいい気もする。
    - agda とかは type checker の中でやってるらしい。
    - conversion が2か所にあるのは負担が大きい。
  - メタ変数が最終的に一意に定まらなかったら警告を出すとか？つまり、 unify が完全にされること前提で組む
    - どれだけ下手な制約の解き方でも、最終的に受理されるものが安全ならいいはず。
    - unifiable と convertible をちゃんと考える。
  - メタ変数の生存期間をちゃんと考えないとやばいし、できる限り共有しない方がいいはずだが、それをやると速度が落ちる。

## crate の分割
- elaboration にも型推論のために kernel みたいな infer をやっているところがあるらしい。それも、 raw の中で。
- raw は内部的なものだったはずだが、実際には表示用の文字列などで外に出ているらしい。
- Annotated という項を入れるよりも、 Arena ID への map にした方がよかったのでは？
  - これは自分が提案したので設計のミス。

## 構文
- CType をせっかく polymorphic にしたのに使ってないので使えるようにしたい。
  - そもそも `\CType` がないらしい。まあ使うかと言われたら使わないかもしれないが。
- マクロとメタ変数がうまくいかないらしい。 `macro!{_ A}` は失敗すると。成功するようにしたい。
- `((\fun (z: \Cast[\Pow B.Bool^] X) => z) x) \assign _1 = (((\fun (z: \Cast[\Pow B.Bool^] X) => z) y) \assign _2)` これはエラーが出て、 `Module Load Error: parse error: expected RParen, found Equal (544..545)` と `=` のところに出るので、 `\assign _n` はもっとどうにかならないか？

## ライブラリ

## エラー表示周り
- 名前が見つからなかったらちょうどその名前のところだけに赤線が出てほしい
- `Elaboration Error: Expected inductive type for field projection` も宣言全体に出るので直したい。

## コードのよくない点
- 関数定義で `\fun` が入れ子でインデントを入れすぎる。 300 行もあったり。
- block をそもそも全然使ってない。あと、 `\enough` も使ってない。
- Logic.And の入れ子も大量なので、 structure を使うようにする。
- ブロック内では `\takefrom x: A \by p;` を使うようにしたい。

## 未分類
- law 周りをもっとどうにかできないか？「record の subset で law が示せるもの」みたいな定義で入れ子になっているのを楽に書きたい。
- 再帰関数書くために state, ready, acc, prec, precmatch みたいなのを並べているのをどうにかしたい。
