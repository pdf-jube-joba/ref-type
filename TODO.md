## 大き目の機能
- [ ] 証明支援系として、 `?` のある `.ref` を受け取ってそれを埋めれるだけ埋めるツールを作る。
  - auto とかできればいい。

## crate の分割

## 構文
- CType をせっかく polymorphic にしたのに使ってないので使えるようにしたい。
  - そもそも `\CType` がないらしい。まあ使うかと言われたら使わないかもしれないが。
- `((\fun (z: \Cast[\Pow B.Bool^] X) => z) x) \assign _1 = (((\fun (z: \Cast[\Pow B.Bool^] X) => z) y) \assign _2)` これはエラーが出て、 `Module Load Error: parse error: expected RParen, found Equal (544..545)` と `=` のところに出るので、 `\assign _n` はもっとどうにかならないか？

### law の分離
law 周りをもっとどうにかできないか？「record の subset で law が示せるもの」みたいな定義で入れ子になっているのを楽に書きたい。
AI による提案
```
\structure Rec: \Set {
  field1 : SetType1,
  field2 : SetType2,
} \where {
  field3 : PropType3,
  field4 : PropType4,
}
```

型や内部での扱いも入れて考えたい。
- 項と型と lift
  - `Rec` 本体は `{ r: Rec::[Raw] \where Rec::[Law][r] }` という項側にする。型は `\Pow Rec::[Raw]` になる。
  - `Rec::[Set]` で `\Cast[Rec::[Raw]] Rec` ... type へ lift したもの
  - `Rec { field1 := value1, ... } \with { field3 := value3, ...}`: `Rec::[Set]` := `\into[::[Raw]] ({field1 := value1, ...}, {x: {field1: SetType1, ...} \where {field3 : PropType3 } } ) \by { field3 := value3, ...}` になる
- Set 側
  - `Rec::[Raw]`: `\Set` := `{ field1: SetType1, field2: SetType2 }`
  - `Rec::[raw]`: `Rec::[Set] -> Rec::[Raw]` := `(s: Rec::[Set]) => { field1 := s #field1, ...}` ... これは `(s: _) => s` と思える。 
- Prop 側
  - `Rec::[Law][r: Rec::[Raw]]`: `\Prop` := `{ field3 : PropType1, ...}`
  - `Rec::[law]`: `(r: Rec::[Set]) -> Rec::[Law][Rec::[raw] r]` := `(r: Rec::[Set]) => { field3 := r #field3, ...}` ... これは Prop 側の record を取り出す関数で `\bysub(Rec::[Raw], Rec, r)` と思える。

できれば `s: Rec::[Set]` に対しても field projection 記法を使いたい。
`s #field` で `\Set` も `\Prop` も取り出したい。

各 field はそれより前の field 名を参考にしていい。
重複はだめ。

### 再帰関数のマッチ
再帰関数書くために state, ready, acc, prec, precmatch みたいなのを並べているのをどうにかしたい。

#### Program と Set の対応
```
\correspondence name: ProgramType {
  \program := program,
  \set := setterm,
  \coherence := proof,
};
```

`name` で対応に名前を付ける。
`ProgramType`, `program`, `setterm`, `proof` は項が書けるところ。

- `program`: `ProgramType`
- `setterm`: `ProgramType^`
- `proof`: `program^ = setterm`

program 側を reflection した項と set 側の項を `=` で比較して証明させる。
（set 側が原始再帰で program 側が run のときはちょっとめんどいが、多分 `=` は fun ext から示せそうと思っている。）

- `name::[Type]` := `ProgramType`
- `name::[program]`, `name::[set]`, `name::[coherence]` で対応するものを取り出す。
- 

この `{ ... }` の中で補定義とか補定義を書きたいときがあると思うので、 `\definition` や `\inductive` や `\alias` が書かれていてもいい。
その際の名前解決についてはそれより前を参照できる。（例えば `\program` が書かれた以降では `name::[program]` を使っていい。）
ただし、他から参照はできない。

> [!note]
> これは名前解決時に防げばよさそう。わざわざ elaboration とかでチェックはしない。

#### program 周りまとめる
これは単に再帰関数周りの1セットを入れればいい。
（全ての入力で停止するものだけ扱っている。）

```
\machine name {
  \State := State,
  \Output := Output,
  \step := step,
  \terminates := acc,
}
```
`name` に名前を付ける。
`State`, `Output`, `step`, `acc` は項が書けるところ。

- `State`, `Output`: `\VType`
- `step`: `\U(State ~> \F RunStep[State, Output])`
- `terminates`: `(x: State^) -> \Acc[State^, Output^] (step^, x)`

- State, Output, step, terminates については `::[ここに入れる]` で対応する field を取り出せるように。
- `name::[run]`: `State ~> \F Output` で対応する `run` を出せるようにする。
- `name::[runbox]`: `\Box [State ~> \F Output]` := `\box[_] (name::[run])` 既存の `\Box` 検査に従う。

ここでも補定義とその名前解決ができるように。

## ライブラリ

## エラー表示周り

## コードのよくない点

## 未分類
