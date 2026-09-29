## 大き目の機能
- [ ] 証明支援系として、 `?` のある `.ref` を受け取ってそれを埋めれるだけ埋めるツールを作る。
  - auto とかできればいい。

## crate の分割

## 構文
- CType をせっかく polymorphic にしたのに使ってないので使えるようにしたい。
  - そもそも `\CType` がないらしい。まあ使うかと言われたら使わないかもしれないが。
- `((\fun (z: \Cast[\Pow B.Bool^] X) => z) x) \assign _1 = (((\fun (z: \Cast[\Pow B.Bool^] X) => z) y) \assign _2)` これはエラーが出て、 `Module Load Error: parse error: expected RParen, found Equal (544..545)` と `=` のところに出るので、 `\assign _n` はもっとどうにかならないか？
- `\idelim` は `(` ~ `)` がいらなそう。

## ライブラリ

## エラー表示周り

## コードのよくない点

## 未分類
### law の分離
law 周りをもっとどうにかできないか？「record の subset で law が示せるもの」みたいな定義で入れ子になっているのを楽に書きたい。
AI による提案
```
\record SomeRecord: \Set {
  field1 : setType1,
  field2 : setType2,
} \where {
  field1 : propType1,
  field2 : propType2,
}
```
後ろは `\Prop` で確定。
また、 `SetRecord::law` とか `SetRecord::raw` で分割してとれるといいらしい。
単語をつぶしたくないので、 `::[keyword]` みたいにしたい。
- `SomeRecord::[Raw]` := `{ field1: SetType1, field2: SetType2 }`
- `SomeRecord::[raw]` := `(s: SetRecord) => { field1 := s #field1, field2  := #field2}`

### 再帰関数のマッチ
再帰関数書くために state, ready, acc, prec, precmatch みたいなのを並べているのをどうにかしたい。
最低限の共通だけ取りたいので、Program と Set の対応用、 Program 周りのまとめる用

#### Program と Set の対応
```
\correspondence add {
  \program: ProgramType := ...,
  \set: SetType := ...,
  \match := ...,
};
```

示すのは `\force \box program = set` で、一応型を
set 側が原始再帰で program 側が run のときはちょっとめんどいが、多分 `=` は fun ext から示せそうと思っている。

Type は reflection された Set 側にする。

使うときは `add::[program]` とかでよさそう。

#### program 周りまとめる
```
\machine add_program {
  \State := ...,
  \step := ...,
  \terminates := ...,
}
```
