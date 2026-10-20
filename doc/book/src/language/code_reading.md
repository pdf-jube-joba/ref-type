# 2026/10/13
もう全然 rust のコードを読まずに AI に任せていたら、よくわからないことがたくさん起きていた。
ちゃんと読みたい。
読んでて、全部最初から生成させたくなってきた。

## rust 実装
- `CrateEnv` という名前をいまだに使っているらしい。

### kernel
#### `ids.rs`
- SymbolId とは？ ... 確か外から対応する str を引っ張るためのもの
- DefinitionId に `arena: u64` が入っているということは、複数の Arena を同時に持つ（例えば外部？）感じっぽい。
- ModuleParameter ない方がいいみたいな話だったはずだが、 `ParameterId(u64)` が復活している。なんだこれ。
- `NEXT_IDENTITY` は static にしてるが、複数の Arena で共通させるため ?

#### `sort.rs`
まあわかる。

#### `error.rs`
- `diagonostics` crate を使っているらしい。基本は気にしなくていいと思うが、フレームを `Vec` で積むのはどうなんだろう重い気もする。ちゃんと測りたい。

#### `syntax.rs`
- `MetaId` に `session` があって、でも `Arena` も複数ある想定だったと思う。1定義で終了するのが `Session` で、 `Arena` は module 単位とか？
- `Properties` を Storage 内で Vec にしているのは、 SoA っぽい。
- Arena 方式で de Bruijn index だっけ？
  - [ ] TODO interened とか scratch について知る。
- Binding は Context 用っぽい。

#### `sharing.rs`
- なんでここに `ContextId` があるの？ `id.rs` じゃない理由は、どこでも context を使うから？
- ContextInterner が extensions で持っているが、これは実質 Arena ？

#### `calculus.rs`
- shift を外部に公開してる。パッと見はやばいね。
- ベータ簡約してないのでは？普通に subst してる？
