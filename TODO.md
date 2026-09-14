- [ ] 型クラスの実装
- [ ] パッケージの定義

## 
- block の take はその場で uniqueness を `\by` でとり、即座に入れ子の block 開始して最後に `dependenct` をとる
- reflect した型名は `^s` とかにする（ Program 側で `Bool: \VType` にしたら `Bool^s: \Set` みたいな感じ。）
  - これは普通に `^` だけでもいい。
- `\inductive` は VType と Set が共通なので、 `\definition` も `\vdefinition` にしないでよさそうに思える。
- `\prec` の方が生で書けて AI には使いやすいらしいが、人間には見づらい。 block 内 induction を入れてそれで書けるようにする。
- `Rat.ref` をちゃんとすでに定義された `Int.ref` を使うようにする。

## 改良案
- 代入を環境との組にして高速化できるか
  - すごい lazy だが、結局 convertible を判定するには厳しそう。
- Arena って使われなくなった項が回収されないのでは？
- de Bruijn 使ってるけど、 FVar と BVar を分けて各 BVar はどのラムダで束縛されているかを直接 Id で持っておいた方がいい気がする。
  - よく考えるとコピーされるときに Id を分けてコピーしないといけないので微妙かも。
  - あと、FVar はなくて ModuleId のようにして束縛されるケースしかない。
- convertibility の判定って weakかheadかのnormalization してる？もっと楽な方法がありそう。
- module の定義を全部インスタンス化しない。
- module のインスタンス化を別の module で再利用できるようにする。 export の仕組み？
