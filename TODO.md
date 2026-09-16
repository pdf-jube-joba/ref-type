## 大き目の機能
- [ ] 型クラスの実装
- [ ] パッケージの定義

## 構文の改良
- block の take はその場で uniqueness を `\by` でとり、即座に入れ子の block 開始して最後に `dependenct` をとる
- `\prec` の方が生で書けて AI には使いやすいらしいが、人間には見づらい。 block 内 induction を入れてそれで書けるようにする。

## 
- front をマジで見てなかったが、 hole の関係で front 側でも conversion をやっているらしくて、かなり無駄。
  - kernel に hole を入れるのはバグになりやすくて微妙なので入れたくない。
  - そもそも conversion をしないと確定しないような hole をなくす、 conversion を行わないで比較する
    - 単に確定しなかった場合は警告を出せばいい。
  - これ、 lean とかもそうらしい。
- front の ExpNode がかなり無駄っぽいので、パーサーの時点で rule 上どの Family 化を確定したい。
