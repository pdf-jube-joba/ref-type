## 大き目の機能
- [ ] 型クラスの実装
- [ ] パッケージの定義
- [ ] LSP とかそこら辺の整備
- [ ] 証明支援系として、 `?` のある `.ref` を受け取ってそれを埋めれるだけ埋めるツールを作る。

## 構文の改良
- `\prec` の方が生で書けて AI には使いやすいらしいが、人間には見づらい。 block 内 `\induction` を入れてそれで書けるようにする。
- `\Power`, `\Subset`, `\Pred`, `\Ty` とかかなり生っぽいので、ここら辺も構文をいい感じにする。左側にある古い構文は保守しなくてよい。
  - `\Power(t)` t: term in Set ... `\Pow t` のように後ろの項をとる
  - `\Subset(x, A, P)` ... `{ x : A \where P }`
  - `\Pred(A, s, t)` ... `\In[A]` で `\fun (s: \Power s) (t: A) => \Pred(A, s, t)`
  - `\Ty(A, s)` ... `\Cast[A]` で `\fun (s: \Power(A)) => \TyLift(A, s)`
  - `\subsetinto(A, X, a, proof)` ... `\into[A](a, X) \by proof`
- `\exact` は逆に要らない？

## 
- front をマジで見てなかったが、 hole の関係で front 側でも conversion をやっているらしくて、かなり無駄。
  - kernel に hole を入れるのはバグになりやすくて微妙なので入れたくない。
  - そもそも conversion をしないと確定しないような hole をなくす、 conversion を行わないで比較する
    - 単に確定しなかった場合は警告を出せばいい。
  - これ、 lean とかもそうらしい。
- front の ExpNode がかなり無駄っぽいので、パーサーの時点で rule 上どの Family 化を確定したい。
