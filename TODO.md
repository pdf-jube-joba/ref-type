## 大き目の機能
- [ ] 型クラスの実装
- [ ] パッケージの定義
- [ ] LSP とかそこら辺の整備
- [ ] 証明支援系として、 `?` のある `.ref` を受け取ってそれを埋めれるだけ埋めるツールを作る。

## 構文の改良
- `\prec` の方が生で書けて AI には使いやすいらしいが、人間には見づらい。
  項として `\induction` も追加する。
  `\induction (x: A) \return T \with { | constructor1 => branch1 | constructor2 => branch2 }` のような感じ。
  これを `\prec` に落とし込む。 motive は `\fun (x: A) => T` になり、型は `(x: A) -> T` になる。
  - `T` が `x` に依存するのは大丈夫だが、 branch は無理。
- `\prec` は `\prec[type, motive] branch1 branch2` の方がよさそう。現状だと sort を推測で入れれるはず。
- `\Power`, `\Subset`, `\Pred`, `\Ty` とかかなり生っぽいので、ここら辺も構文をいい感じにする。左側にある古い構文は保守しなくてよい。
  - `\Power(t)` t: term in Set ... `\Pow t` のように後ろの項をとる
  - `\Subset(x, A, P)` ... `{ x : A \where P }`
  - `\Pred(A, s, t)` ... `\In[A]` で `\fun (s: \Power s) (t: A) => \Pred(A, s, t)` と同じに。
  - `\Ty(A, s)` ... `\Cast[A]` で `\fun (s: \Power(A)) => \TyLift(A, s)` と同じに。
  - `\subsetinto(A, X, a, proof)` ... `\into[A](a, X) \by proof` で書く。
- run 系もかなり生っぽい。 state-type と return-type をとるところは `\name[state-type, return-type]` にしたい。これも古い構文は deprecated に。
  - `\name[t1, t2](他の引数)` ... 例: `\accintro[state-type, result-type](step, state, predecessors)`
  - 対象は `\continue`, `\finish`, `\Acc`, `\accintro`, `\accdecent`, `\runStepRec`, `\run`, `\runCase`,
- box でも `\name[program-computation-type]` をとる。これも古い構文は deprecated に。
  - `\Box`, `\box`, `\force`
  - `\Force` じゃなくて `\force` にする。

## 
- front をマジで見てなかったが、 hole の関係で front 側でも conversion をやっているらしくて、かなり無駄。
  - kernel に hole を入れるのはバグになりやすくて微妙なので入れたくない。
  - そもそも conversion をしないと確定しないような hole をなくす、 conversion を行わないで比較する
    - 単に確定しなかった場合は警告を出せばいい。
  - これ、 lean とかもそうらしい。
- front の ExpNode がかなり無駄っぽいので、パーサーの時点で rule 上どの Family 化を確定したい。
