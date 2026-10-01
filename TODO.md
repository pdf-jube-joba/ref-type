## 大き目の機能
- [ ] 証明支援系として、 `?` のある `.ref` を受け取ってそれを埋めれるだけ埋めるツールを作る。
  - auto とかできればいい。

## crate の分割

## 構文
- CType をせっかく polymorphic にしたのに使ってないので使えるようにしたい。
  - そもそも `\CType` がないらしい。まあ使うかと言われたら使わないかもしれないが。
- `((\fun (z: \Cast[\Pow B.Bool^] X) => z) x) \assign _1 = (((\fun (z: \Cast[\Pow B.Bool^] X) => z) y) \assign _2)` これはエラーが出て、 `Module Load Error: parse error: expected RParen, found Equal (544..545)` と `=` のところに出るので、 `\assign _n` はもっとどうにかならないか？

## ライブラリ
- `orElim` を `either!` みたいなマクロを使いたい。
  ```
  either!{
    P "or" Q "either" R
    "lt:" p2r
    "rt:" q2r
  }
  ```
  これで `Logic.Or[P, Q] -> R` の型。
- 改行入れるところと入れないところの統一。

## エラー表示周り

## コードのよくない点

## 未分類
