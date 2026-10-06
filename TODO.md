## 大き目の機能
- [ ] 証明支援系として、 `?` のある `.ref` を受け取ってそれを埋めれるだけ埋めるツールを作る。
  - auto とかできればいい。

## crate の分割

## 構文
- CType をせっかく polymorphic にしたのに使ってないので使えるようにしたい。
  - そもそも `\CType` がないらしい。まあ使うかと言われたら使わないかもしれないが。
- `((\fun (z: \Cast[\Pow B.Bool^] X) => z) x) \assign _1 = (((\fun (z: \Cast[\Pow B.Bool^] X) => z) y) \assign _2)` これはエラーが出て、 `Module Load Error: parse error: expected RParen, found Equal (544..545)` と `=` のところに出るので、 `\assign _n` はもっとどうにかならないか？

## ライブラリ
- 実数の間の変換の定義

## エラー表示周り
### definition の型に str -> str は書けない
```
\module Playground {
  \structure A[Carrier: \Set] {
    a: Carrier,
  }

  \structure B[Carrier: \Set] {
    b: Carrier,
  }

  \definition AtoB[Carrier: \Set]: A[Carrier] -> B [Carrier] :=
    \fun (data: A[Carrier]) => B[Carrier] { b := data.a };
}
```
これのエラーがこう。
```
Resolution Error: definition does not satisfy structure result signature
/playground/root.ref:10:3
  |
10 |   \definition AtoB[Carrier: \Set]: A[Carrier] -> B [Carrier] :=
  |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```
そもそも `A[Carrier] -> B[Carrier]` が書けないと思う。
バグか、あるいはエラー表示を親切にしたい。

### product rule として実際に出てきたものを出したい。
```
Elaboration Error: Generated projection b does not typecheck: no product rule for these sorts
```
何の rule が拒否されたのかを見たい。

### program syntax と出る
```
\module Playground {
  \structure A: \SetKind {
    Carrier: \Set,
    a: Carrier,
  }

  \structure ALaw {
    data: A,
    some: A.a = A.a
  }
}
```
これのエラーがこう
```
Elaboration Error: expected Program value-type syntax
/playground/root.ref:9:8
  |
 9 |     s: A.a = A.a,
  |        ^^^
```
`A` が `\structure A` の名前なのでダメで、 `data.a` ならいいはず。
ただ、 `A.a` に対するエラーとしてはよくない。

## コードのよくない点

## 未分類
