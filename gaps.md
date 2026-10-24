# 言語の表現上の不足

## 集合族を引数に持つ structure の組み立て

次のように、集合族を直接 structure の引数にしたい。
現在は `make` の検査が `parameter count mismatch`（`IndType`）で失敗する。

```ref
\module Test {
  \structure Witness[X: \Set, F: X -> \Set]: \Set := {
    point: X, value: F point
  };
  \definition make[X: \Set][F: X -> \Set][x: X][v: F x]: Witness X F :=
    Witness[X, F] { point := x, value := v };
}
```

現在は集合族を module の引数に置き、内部の structure を組み立てる。
この形は CLI の通常検査で終了コード0となる。
B03 の `Representations.Representing` はこの配置を使う。

```ref
\module Test {
  \module Witness(X: \Set, F: X -> \Set) {
    \structure Data: \Set := { point: X, value: F point };
    \definition make[x: X][v: F x]: Data :=
      Data { point := x, value := v };
  }
}
```
