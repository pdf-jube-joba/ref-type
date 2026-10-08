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
```
\module Playground {
\structure A[Carrier: \Set]: \Set {
  op1: Carrier,
}

\definition F: \forall (Carrier: \Set) -> \Set := \fun (Carrier: \Set) => A[Carrier];

}
```
これは `\Set` を明示しているので通る。
```
\module Playground {
\structure A[Carrier: \Set] {
  op1: Carrier,
}

\definition F: \forall (Carrier: \Set) -> \Set := \fun (Carrier: \Set) => A[Carrier];

}
```
これは通らない:
```
Elaboration Error: Failed to access item at path Resolved { span: SourceSpan { start: 144, end: 145 }, module: ModuleId(1), access: Name("A", Some(BindingId(6))), display: "A" }
/playground/root.ref:6:1
  |
 6 | \definition F: \forall (Carrier: \Set) -> \Set := \fun (Carrier: \Set) => A[Carrier];
  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```
エラーの内容がわかりにくい。

## コードのよくない点

## 未分類
