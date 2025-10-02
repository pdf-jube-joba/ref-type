対処したい問題：
- コード全体を適切に分割するための機構が欲しい
- パラメータによって一般化された議論に対して、そのパラメータに代入ができるとうれしい。

## コード例

```
module test1(
  A: Set;
  f: A -> A -> A;
) {
  definition double: A -> A := (x: A) => f x x;

  module child1(
    a: A;
  ) {
    definition double-pt: A := double a;
  }
}

module testB(
  a: A;
) extends test1 {
  definition aa: A := double a;
}

module test2(
  B: Set;
  f: B -> B;
  b: B;
) requires test1 {

  definition l (b: B): B := test1(A := B, f := true-map).double b;

  theorem h: test1(A := B, f := true-map).child1(a := b).double-pt = b := {
    ...
  };

  import test1(A := B, f := true-map) as test2;

  theorem h: test2.child1(a := b).double-pt = b := {
    ...
  };
}

module test3(
  b0: B;
) extends test2 {
  definition k: B := l b0;
}
```
