対処したい問題：
- コード全体を適切に分割するための機構が欲しい
- パラメータによって一般化された議論に対して、そのパラメータに代入ができるとうれしい。

## コード例

```
module test1(
  // module にはパラメータを指定できる。
  A: Set;
  f: A -> A -> A;
) {
  definition double: A -> A := (x: A) => f x x;

  // 子の module も宣言できる。
  module child1(
    a: A;
  ) {
    definition double-pt: A := double a;
  }
}

module testB(
  a: A;
) extends test1 {

  // extend は元の module で宣言された変数に加えての宣言ができる
  definition aa: A := double a;
}

module test2(
  B: Set;
  g: B -> B;
  b: B;
) requires test1 {
  // requires により明示的に依存する module を指定する。

  definition use-snd: B -> B -> B := (x: B) => g;

  // module を instantiate して利用する。
  // ただし、 module 自体は expression としては利用できなくて、
  // module 内の（子 module **以外**の）アイテムに `.` でアクセスしたものが expression として利用できる。
  definition l (b: B): B := test1(A := B, f := use-snd).double b;

  theorem h: test1(A := B, f := use-snd).child1(a := b).double-pt = b := {
    ...
  };

  // instantiate した module へ名前を付けて利用する。
  import test1(A := B, f := use-snd) as test2;

  // 名前を経由して子 module にアクセスする。
  theorem h: test2.child1(a := b).double-pt = b := {
    ...
  };
}
```
