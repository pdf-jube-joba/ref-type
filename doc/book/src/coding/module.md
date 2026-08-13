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
  // 以降では、 `A` や `f` は自由変数ではなく、 module parameter への言及になる。
  
  definition double: A -> A := (x: A) => f x x;
  definition triple: A -> A := (x: A) => f x (double x); // この double は同じ階層にいて、これより前に宣言された definition を指していることがわかる。

  // 子の module も宣言できる。
  module child(
    a: A;
  ) {
    // 子の module での宣言
    // A は親の Module の parameter の言及, a は自身の parameter への言及になる。
    definition pt: A := a;

    // 親の module での定義にも言及できる
    definition db: A := parent.double a;
  }
}

module test2()
  requires test1 // 明示的に依存を書いているだけで、あまり動作に支障はない
  // 強いて言えば、将来的に order を指定するとき？
{

  // module の定義へのアクセスの書き方。
  // module への引数を完全に渡してから、その要素にアクセスする。
  definition nat-double: Nat -> Nat := test1(A := Nat, f := mul).double;

  // **これは大きな間違い。**
  // module はどんな手段でもそのままでは式にはなるべきではない。
  definition nat-inst-wrong1: WRONG := test1;
  // instance 化される前の module にもアクセスしてはいけない。
  definition nat-inst-wrong2: WRONG := test1.double;
  // **これも大きな間違い。**
  // 理由は、 module は (instance 化されていても) 式としては扱ってはいけないから。型が違う。
  definition nat-inst-wrong3: WRONG := test1(A := Nat, f := mul);
  // instance 化されてている module の存在する定義にアクセスして初めて valid かどうかの俎上に立つ。

  // 毎回 instance 化の引数を書く代わりの手段の提供としての import
  import test1(A := Nat, f := mul) as hello;

  // 当然、これもだめ
  definition nat-inst-wrong4 := hello;

  // こういう感じでアクセスすることはできる。
  definition nat-double2: Nat -> Nat := hello.double;

  // さらに child module にアクセスすることもできる
  definition nat-db0: Nat := test1(A := Nat, f := mul).child(a := 0).db;

  // **これらは大きな間違い**
  // そのパスに含まれる全ての module は instance 化されていないといけないから。
  definition nat-db0-wrong1: WRONG := test1.child.db;
  definition nat-db0-wrong1: WRONG := test1(A := Nat, f := mul).child.db;
  definition nat-db0-wrong1: WRONG := test1.child(a := 0).db;
  // 型チェック前の意味解析で、だめだとわかる。
  
  // import は常に instance 化されているので、アクセスして大丈夫
  definition nat-db1: Nat := hello.child(a := 0).db;

  // さらに instance 化する
  import hello.child(a := 0) as childNat;
  definition nat-db2: Nat := childNat.db;

  // 定義について改めて
  definition a: Nat := 0;
  definition b: Nat := a; // ここの `a` は module アクセスとして、自分を "identical に" instance 化したものとして考える。

  module foo(
    B: Set;
  ) {
    definition f: Nat := 0;
  }

  module bar() {
    // parent はキーワードになっていて、parent.? もまた "identical" な instance 化された module へのアクセスと考える。
    definition c: Nat := parent.a;
    module bar2() {
      definition cinner: Nat := parent.parent.a;
    }
    // この場合、"親の系列にいない" module へのアクセスは instance 化が必要になる。
    definition d: Nat := parent.foo(B := Nat).f;
  }

  // 可能な path の考察：
  // parent.parent. ... . instance.instance
  // name.instance.instance
}

// 絶対パス表示
module a(A := Set){
  definition x: Nat := 0;

  module b(B := Set){
    definition x: Nat := 0;　// 1.
    definition abs-path-access1: Nat := root.a(A := A).x
    // => same as `parent.x`
    definition abs-path-access2: Nat := root.a(A := A).b(B := B).x;
    // => same as `x` (meaning `x` in 1.)
  }
}

module test3() {
  // "global" な module と名前がかぶることはいい（こっちが優先される。）
  module test1() {
    definition a: Nat := 0;
  }

  definition l: Nat := test1.a;
}

module testB(
  a: A;
) extends test1 {

  // extend は元の module で宣言された変数に加えての宣言ができる
  definition aa: A := double a;
}
```

## 実装について
surface 側で定義しているけれど、 kernel 側では context にしてしまう。
```
mod A(
  P1: Set,
) {
  mod B(
    P2: Set,
  ) {
    mod B2(
      P22: Set,
    ) {
      definition t: P2 -> P22 -> Nat := (_: P2) => (_: P22) => Nat;
    }
  }

  mod C(
    P3: Set,
  ) {
    definition X: P3 -> P3 -> Nat := $root.A(P1 := P1).B(P2 := P3).B2(P22 := P3).t;
    definition Y: P3 -> P3 -> Nat := $parent.B(P2 := P3).B2(P22 := P3).t;

    import $parent.B(P2 := P3) as CB;
    definition Z: P3 -> P3 -> Nat := CB.B2(P22 := P3).t;
  }
}

```
こういう状況で `mod C` の検査をしているときにどうするか...
`mod C` の検査時に、 elaborator には次が入っている？
- `[["A", [(Var("P1")], Set)], ["C", [(Var("P3"), Set)]]]`

このとき、
- root の場合には、素直に代入をしていけばいい。
- parent の場合には、 root から同じ変数への代入を下と考えればいい。
- name の場合には事前に代入したものから再びたどっていく

いずれにせよ、 ModPath の解決後を持っておけばいい？
- `$root.A(P1 := P1).B(P2 := P3).B2(P22 := P3)` も `$parent.B(P2 := P3).B2(P22 := P3)` も、
  `"B2"` で指定される module に対して、 `P1 := P1, P2 := P3, P22 := P3` をしてからその item を得る。

全然実装がわからなかったので、 しばらく full-path でのみとする。
なんかもう全然わからない。
```
mod A(P: Set) {
  inductive U: Set := U1: A.
}

mod B() {
  // 1. は accept, 2. は reject
  definition x: $root.A(P := Nat).U := $root.A(P := Nat).U::U1;
  definition x: $root.A(P := Nat).U := $root.A(P := Nat2).U::U1; 
}

mod B2() {
  import B() as BB;

  // これはどうする？
  definition x: $root.A(P := Nat).U := BB.x;
}
```

理想的には、 access path を覚えておく ... それが一致したら同じとみなす。

nest をやめる。
