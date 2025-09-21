# 全体で考慮する点・・
- haskell の type class みたいに、辞書渡し（ dictionary passing ）で定義する？
  - record 型を持つ言語への変換と考えてしまうらしい。直感にあっている。
- 型は交差しうることを考えると、 term のレベルから実装が一意に定まってほしいので、交差しうる型に対しては、実装が同じになっていることを課すべき
  - 「ある部分集合では効率的に計算できるアルゴリズムがある」状況を考えると、この"同じ"は functional extensionality にする？
  - `B1, B2: A` とかの状況で、それぞれ `impl T for ?` が `A, \Ty(B1), \Ty(B2)` それぞれにあるなら、そこにある var は equal up to fun extを課す。
    - axiom に fun ext を入れて、 prop のレベルで `=` にすればいいか。
- trait の目的が overload なら、型が強いので implicit な代入さえ許せば $*$ は record 型を引数にとるようにすればいい。
  - この場合、 $1 * 1$ の意味は `*` が `Record { A: Set, o: A -> A -> A } -> A -> A` と考えたときに、
    `1: Nat` から `Nat` に定義された record を探索する必要がある。
    なので、 `Nat` に2つ以上の BinOp の実装があるなら、 正しく反映されない？

思ったのが、 **そもそも** レコード型を中心に考えた方がいいかも。
- record 自体は parametric にする（ polymorphic だと意味が違う？型に引数を与える。）
  - record は nominal にするために `RecordName { field := expression }` が項になるようにする。
- record 型と型を結び付ける宣言が instance になる。
- どんな時でも使える notation の部分と、特定の record を使って解釈する部分の両方を定義する。
  - context の解決は明示的に書けたほうがいいが、多くの場合は、型に結びつけられた Record を用いたり、一般の Notation の定義による。
- law は Record に対する性質として定義する。

## コードはこんな感じ
- 普通の Record 型の使い方：
  - record 定義： `parame` への projection を持つ型を定義してみる。
    ```
    Record NewA (param: Set) {
      base: Set;
      map: base -> param;
    };
    ```
  - Record 型の項：
    ```
    definition some-a: NewA(Nat) := NewA(Nat) {
      base := Nat;
      map := id;
    };
    definition make0: (x: Set) -> NewA(Nat) := (x: Set) => NewA(Nat) {
      base := x;
      map := (_: x) => 0;
    };
    definition make1: (x: Set) -> NewA(x) := (x: Set) => NewA(x) {
      base := x;
      map := (u: x) => u;
    }
    ```
  - field へのアクセス：
    ```
    definition h1: Nat -> Nat := some-a#map;
    definition h2: some-a#base -> Nat := some-a#map;

    definition proj-def1: (x: Set) -> (a: NewA(x)) -> a#base -> Nat := (x: Nat) => (a: NewA(x)) => a#map;
    definition proj-def2: (x: Set) -> (a: NewA(x)) -> x -> Nat := (x: Nat) => (a: NewA(x)) => a#map;
    ```
- overload 解決のための type class 的なもの
  - record を structure にする： `Carrior: Set` を台集合とすることに決め打ちする。
    ```
    Structure PointedOver(X: Set) {
      var pt: Carrior
      var proj: Carrior -> X;
    }
    ```
  - Structure 自体に名前を付ける： `[]` で渡した Set を Carrior と考える。
    ```
    definition NatId: PointedOver[Nat] := PointedOver(Nat)[Nat] {
      pt := 0;
      proj := (n: Nat) => Nat;
    };
    definition NatConst0: (X: Set) -> (p: X) -> PoitedOver(Nat)[X] := {
      pt := p;
      proj := (p: X) => 0;
    }
    ```
  - Structure と型を結び付ける
    ```
    Instance PointedOver(Nat)[Nat] := NatId;
    ```
