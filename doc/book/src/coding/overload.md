対処したい問題：
- `a "div" b` のような、通常とは異なるパースを要するような演算子について、これをその関数の定義の仕方とは分離した形で記述できてほしい。
- `a * b` のように文脈によって異なる解釈をするものを、適切に（文脈を明示的に与えることもできるようにしたうえで）記述したい。
- 暗黙的な引数を使うところもわかった方がいい。

## アイディア
Record 型を使ってみる。

- record 型とその項について
  - record 型は parametric にする（ polymorphic だと意味が違う？）。型自体に引数があるということ。
  - 項は nominal にするために `RecordName { field := expression }` が項になるようにする。
- record 型と型を結び付ける宣言が instance になる。
- どんな時でも使える notation の部分と、特定の record を使って解釈する部分の両方を定義する。
  - context の解決は明示的に書けたほうがいいが、多くの場合は、型に結びつけられた Record を用いたり、一般の Notation の定義による。
- law は Record に対する性質として定義するが、性質として扱いやすいように形容詞として使えるようにしたい。
  - `X: Associative Unital BinOp` とか

overload 以外にも、そもそも記号の"解釈"を定義することを考える。
現在は `$ ... $` みたいに書いているけど、パースの都合上、左と右がちゃんと分けられた方がいい。
それと、 `$ ... $` の解釈に何を使うかも指定できた方がいい。
なので、 `$( ('token)+ $ expr2 )` のようにしてみる。
`expr2` の部分には、 context を与える。

## コード例
parametric な Record 型の使い方はこんな感じ。
`param` への projection を持つ型を定義してみる。

```
// 型の定義
Record NewA (param: Set) {
  base: Set;
  proj: base -> param;
};

// 項の定義
definition some-a: NewA(Nat) := NewA(Nat) {
  base := Nat;
  proj := id;
};
definition make0: (x: Set) -> NewA(Nat) := (x: Set) => NewA(Nat) {
  base := x;
  proj := (_: x) => 0;
};
definition make1: (x: Set) -> NewA(x) := (x: Set) => NewA(x) {
  base := x;
  proj := (u: x) => u;
}

// field へのアクセス：
definition h1: Nat -> Nat := some-a#proj;
definition h2: some-a#base -> Nat := some-a#proj;

definition proj-def1: (x: Set) -> (a: NewA(x)) -> a#base -> Nat := (x: Nat) => (a: NewA(x)) => a#proj;
definition proj-def2: (x: Set) -> (a: NewA(x)) -> x -> Nat := (x: Nat) => (a: NewA(x)) => a#proj;
```

## overload 部分
`Carrior: Set` を台集合とすることに決め打ちする。
`Structure` という型宣言でそれを使う。

```
// structure 宣言
Structure PointedOver(X: Set) {
  pt: Carrior
  proj: Carrior -> X;
}

// 型の上の Structure の宣言
definition NatId: PointedOver[Nat] := PointedOver(Nat)[Nat] {
  pt := 0;
  proj := (n: Nat) => Nat;
};
definition NatConst0: (X: Set) -> (p: X) -> PoitedOver(Nat)[X] := {
  pt := p;
  proj := (p: X) => 0;
}

// Structure と型を結び付ける
Instance PointedOver(Nat)[Nat] := NatId;
Instance (X: Set) -> PointedOver(X)[A] -> PointedOver(X)[B] -> PointedOver(X)[Prod(A, B)] := ...;
// `A` と `B` は bind が `(A: Set) -> (B: Set) -> ...` と来ていることを暗黙的に仮定する？
```

## 解釈の話
`$($)` を使う。
```
definition div: nat -> nat -> nat := ... ;
// 関数と記号の結び付け
interpretation $(expr1 "div" expr2$) := div expr1 expr2;
// 使い方
definition example1: nat := $(1 "div" 3$); 
```

Structure による解釈の場合：
```
// BinOp を定義してみる
Structure BinOp {
  operator:  Carrior -> Carrior -> Carrior;
}

interpretation $(expr1 * expr2$) for X: BinOp := X#operator expr1 expr2;

definition NatAdd: BinOp[Nat] := BinOp[Nat] { opetator := add };
definition NatMul: BinOp[Nat] := BinOp[Nat] { opetator := mul };

definition tmp1: Nat := $(1 * 2$ NatAdd ); // => 3
definition tmp2: Nat := $(1 * 2$ NatMul ); // => 2
```

instance 宣言により、書かなくてもよくなる。
```
Instance BinOp[Nat] := NatAdd;
definition tmp3: Nat := $(3 * 4$); // => 7
```

## structure の性質について
形容詞として性質をいろいろつけることができるとうれしい。
```
property Associative on X: BinOp {
  assoc: (x, y, z: X) -> $((x * y) * z$) = $(x * (y * z)$);
}

property Commutative on X: BinOp {
  assoc: (x, y, z: X) -> $((x * y) * z$) = $(x * (y * z)$);
}

// theorem 名を書かなくていい。
satisfy Associative- NatAdd :={
  // ここに add の addociative を書く。
};

satisfy Commutative- NatAdd := {
  // ここに add の addociative を書く。
};

definition double: (X: Associative- Commutative- BinOp) -> (x: X) -> X := $(x * x$);

theorem test: double NatMul 1 = 1 := {
  notice (double NatMul 1) is (mul 1 1);
  \refl;
}

satisfy (X: Associative- BinOp) -> (Y: Associative- BinOp) -> (Prof(X, Y): Associative- BinOp) := {
  ...
}
```
