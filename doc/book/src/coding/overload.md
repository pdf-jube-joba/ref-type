対処したい問題：
- `a "div" b` のような、通常とは異なるパースを要するような演算子について、これをその関数の定義の仕方とは分離した形で記述できてほしい。
- `a * b` のように文脈によって異なる解釈をするものを、適切に（文脈を明示的に与えることもできるようにしたうえで）記述したい。
- 暗黙的な引数を使うところもわかった方がいい。

## overload 部分
`Carrior: Set` を台集合とすることに決め打ちする。
`Structure` という型宣言でそれを使う。
普通の Record 型は今は考えない。

```
// structure 宣言（ X 上の基点付き集合の例）
structure PointedOver(X: Set) {
  pt: Carrior
  proj: Carrior -> X;
}

// 型の上の Structure の宣言（自然数を 0 を基点とした自然数上の集合と考える。）
definition NatId: PointedOver[Nat] := PointedOver(Nat)[Nat] {
  pt := 0;
  proj := (n: Nat) => Nat;
};

// 任意の集合とその上の点を受け取って、自然数上の集合にする
definition NatConst0: (X: Set) -> (p: X) -> PoitedOver(Nat)[X] := {
  pt := p;
  proj := (x: X) => 0;
}

// Structure と型を結び付ける
instance PointedOver(Nat)[Nat] := NatId;
instance (X: Set) -> PointedOver(X)[A] -> PointedOver(X)[B] -> PointedOver(X)[Prod(A, B)] := ...;
// `A` と `B` は bind が `(A: Set) -> (B: Set) -> ...` と来ていることを暗黙的に仮定する？
```

## 解釈の話
`$($)` の解釈と構造を結び付ける。
```
// BinOp を定義してみる
structure BinOp {
  operator:  Carrior -> Carrior -> Carrior;
}

// `*` が出てきたら何かしらの BinOp を使う。
interpretation $(expr1 * expr2$) for X: BinOp := X#operator expr1 expr2;

definition NatAdd: BinOp[Nat] := BinOp[Nat] { opetator := add };
definition NatMul: BinOp[Nat] := BinOp[Nat] { opetator := mul };

definition tmp1: Nat := $(1 * 2$ NatAdd ); // => 3
definition tmp2: Nat := $(1 * 2$ NatMul ); // => 2

// instance 宣言により型と構造を結び付けて、書かなくてよいようにする。
instance BinOp[Nat] := NatAdd;
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
satisfy Associative NatAdd :={
  assoc:= { ここに add の addociative を書く。 };
};

satisfy Commutative NatAdd := {
  assoc:= { ここに add の commutative を書く。 };
};

definition double: (X: Associative- Commutative- BinOp) -> (x: X) -> X := $(x * x$);

theorem test: double NatMul 1 = 1 := {
  notice (double NatMul 1) is (mul 1 1);
  \refl;
}

// proj1: Prod(X, Y) -> X とかは定義されている前提

instance (X: BinOp) -> (Y: BinOp) -> BinOp[Prod(X, Y)] := {
  operation := (z1: Prod(X, Y)) => (z2: Prod(X, Y)) => Prod::pair $((proj1 z1) * (proj1 z2)$) $((proj2 z1) * (proj2 z2)$);
};

satisfy (X: Associative- BinOp) -> (Y: Associative- BinOp) -> (Prod(X, Y): Associative- BinOp) := {
  assoc:= {
    
  };
}

```
