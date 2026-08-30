## 型関連アイテム
型のコンストラクタや関連アイテムを `::` でアクセスする。

### コンストラクタの場合
これでコンストラクタに対して `List[Nat]::nil` とか `List[Nat]::cons` とかで指定する。
```
inductive List(A: \Type): \Type :=
| nil: List
| cons: A -> List -> List
;
```

### 型関連アイテム
```
impl List(A: \Type) {
  def is_empty: List -> Bool := (l: A) =>
    match l with
    | nil: Bool::true
    | cons(x, xs): Bool::false
  ;
};
```

これで `List[Nat]::is_empty` が使えるようになる。

## 型クラス
構造体と型クラスを分けなくていいと思ったので統合する。
structure は、 `Name { a := a', b := b' }: Name { a : A, b: B }: \Type` の階層にする。
値に対するアクセスは従来通り field access と思って `.` を使うほうがいい？
`natPt: PtSet(Nat): \Type` なので `Group(NatId)` は値に依存する型になるから微妙 ... extend とかで記述する方がいい。

ここら辺は Set でも Program でもできるとうれしい。

```
structure PtSet(A: \Type) := {
  pt: A,
};

definition natPt: PtSet(Nat) := {
  pt := Nat::zero,
};

definition pt: Nat := PtSet(Nat)::pt natPt;
```

構造体に対しても impl が使える。

構造体の拡張は1つだけ指定がよさそう。 `extend Base`

```
structure PtBin extend PtSet(A) := {
  bin: A -> A -> A,
}
```

インスタンスの宣言は、
```
instance NatAdd: PtBin(Nat) := { ... };
```

型クラスの利用の仕方は `\with` を使う
```
definition twice: (A: \Type \with PtBin(A)) -> (a: A) -> A := A<PtBin>::bin a a;
```

コンテキストにも

### 性質の宣言

```
```

ただし、次の law のようなものは

```

structure Group(PointedSet) := {
  bin: # -> # -> #,
  law unit: (a: #) -> #bin #pt a = #bin a #pt,
  law assoc: (a: #) -> (b: #) -> (c: #) -> #bin (#bin a b) c = #bin a (#bin b c),
};

definition nat_add_natural: Nat -> Nat -> Nat := ...;

definition NatAdd: Group(NatId) := {
  bin := nat_add_natural;
  law unit := ...;
  law assoc := ...;
};
```

注意点として、

## 型クラス
型クラスの目的？
- 型ごとに adhoc に実装を選ぶ: `#add 1 2` も `#add (1, 4) (2, 2)` もできてほしい。
- 型関連アイテムをまとめる: `#add` と `#unit` の関連性をまとめる。

構造と型クラスは別にしたい。

```
class Group(Type) {
  unit: #,
  bin: # -> # -> #,
  law unital: ...,
  law assoc: ...,
}

instance Group for Nat {

}
```

型クラス上の関数
```

```
