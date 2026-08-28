structure とか type associated item について
型に対するコンストラクタが `A#B` なので、
これと似たような記法で型関連のアイテムをできるならよさそう。

あと、数学的構造についてもここで書くことにする。

Carrier と書いていたのを `#` にする。
あと、型に関連したアイテムとして何かを書けるようにする。

## 型関連アイテム

```
inductive List(A: Type): Type :=
| nil: List
| cons: A -> List -> List
;
```

これでコンストラクタに対して `List[Nat]#nil` とか `List[Nat]#cons` とかで指定する。

```
impl List(A: Type) {
  def is_empty: List -> Bool := (l: A) =>
    match l with
    | nil: Bool#true
    | cons(x, xs): Bool#false
  ;
};
```

これで `List[Nat]#is_empty` が使えるようになる。

## 構造体
### 構造体の定義と関連アイテムの定義
```
structure PtSet(Type) := {
  pt: #,
};

impl PtSet {
  def is_not_empty: Prop := \nonempty(#, #pt);
}

definition NatId: PtSet(Nat) := {
  pt := Nat#zero,
};

structure Group(PointedSet) := {
  bin: # -> # -> #,
  law unit: (a: #) -> #bin #pt a = #bin a #pt,
  law assoc: (a: #) -> (b: #) -> (c: #) -> #bin (#bin a b) c = #bin a (#bin b c),
};

definition nat_add_natural: Nat -> Nat -> Nat := ...;

definition NatAdd: Group(NatId) := {
  bin := nat_add_natural
  law unit := ...;
  law assoc := ...;
};
```



## 型クラス
