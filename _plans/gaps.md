## record eta 則
record に対する eta がない。 `s = { fiel1 := 2 #field }` が示せない。

## Machine の実行を Box にする定義

Machine を引数に取り、その実行を Box にする共通の定義を書きたい。

```text
\definition runBox(machine: Machine): \Box[machine.State ~> \F(machine.Output)] :=
  \box[_](\force machine.run);
```

現在は引数の State と Output が未確定なため、Box の閉性検査でこの定義を検査できない。
`std.Program.runBox` はマクロとして提供し、呼出側で具体化した Machine の実行を検査している。

## 命題を条件とする集合値の構成

命題の証明を引数に取り、集合値を返す関数を書きたい。
位相空間の正規性から得られる開集合や Urysohn 関数を、正規性の証明と閉集合の証明を引数とする集合値の関数として構成できると、存在証明を何度も展開せずに利用できる。

> [!note]
> この引用欄は人間のメモです。
> 矛盾しなさそうなのは言われているんですが、こういう Prop -> Set はちょっと許しがたい。

## 宣言された型からの証明引数の推論

証明の引数の型を、定義の宣言された型から推論して record の射影や存在証明の消去に使いたい。

```text
\definition andElim(P, Q, R: \Prop): (P -> Q -> R) -> And[P, Q] -> R :=
  \fun (curried: _) (value: _) => curried (value #left) (value #right);
```

現在の elaborator は射影を処理する時点で `value` の型を確定できず、この例には `value: And[P, Q]` が必要になる。
存在証明を `\takefrom` で消去する証明でも、同様に引数の型を明示する必要がある。
部分集合型の引数でも、型を `_` と書いたときに宣言された部分集合型を保持したまま台集合の演算へ渡したい。
方向微分の差商では、`t` を `inv t` に使うと `Real` と推論されるため、`t: Parameter interval` と明示している。

## 定義した型名からの帰納型の操作

`\definition` で名前を付けた帰納型に対して、その名前で constructor の参照と帰納法を書きたい。

```text
\definition Directions: \Set := Lists.List[Coordinate];
Directions::nil
\induction (directions: Directions) \return P directions \with {
  | nil : base
  | cons : step
}
```

多変数微分の微分順序では、現在は `Lists.List[Coordinate]::nil` と `\induction (directions: Lists.List[Coordinate])` を使っている。

## 帰納型の再帰的な述語

帰納型の再帰を使って、命題値の述語を直接定義したい。

```text
\definition Valid(tags: Tags) (a, b: Real): \Prop :=
  \prec[Tags, \fun (tags: Tags) => Real -> Real -> \Prop]
    (\fun (x, a, b: Real) => Logic.And[Le a x, Le x b])
    (\fun (left: Tags) (leftValid: Real -> Real -> \Prop)
      (right: Tags) (rightValid: Real -> Real -> \Prop) (a, b: Real) =>
      Logic.And[leftValid a (midpoint a b), rightValid (midpoint a b) b]) tags a b;
```

現在の recursor はこの motive を `upper sort has no classifier` として拒否する。
積分のタグ付き分割では、`Real -> \Pow Real` に対する再帰で適切なタグの集合を作り、所属命題から `Valid` を定義している。


## モジュール引数に依存する部分集合型の商

区間に依存する部分集合型を、汎用の商モジュールの台集合として渡したい。

```text
\module Lebesgue(interval: Interval) {
  \definition Representation: \Set :=
    \Cast[Nat -> Riemann.Function] ({ sequence: Nat -> Riemann.Function \where Cauchy sequence });
  \import std.Set[].Quotient[A := Representation, Equivalent := Equivalent] \as Q;
  \definition Function: \Set := Q.Carrier;
}
```

現在は区間を具体化して積分の定義を利用すると、具体化済みの `Representation` と、区間引数を受け取る元の定義が convertible と判定されない。
積分ライブラリでは、代表列の同値類を同じモジュール内で構成している。

## 具体化したモジュール内の型と座標空間

体をパラメーターに取るモジュールの中で有限添字型を宣言し、その型を座標空間や基底の添字に使いたい。

```text
\import std.Alg[].Field[] \as Fields;

\module Example(K: \Set, field: Fields.Field[K]) {
  \import linear_algebra.Field[].Space[K := K, field := field] \as Algebra;
  \inductive Unit: \Set := | unit: Unit;
  \import Algebra.Coordinates[I := Unit] \as Coordinates;
  \import Algebra.Finite[V := K, I := Unit, space := Algebra.scalarSpace] \as Finite;
}
```

この形で基底を構成し、モジュールを実数の体に具体化してトレースを検査すると、座標空間の法則の検査で具体化済みの `Example[K := Real, field := realField].Unit` と元の `Example.Unit` が convertible と判定されない。
線形代数の利用例では、添字型を体のパラメーターを持つモジュールの外で宣言している。


## 圏の signature を添字に取る Set の構造

対象の集合と射の集合族を持つ圏を、そのまま関手の構造の添字に使いたい。

```text
\structure Functor[C, D: Category]: \Set {
  object: C.Object -> D.Object,
  map: \forall (u, v: C.Object) -> C.Hom u v -> D.Hom (object u) (object v),
}
\definition identity(C: Category): Functor[C, C] := Functor[C, C] {
  object := \fun (u: C.Object) => u,
  map := \fun (u, v: C.Object) (f: C.Hom u v) => f,
};
```

現在は、Set をフィールドに持つ signature 全体を Set の構造の添字にすると、フィールドのアクセスや sort の検査に失敗する。
圏論ライブラリでは、対象の集合、射の集合族、演算のデータを別々の添字に持つ構造を用意し、`Functor C D` という contextual な定義でまとめている。

## contextual な定義をモジュール引数に渡す

証明内の型を推論させた関手の定義を、モジュール引数に直接渡したい。

```text
\import category.Kan[].Along[A := A, B := A, C := C,
  K := Functors.identity A, F := F] \as Extension;
```

現在は contextual な定義の展開後に残る `_` が `module arguments do not allow inference holes` として拒否される。
圏論ライブラリでは、先に `\definition identity: Functors.Functor A A := Functors.identity A;` を検査し、その名前をモジュール引数に渡している。


## ブロックで導入した contextual な関手の射影

関手を証明ブロックの中で導入し、その対象写像を使いたい。

```text
\definition component(C, D: Cat.Category):
  \forall (F, G, H: Functors.Functor C D) -> \forall (u: C.Object) ->
  D.Hom (F.object u) (H.object u) -> D.Hom (F.object u) (H.object u) := \block {
    \fun (F, G, H: Functors.Functor C D) \then
    \fun (u: C.Object) \then
    \let Arrow: \Set := D.Hom (F.object u) (H.object u) \then
    \fun (f: Arrow) \then
    \return f
  };
```

圏論の垂直合成の証明では、この形の `F.object` が `Module import 'F' was not found` になった。
現在は関手を導入する lambda をブロックの外に置き、ブロック内では中間式と証明を定義している。

## 集合値関手の内部で具体化した自然変換の型

集合値関手のモジュール内で、表現可能関手からの自然変換の型を既存のモジュールから取得したい。

```text
\module Yoneda(P: Diagram, u: C.Object) {
  \import category.SetValued[].On[C := C].Transformations[P := hom u, Q := P] \as Maps;
  \definition evaluate(a: Maps.Transformation): P.Carrier u := a u (C.structure.identity u);
}
```

関数の圏に具体化して `evaluateFromElement` を使うと、具体的な対象集合 `Unit` と、具体化前の `C.Object` が convertible と判定されなかった。
現在の米田の全単射は、同じスコープ内で自然変換の部分集合型を定義している。
