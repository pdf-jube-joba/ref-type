# 言語処理系の未対応項目

G01〜G10 はこの文書の掲載順である。
各例の枝番・実測・原因は [調査報告と対応表](fix-md/README.md#対象文書の対応) を参照。
分割済みの検討は [G11: Machine の実行を Box にする定義](box-parameters.md#g11) と [G12: 帰納型の再帰的な述語](fix-md/README.md#g12) に続けて採番する。

<a id="g01"></a>

## G01: record eta 則

[再現例・原因: G01](fix-md/README.md#g01)

record に対する eta がない。 `s = { fiel1 := 2 #field }` が示せない。

<a id="g02"></a>

> [!note]
> これは対応しなくていいかな。この gaps には残しておかないと、あとで同じものが記載されうるので残しておきます。

## G02: 命題を条件とする集合値の構成

[再現例・原因: G02](fix-md/README.md#g02)

命題の証明を引数に取り、集合値を返す関数を書きたい。
位相空間の正規性から得られる開集合や Urysohn 関数を、正規性の証明と閉集合の証明を引数とする集合値の関数として構成できると、存在証明を何度も展開せずに利用できる。

<a id="g03"></a>

> [!note]
> 矛盾しなさそうなのは言われているんですが、こういう Prop -> Set はちょっと許しがたい気がするので、保留する。

## G03: 宣言された型からの証明引数の推論

[再現例・原因: G03](fix-md/README.md#g03)

証明の引数の型を、定義の宣言された型から推論して record の射影や存在証明の消去に使いたい。

```text
\definition andElim(P, Q, R: \Prop): (P -> Q -> R) -> And[P, Q] -> R :=
  \fun (curried: _) (value: _) => curried (value #left) (value #right);
```

対応済み。
定義の宣言型を本体の lambda に渡し、射影や `\takefrom` の継続を処理する前に引数の型を確定する。
複数変数を束縛する lambda、ブロック、型注釈付きの局所定義にも期待型を渡す。
部分集合型の引数は、台集合の演算に渡しても宣言された型を保持する。

<a id="g04"></a>

> [!note]
> 対応したい。

## G04: 定義した型名からの帰納型の操作

[再現例・原因: G04](fix-md/README.md#g04)

`\definition` で名前を付けた帰納型に対して、その名前で constructor の参照と帰納法を書きたい。

```text
\definition Directions: \Set := Lists.List[Coordinate];
Directions::nil
\induction (directions: Directions) \return P directions \with {
  | nil : base
  | cons : step
}
```

対応済み。
型の定義を展開して帰納型を特定し、constructor の参照と帰納法を構成する。
多変数微分では `Directions::nil` と `\induction (directions: Directions)` を利用する。
部分集合型は帰納型そのものとして扱わず、元の constructor の引数検査と消去規則を維持する。

<a id="g05"></a>

> [!note]
> 対応したい。

## G05: モジュール引数に依存する部分集合型の商

[再現例・原因: G05](fix-md/README.md#g05)

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

<a id="g06"></a>

## G06: 具体化したモジュール内の型と座標空間

[再現例・原因: G06](fix-md/README.md#g06)

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


<a id="g07"></a>

## G07: 圏の signature を添字に取る Set の構造

[再現例・原因: G07](fix-md/README.md#g07)

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

<a id="g08"></a>

## G08: contextual な定義をモジュール引数に渡す

[再現例・原因: G08](fix-md/README.md#g08)

証明内の型を推論させた関手の定義を、モジュール引数に直接渡したい。

```text
\import category.Kan[].Along[A := A, B := A, C := C,
  K := Functors.identity A, F := F] \as Extension;
```

現在は contextual な定義の展開後に残る `_` が `module arguments do not allow inference holes` として拒否される。
圏論ライブラリでは、先に `\definition identity: Functors.Functor A A := Functors.identity A;` を検査し、その名前をモジュール引数に渡している。


<a id="g09"></a>

## G09: ブロックで導入した contextual な関手の射影

[再現例・原因: G09](fix-md/README.md#g09)

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

<a id="g10"></a>

## G10: 集合値関手の内部で具体化した自然変換の型

[再現例・原因: G10](fix-md/README.md#g10)

集合値関手のモジュール内で、表現可能関手からの自然変換の型を既存のモジュールから取得したい。

```text
\module Yoneda(P: Diagram, u: C.Object) {
  \import category.SetValued[].On[C := C].Transformations[P := hom u, Q := P] \as Maps;
  \definition evaluate(a: Maps.Transformation): P.Carrier u := a u (C.structure.identity u);
}
```

関数の圏に具体化して `evaluateFromElement` を使うと、具体的な対象集合 `Unit` と、具体化前の `C.Object` が convertible と判定されなかった。
現在の米田の全単射は、同じスコープ内で自然変換の部分集合型を定義している。


<a id="g13"></a>

## G13: parameter を持つ帰納型の match

parameter を持つ List の要素を、Set 側でも直接場合分けしたい。

```text
\module Example {
  \inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List;
  \inductive Bool: \Set := | false: Bool | true: Bool;
  \definition List(A: \Set)::isEmpty(xs: List[A]): Bool :=
    \match xs \in List \return Bool \with {
      | nil: Bool::true
      | cons x rest: Bool::false
    };
}
```

2026-10-06 の CLI では構文解析後、`motive telescope length mismatch` で失敗した。
処理系の消去項の構成・検査を調べる必要がある。
