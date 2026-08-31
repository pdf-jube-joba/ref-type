> [!warning]
> なんか微妙に思えてきた。
> metavariable で `_` を常に表示するのと何が違うんだ？
> 最初の `#` であいまいな使い方ができるほうがよっぽどよかった。

# 型関連 item、structure、property

型に関連する名前、structure、型クラス、数学的構造の性質をどう記述するかをまとめる。

## 名前へのアクセス

名前へのアクセスには `::` を使う。
値に対する `.` projection や method call は用意しない。

```text
List[Nat]::nil
List[Nat]::is_empty xs
Point::x p
Nat<PtBin>::bin a b
```

constructor、field projection、ユーザー定義の関数、instance から選ばれる field は、
いずれも `::` でアクセスする。

## 帰納型の型関連 item

```text
\inductive List(A : \Type) : \Type :=
| nil  : List
| cons : A -> List -> List
;
```

constructor は帰納型の型関連 item とする。

```text
List[Nat]::nil
List[Nat]::cons Nat::zero List[Nat]::nil
```

帰納型に対する通常の関数も qualified name で定義する。

```text
\definition List(A : \Type)::is_empty(l : List[A]) : Bool :=
  \match l \with
  | nil         : Bool::true
  | cons(x, xs) : Bool::false
;
```

## structure

named field を持つ通常の record が必要な場合は、`\structure` として明示的に宣言する。

```text
\structure Point(A : \Type) := {
  x : A,
  y : A,
};
```

structure の parameter は通常の名前付き parameter とする。
structure が carrier を持つとは限らないため、特別な carrier binder は用意しない。

```text
\definition origin : Point(Nat) := Point {
  x := Nat::zero,
  y := Nat::zero,
};
```

各 field について projection を型関連 item として生成する。

```text
Point(A)::x : Point(A) -> A
Point(A)::y : Point(A) -> A

\definition origin_x : Nat := Point::x origin;
```

projection の structure parameter は引数の型から推論できるため、使用時には省略できる。

surface syntax としては `\inductive` と `\structure` を完全に分ける。
一方、nominal identity を維持する限り、core や実装内部で structure を
固有の1 constructor を持つ帰納型として表現することは構わない。

structure の field には計算データだけを置く。
数学的な law を proof field として structure に格納する方法は採用せず、後述する property を使う。

structure は通常の record として明示的に使うことも、instance search の対象として使うこともできる。

```text
\structure PtSet(A : \Type) := {
  pt : A,
};

\structure PtBin \extend PtSet(A) := {
  bin : A -> A -> A,
};
```

`\extend` で指定できる基底 structure は一つだけとする。
`\extend PtSet(A)` は `PtSet` の parameter telescope から `A : \Type` を導入し、
`PtBin` は `PtSet(A)` の field `pt` を引き継ぐ。
継承した field にも `PtBin(A)::pt` のような projection を生成する。
ただし `PtBin` と `PtSet` は別の nominal type である。

structure の値を `\definition` で定義しただけでは instance search には登録しない。

```text
\definition nat_add : PtBin(Nat) := PtBin {
  pt  := Nat::zero,
  bin := nat_add_natural,
};
```

instance を明示する場合は、対象の型、structure、instance を指定して field を参照する。

```text
Nat<PtBin \using nat_add>::pt
Nat<PtBin \using nat_add>::bin a b
```

`\using` を省略した場合は、local instance context と global instance environment から
一意な instance を探す。候補が存在しない場合と複数存在する場合は error にする。

```text
Nat<PtBin>::bin a b
```

### `\with` binder

型変数と、それに対する structure の instance constraint をまとめて書くために `\with` を使う。

```text
\definition twice:
  (A : \Type \with PtBin(A)) ->
  (a : A) ->
  A
:=
  A<PtBin>::bin a a;
```

`A : \Type \with PtBin(A)` は、`A` と anonymous な `PtBin(A)` instance を context に加える。
同じ structure の instance を複数受け取る場合は名前を付け、`\using` で選択する。

```text
(A : \Type \with (add : PtBin(A)))
A<PtBin \using add>::bin a b
```

## property

数学的構造は、計算データと、それが満たす性質に分ける。
計算データは structure の値として定義し、性質は PTS の predicate として定義する。

structure `PtBin(A)` に対する単位元則は次のように宣言する。

```text
\property Unital(p : PtBin(A)) :=
  (a : A) ->
    PtBin(A)::bin p
      (PtBin(A)::pt p)
      a
    = a
  /\
    PtBin(A)::bin p
      a
      (PtBin(A)::pt p)
    = a
;
```

`PtBin(A)` によって `PtBin` の parameter telescope から `A` を導入する。
`p` は特別な self binder ではなく、任意の `PtBin(A)` の値を受け取る通常の変数である。

### adjective notation

property を満たす構造は、property name に `-` を付けて記述する。

```text
Unital- PtBin(A)
Unital- Associative- PtBin(A)
```

`-` は identifier の一部ではなく、property を base structure に適用する構文である。
この構文は type/constraint の位置でだけ解釈する。

複数の property は nested subset とせず、base structure に対する predicate の積として扱う。
例えば `Unital- Associative- PtBin(A)` は PTS 側で概念的に次の subset に対応する。

```text
Ty(
  RfType(PtBin(A)),
  { p : RfType(PtBin(A))
  | Unital(A, p) /\ Associative(A, p) }
)
```

`\with` binder や instance declaration では、property が要求する structure instance と証明を補う。

```text
(A : \Type \with Unital- Associative- PtBin(A))
```

## `\satisfy`

既に定義された structure value が property を満たすことは、`\satisfy` で宣言する。

```text
\satisfy NatAdd : Unital(Nat) := ...;
\satisfy NatAdd : Associative(Nat) := ...;
```

`\satisfy` は `NatAdd` の Program type を後から変更しない。
structure value とは別に PTS の証明を生成するため、property proof は structure の field や Program の計算には入らない。
instance search は、明示的に検査済みの `\satisfy` declaration を evidence として利用する。

## `\instance`

structure value を instance search に登録するには `\instance` を使う。

```text
\instance nat_add : Unital- Associative- PtBin(Nat) := NatAdd;
```

この declaration は `NatAdd` の型と二つの `\satisfy` declaration を検査し、
structure value と property evidence の組を instance environment に登録する。

instance search は surface term を明示的な structure value と property proof を取る項へ変換する。
kernel は instance environment や property search を知らず、通常の Program typing と PTS proof checking だけを行う。
