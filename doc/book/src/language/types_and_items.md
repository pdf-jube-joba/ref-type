# 型関連 item と structure

型に関連したアイテムと record の定義を扱う。
structure の宣言と、data と law の値表現は [structure](structure.md) を参照。

## 名前へのアクセス

constructor と型関連 item へのアクセスには `::`、値の field には `.` を使う。

```text
List[Nat]::nil
List[Nat]::is_empty xs
p.x
Nat<PtBin>::bin a b
```

生成した projection は型関連 item としても参照できる。

## パラメータ付きの定義

```text
\definition Relation[Carrier: \Set]: \PropKind := Carrier -> Carrier -> \Prop;
\definition Predicate[Carrier: \Set]: _ := Carrier -> \Prop;
```

definition の parameter は宣言を検査する文脈として保持する。
`Relation[A]` は elaboration 中に `A -> A -> \Prop` へ展開され、既存の kernel で検査する。
この展開の型付けは、parameter の文脈に対する代入補題で説明できる。

## 帰納型の型関連 item

```text
\inductive List[A: \Set]: \Set :=
| nil  : List
| cons : A -> List -> List
;
```

constructor は帰納型の型関連 item とする。

```text
List[Nat]::nil
List[Nat]::cons Nat::zero List[Nat]::nil
```

Set/Prop の帰納型に対する通常の関数も qualified name で定義する。

```text
\definition List(A: \Set)::is_empty(l: List[A]): Bool :=
  \match l \with
  | nil         : Bool::true
  | cons(x, xs) : Bool::false
;
```

## sort を持つ structure

named field を持つ通常の record が必要な場合は、`\structure` として明示的に宣言する。

```text
\structure Point[A: \Set]: \Set := {
  x : A,
  y : A,
};
```

record の parameter は通常の名前付き parameter とする。
record が carrier を持つとは限らないため、特別な carrier binder は用意しない。

```text
\definition origin: Point[Nat] := Point[Nat] {
  x := Nat::zero,
  y := Nat::zero,
};
```

各 field について projection を型関連 item として生成する。

```text
Point[A]::x : Point[A] -> A
Point[A]::y : Point[A] -> A

\definition origin_x: Nat := origin.x;
```

constructor を明示する宣言は `\inductive`、field を持つ宣言は `\structure` で扱う。
一方、nominal identity を維持する限り、core や実装内部で record を固有の1 constructor を持つ帰納型として表現することは構わない。

result kind には PTS の `\Prop`、`\Set`、`\PropKind`、`\SetKind` を指定できる。

Program の constructor は `Type::item` で参照する。Program の値・計算は
module-level または型関連 item の `\definition` として定義する。
Program value の確認・推論には `\vcheck`、`\vinfer` を使い、computation には
`\ccheck`、`\cinfer`、`\ceval`、`\cnormalize` を使う。`\definition` は体系間で共通だが、
`\check`、`\infer`、`\eval`、`\normalize` は Set/Prop 専用である。
Program の各カテゴリでも `_`、`_0`、`?` を使える。
型注釈や datatype parameter に現れる推論変数は、その宣言内の制約から解決される。
`?` の診断には value または computation の期待型と文脈を表示する。

PTS record の field は宣言順に依存できる。
たとえば次の `value` の型は先行する `carrier` projection によって定まる。

```text
\structure Packed: \SetKind := {
  carrier: \Set,
  value: carrier,
};
```

## Program の record と型関連 item

Program の record は `\VType` の型パラメータと、非依存・非再帰の値 field を持つ。
field に thunk 型 `\U(C)` を使うこともできる。空の record も宣言できる。

```text
\structure Pair[A: \VType]: \VType := {
  first: A,
  second: A,
};

\definition Pair(A: \VType)::swap(p: Pair[A]): \F(Pair[A]) :=
  \bind x: A <- Pair[A]::first p \in
  \bind y: A <- Pair[A]::second p \in
  \return Pair[A] { first := y, second := x };

\definition Pair(A: \VType)::swap_thunk:
  \U(Pair[A] ~> \F(Pair[A])) := \thunk (Pair[A]::swap);
```

各 projection は `Pair[A] ~> \F(A)` 型の計算として生成する。
`Pair[A]::first pair` のように適用し、結果の値を使う場合は `\bind` で受け取る。
record literal の field は任意の順序で指定できるが、全 field を一度ずつ指定する。

型関連の `\definition` は Program の inductive にも定義できる。
owner と同じ module 内で、owner の型パラメータをすべて `\VType` として束縛する。
値引数を取る計算は item 名の後に引数を書ける。本体に明示的な `\cfun` を書いてもよい。
constructor、projection、ユーザー定義 item の名前は重複できない。

参照は `Type[A]::item`、import 経由では `Module.Type[A]::item` と書く。
record literal と型関連定義の型引数は全省略または `_` によって推論できる。
文脈から決まらない型引数はエラーになる。
`\vcheck`／`\vinfer` は関連値、`\ccheck`／`\cinfer` は関連計算を扱う。

## 型から解決する field projection

```text
\structure Pair[A: \Set, B: \Set]: \Set {
  first: A,
  second: B,
}
```

`p: Pair[A, B]` の field は `p #first` と書ける。
record の型から projection を解決し、Program record の場合は computation を返す。
`\structure` の要素ではデータ record と law record の両方から field を解決する。
