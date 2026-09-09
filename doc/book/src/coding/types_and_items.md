# 型関連 item、structure

型に関連したアイテムと structure の定義

## 名前へのアクセス

名前へのアクセスには `::` を使う。
値に対する `.` projection や method call は用意しない。

```text
List[Nat]::nil
List[Nat]::is_empty xs
Point::x p
Nat<PtBin>::bin a b
```

constructor、field projection、ユーザー定義の関数などは
いずれも `::` でアクセスする。

## 帰納型の型関連 item

```text
\inductive List(A: \Set): \Set :=
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

## structure

named field を持つ通常の record が必要な場合は、`\structure` として明示的に宣言する。

```text
\structure Point(A: \Set): \Set := {
  x : A,
  y : A,
};
```

structure の parameter は通常の名前付き parameter とする。
structure が carrier を持つとは限らないため、特別な carrier binder は用意しない。

```text
\definition origin: Point[Nat] := \record Point[Nat] {
  x := Nat::zero,
  y := Nat::zero,
};
```

各 field について projection を型関連 item として生成する。

```text
Point[A]::x : Point[A] -> A
Point[A]::y : Point[A] -> A

\definition origin_x : Nat := Point[Nat]::x origin;
```

surface syntax としては `\inductive` と `\structure` を完全に分ける。
一方、nominal identity を維持する限り、core や実装内部で structure を
固有の1 constructor を持つ帰納型として表現することは構わない。

result kind には PTS の `\Prop`、`\Set`、`\PropKind`、`\SetKind` を指定できる。

Program の constructor は `Type::item` で参照する。Program の値・計算は
module-level または型関連 item の `\vdefinition`／`\cdefinition` として定義する。
Program value の確認・推論には `\vcheck`、`\vinfer` を使い、computation には
`\ccheck`、`\cinfer`、`\ceval`、`\cnormalize` を使う。汎用の `\definition`、
`\check`、`\infer`、`\eval`、`\normalize` は Set/Prop 専用である。
Program の各カテゴリでも `_`、`?`、`?N` を使える。型注釈や datatype parameter
に現れる metavariable は、その Program judgement 内の制約から解決される。

PTS structure の field は宣言順に依存できる。たとえば次の `value` の型は先行する
`carrier` projection によって定まる。

```text
\structure Packed: \SetKind := {
  carrier: \Set,
  value: carrier,
};
```

## Program の structure と型関連 item

Program の structure は `\VType` の型パラメータと、非依存・非再帰の値 field を持つ。
field に thunk 型 `\U(C)` を使うこともできる。空の structure も宣言できる。

```text
\structure Pair(A: \VType): \VType := {
  first: A,
  second: A,
};

\cdefinition Pair(A: \VType)::swap(p: Pair[A]): \F(Pair[A]) :=
  \bind x: A <- Pair[A]::first p \in
  \bind y: A <- Pair[A]::second p \in
  \return \record Pair[A] { first := y, second := x };

\vdefinition Pair(A: \VType)::swap_thunk:
  \U(Pair[A] ~> \F(Pair[A])) := \thunk (Pair[A]::swap);
```

各 projection は `Pair[A] ~> \F(A)` 型の計算として生成する。
`Pair[A]::first pair` のように適用し、結果の値を使う場合は `\bind` で受け取る。
record literal の field は任意の順序で指定できるが、全 field を一度ずつ指定する。

型関連の `\vdefinition`／`\cdefinition` は Program の inductive にも定義できる。
owner と同じ module 内で、owner の型パラメータをすべて `\VType` として束縛する。
値引数を取る計算は item 名の後に引数を書ける。本体に明示的な `\cfun` を書いてもよい。
constructor、projection、ユーザー定義 item の名前は重複できない。

参照は `Type[A]::item`、import 経由では `Module.Type[A]::item` と書く。
record literal と型関連定義の型引数は全省略または `_` によって推論できる。
文脈から決まらない型引数はエラーになる。
`\vcheck`／`\vinfer` は関連値、`\ccheck`／`\cinfer` は関連計算を扱う。
structure は内部で単一 constructor の Program datatype として表現し、
その constructor を表面構文で公開しない。
