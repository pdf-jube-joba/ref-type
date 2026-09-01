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
\inductive List(A: \Type): \Type :=
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
\definition List(A: \Type)::is_empty(l: List[A]): Bool :=
  \match l \with
  | nil         : Bool::true
  | cons(x, xs) : Bool::false
;
```

## structure

named field を持つ通常の record が必要な場合は、`\structure` として明示的に宣言する。

```text
\structure Point(A: \Type): \Type := {
  x : A,
  y : A,
};
```

structure の parameter は通常の名前付き parameter とする。
structure が carrier を持つとは限らないため、特別な carrier binder は用意しない。

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

\definition origin_x : Nat := Point::x origin;
```

surface syntax としては `\inductive` と `\structure` を完全に分ける。
一方、nominal identity を維持する限り、core や実装内部で structure を
固有の1 constructor を持つ帰納型として表現することは構わない。

result kind には PTS の `\Prop`、`\Set`、`\PropKind`、`\SetKind` と、
純粋 Program value の universe `\Type` を指定できる。`\VType` は
`\Type` の互換 alias として扱う。同じ structure の parameter と field は
PTS と Program のいずれか一方に揃える。

field は宣言順に依存できる。たとえば次の `value` の型は先行する
`carrier` projection によって定まる。

```text
\structure Packed: \SetKind := {
  carrier: \Set,
  value: carrier,
};
```
