# 型関連 item と射影

constructor と型関連 item は `::`、field は `.` または `#field` で参照する。
structure の宣言と法則の扱いは [structure](structure.md) を参照。

## 宣言とアクセス

```text
\inductive List[A: \Set]: \Set :=
| nil: List
| cons: A -> List -> List
;
\definition List(A: \Set)::singleton(x: A): List[A] :=
  List[A]::cons x List[A]::nil;
```

型関連定義は owner と同じ module に置き、owner の parameter を先頭で束縛する。
constructor・projection・定義の名前は重複できない。

```text
List[A]::nil
List[A]::singleton x
Import.List[A]::singleton x
```

## Program の record

`\VType` の record は非依存・非再帰の値 field を持ち、thunk 型 `\U C` も使える。

```text
\structure Pair[A: \VType]: \VType {
  first: A,
  second: A,
}
\definition Pair(A: \VType)::swap(p: Pair[A]): \F(Pair[A]) :=
  \program {
    \bind x: A <- Pair[A]::first p \then
    \bind y: A <- Pair[A]::second p \then
    \return Pair[A] { first := y, second := x }
  };
```

projection は `Pair[A] ~> \F A` 型の計算なので、値を使うには `\bind` で受け取る。
Program の型引数は、文脈から決まれば省略または `_` で指定できる。
`Type[A]::item^` は型関連 item の反映を参照する。

## 型から解決する射影

`p #first` と `#first{p}` は p の型から projection を解決する。
Set の法則付き record では data と law の両方を参照でき、Program record では計算を返す。
名前付きの field 参照 `p.first` も使える。
block 内の束縛など、現在の対応範囲は [再現例](../../../../_plans/fix-md/README.md#g09) を参照。
