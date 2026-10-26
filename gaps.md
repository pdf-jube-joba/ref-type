# 言語の表現上の不足

## 自然数で再帰する有限係数の型

固定次数の多項式の係数を、次のように先頭と残りの再帰で表したい。
現在は `Data` の検査が `forbidden large elimination` で失敗する。

```ref
\module Test {
  \import std.Data[].Nat[] \as N;
  \structure Layer[A: \Set]: \Set := { head: N.Nat^, tail: A };
  \definition Data: N.Nat^ -> \Set :=
    \induction (k: N.Nat^) \return \Set \with {
      | zero: N.Nat^
      | succ: \fun (k: N.Nat^)(previous: \Set) => Layer[previous]
    };
}
```

現在は最高次係数と固定長ベクトルを持つ型を使う。

```ref
\module Test {
  \import std.Data[].Nat[] \as N;
  \import std.Data[].FinSet[] \as Fin;
  \structure Data[k: N.Nat^]: \Set := {
    top: N.Nat^, lower: Fin.Fin k -> N.Nat^
  };
}
```

## 証明引数を持つ集合値の構成

次のように命題の証明を通常の関数引数にすると、`no product rule for domain Prop and body Set(0)` で失敗する。

```ref
\module Test {
  \import std.Data[].Nat[] \as N;
  \definition make: (N.Nat^::zero = N.Nat^::zero) -> N.Nat^ :=
    \fun (_: N.Nat^::zero = N.Nat^::zero) => N.Nat^::zero;
}
```

現在は証明を宣言の引数に置く。

```ref
\module Test {
  \import std.Data[].Nat[] \as N;
  \definition make[proof: N.Nat^::zero = N.Nat^::zero]: N.Nat^ := N.Nat^::zero;
}
```

## 集合族を引数に持つ structure の組み立て

次のように、集合族を直接 structure の引数にしたい。
現在は `make` の検査が `parameter count mismatch`（`IndType`）で失敗する。

```ref
\module Test {
  \structure Witness[X: \Set, F: X -> \Set]: \Set := {
    point: X, value: F point
  };
  \definition make[X: \Set][F: X -> \Set][x: X][v: F x]: Witness X F :=
    Witness[X, F] { point := x, value := v };
}
```

現在は集合族を module の引数に置き、内部の structure を組み立てる。
この形は CLI の通常検査で終了コード0となる。
B03 の `Representations.Representing` はこの配置を使う。

```ref
\module Test {
  \module Witness(X: \Set, F: X -> \Set) {
    \structure Data: \Set := { point: X, value: F point };
    \definition make[x: X][v: F x]: Data :=
      Data { point := x, value := v };
  }
}
```

## 大きな構造体からの小さな依存データの取り出し

次の自然な表示では `point` の生成で `forbidden large elimination` となる。

```ref
\module Test {
  \structure Data: \Set(1) := { Carrier: \Set, point: Carrier };
}
```

現在は小さな結果型への関数を受け取るフィールドを使い、必要なデータを復元する。
次の形は通常検査で終了0となり、`puppe_sequences.Puppe.Sequence.Arrow` も同じ方法を使う。

```ref
\module Test {
  \structure Data: \Set(1) := {
    Carrier: \Set,
    pointLift: \forall (X: \Set) -> (Carrier -> X) -> X,
  };
  \definition point[d: Data]: d.Carrier :=
    d.pointLift d.Carrier (\fun (x: d.Carrier) => x);
}
```

## ブロック内部での module の別名

局所的に使う module をブロック内で import したいが、次の形は構文解析で `expected block statement or \return` となる。

```ref
\module Test {
  \definition zero: std.Data[].Nat[].Nat^ := \block {
    \import std.Data[].Nat[] \as N \then
    \return N.Nat^::zero
  };
}
```

現在は module のスコープに import を置く。
局所値に依存する import は、その値を引数に取る補助 module に移す。

```ref
\module Test {
  \import std.Data[].Nat[] \as N;
  \definition zero: N.Nat^ := N.Nat^::zero;
}
```
