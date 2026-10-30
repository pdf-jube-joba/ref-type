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

## 親 module 内の定義への直接参照

次のように子 module から `\parent.identity` を項として使いたい。
現在は `Module instantiation path must contain at least one module` で失敗する。

```ref
\module Test {
  \definition identity[A: \Set][x: A]: A := x;
  \module Child {
    \definition result[A: \Set][x: A]: A := \parent.identity A x;
  }
}
```

現在は親 module を明示的に import してから定義を参照する。

```ref
\module Test {
  \definition identity[A: \Set][x: A]: A := x;
  \module Child {
    \import \root.Test[] \as Parent;
    \definition result[A: \Set][x: A]: A := Parent.identity A x;
  }
}
```

## import 別名を経由する公開参照

module 内の import 別名を、その module の利用側から修飾して参照したい。
現在は `Name 'Internal' was not found in its scope` となる。

```ref
\import std.Data[].Nat[] \as N;
\module Core {
  \definition value: N.Nat^ := N.Nat^::zero;
}
\module Wrapper {
  \import \root.Core[] \as Internal;
}
\import \root.Wrapper[] \as API;
\definition result: N.Nat^ := API.Internal.value;
```

現在は必要な定義を明示的に公開するか、利用側で元の module を import する。

```ref
\import std.Data[].Nat[] \as N;
\module Core {
  \definition value: N.Nat^ := N.Nat^::zero;
}
\module Wrapper {
  \import \root.Core[] \as Internal;
  \definition value: N.Nat^ := Internal.value;
}
\import \root.Wrapper[] \as API;
\definition result: N.Nat^ := API.value;
```


## Fredholm 性の具体的な作用素への特殊化

次の具体例で、零 Hilbert 空間の恒等作用素に汎用定理を適用したい。
`fredholmOfParametrix` の特殊化で、元の `Fredholm(V, space, norm, W, target, targetNorm, f)` が残り、具体的な結論と変換可能にならない。
`Examples.ref` と同じ条件で `target/release/cli libs/analysis/fredholm_operators --module fredholm_operators.Examples --full-check-local` により再現できる。

```ref
\module Test {
  \import complex_hilbert.Examples[] \as Z;
  \import fredholm_operators.Space[V := Z.Point, space := Z.space, norm := Z.norm].Operators[W := Z.Point, target := Z.space, targetNorm := Z.norm] \as O;
  \import O.At[f := Z.identity] \as I;
  \import I.Hilbert[inner := Z.inner, targetInner := Z.inner] \as H;
  \import complex_hilbert.Space[V := Z.Point, space := Z.space].Operators[W := Z.Point, target := Z.space, norm := Z.norm, targetNorm := Z.norm].Compact[] \as K;
  \import functional_analysis.Normed[V := Z.Point, space := complex_hilbert.Space[V := Z.Point, space := Z.space].realSpace] \as N;
  \import std.Logic[].Proposition[] \as Logic;
  \definition p: I.Parametrix Z.identity := Logic.And[_, _]::#
    (K.zeroImage (I.leftDefect Z.identity) (\fun (x: Z.Point) => N.subSelf x))
    (K.zeroImage (I.rightDefect Z.identity) (\fun (x: Z.Point) => N.subSelf x));
  \definition fredholm: H.Fredholm := H.fredholmOfParametrix Z.complete Z.complete Z.identity p;
}
```

現在は、作用素を定理の通常の引数に移す次の適用も試している。
この回避案でも、`Space.Operators.Hilbert.atkinson` の検査で特殊化に関する型エラーを確認した。

```ref
\module Test {
  \import complex_hilbert.Examples[] \as Z;
  \import fredholm_operators.Space[V := Z.Point, space := Z.space, norm := Z.norm].Operators[W := Z.Point, target := Z.space, targetNorm := Z.norm] \as O;
  \import O.At[f := Z.identity] \as I;
  \import I.Hilbert[inner := Z.inner, targetInner := Z.inner] \as H;
  \definition apply: I.Parametrix Z.identity -> H.Fredholm :=
    \fun (p: I.Parametrix Z.identity) => O.Hilbert[inner := Z.inner, targetInner := Z.inner].atkinson Z.identity Z.complete Z.complete Z.identity p;
}
```
