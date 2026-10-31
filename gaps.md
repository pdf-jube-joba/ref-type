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


## 局所的な存在量化の添字を持つ構造体の構成

有限階数の因子分解の証明で、存在量化から取り出した添字 `n` を使い、その場で `Factor[g]` を構成したい。
次の 44 行の単独例は、PR #59 を含む処理系でも `--no-cache` で `DefinitionLocalContextIsOutsideReferenceScope` を返して worker が panic する。
`lowering/captures.rs` の `definition_expression_with_parameters` が定義の周囲の局所文脈を参照位置へ下げる段階で失敗し、`kernel_bridge/terms.rs` の弱頭正規化がそのエラーを受け取る。

型導出は、`factor.equation x : out(into x)=f x` と `equal x : f x=g x` の推移性で新しい `equation` を作り、同じ `n` で存在導入するものである。
存在消去の結論は命題 `Finite g` であり、命題から集合への除去は使わない。

こう書きたい版:

```ref
\module Space(V: \Set) {
  \import std.Logic[].Proposition[] \as Logic;
  \import std.Logic[].Equality[] \as E;
  \use E.trans;
  \import std.Data[].Nat[] \as N;
  \import std.Data[].FinSet[] \as Fin;
  \definition identity: V -> V := \fun (x: V) => x;
  \module Through(n: N.Nat^) {
    \structure Factor[f: V -> V]: \Set := {
      into: V -> (Fin.Fin n -> V),
      out: (Fin.Fin n -> V) -> V,
      equation: \forall (x: V) -> out (into x) = f x,
    };
  }
  \definition Finite[f: V -> V]: \Prop := \exists ( n: N.Nat^ \where \exists \root.Space[V := V].Through[n := n].Factor f );
  \module Transport(f, g: V -> V, equal: \forall (x: V) -> f x = g x) {
    \definition finite: Finite f -> Finite g := \block {
      \fun (finite: Finite f) \then
      \takefrom n: \Cast[N.Nat^] ({ n: N.Nat^ \where \exists \root.Space[V := V].Through[n := n].Factor f }) \by finite \then
      \takefrom factor: \parent.Through[n := n].Factor f \by \bysub(N.Nat^, { n: N.Nat^ \where \exists \root.Space[V := V].Through[n := n].Factor f }, n) \then
      \return Logic.existsIntro[N.Nat^, { n: N.Nat^ \where \exists \root.Space[V := V].Through[n := n].Factor g }] n
        (\exact(\parent.Through[n := n].Factor[g] {
          into := factor.into, out := factor.out,
          equation := \fun (x: V) => trans!{V} _ _ _ (factor.equation x) (equal x)
        }, \parent.Through[n := n].Factor g))
    };
  }
}
\module Test {
  \import std.Data[].Nat[] \as N;
  \import std.Data[].FinSet[] \as Fin;
  \import std.Logic[].Proposition[] \as Logic;
  \inductive Point: \Set := | origin: Point;
  \import \root.Space[V := Point] \as S;
  \definition one: N.Nat^ := N.Nat^::succ N.Nat^::zero;
  \definition factor: S.Through[n := one].Factor S.identity := S.Through[n := one].Factor[S.identity] {
    into := \fun (x: Point)(i: Fin.Fin one) => x,
    out := \fun (a: Fin.Fin one -> Point) => a (Fin.zero N.Nat^::zero),
    equation := \fun (x: Point) => \refl(x)
  };
  \definition finite: S.Finite S.identity := Logic.existsIntro[N.Nat^, { n: N.Nat^ \where \exists \root.Space[V := Point].Through[n := n].Factor S.identity }] one
    (\exact(factor, S.Through[n := one].Factor S.identity));
  \definition transported: S.Finite S.identity := S.Transport[f := S.identity, g := S.identity, equal := \fun (x: Point) => \refl(x)].finite finite;
}
```

現在は構造体の構成を `Transport.At(n, factor).result` へ分けると、同じ仮定・結論で検査できる。
こちらは `--no-cache` で成功する 47 行の単独例である。

```ref
\module Space(V: \Set) {
  \import std.Logic[].Proposition[] \as Logic;
  \import std.Logic[].Equality[] \as E;
  \use E.trans;
  \import std.Data[].Nat[] \as N;
  \import std.Data[].FinSet[] \as Fin;
  \definition identity: V -> V := \fun (x: V) => x;
  \module Through(n: N.Nat^) {
    \structure Factor[f: V -> V]: \Set := {
      into: V -> (Fin.Fin n -> V),
      out: (Fin.Fin n -> V) -> V,
      equation: \forall (x: V) -> out (into x) = f x,
    };
  }
  \definition Finite[f: V -> V]: \Prop := \exists ( n: N.Nat^ \where \exists \root.Space[V := V].Through[n := n].Factor f );
  \module Transport(f, g: V -> V, equal: \forall (x: V) -> f x = g x) {
    \module At(n: N.Nat^, factor: \root.Space[V := V].Through[n := n].Factor f) {
      \definition result: \root.Space[V := V].Through[n := n].Factor g := \root.Space[V := V].Through[n := n].Factor[g] {
        into := factor.into, out := factor.out,
        equation := \fun (x: V) => trans!{V} _ _ _ (factor.equation x) (equal x)
      };
    }
    \definition finite: Finite f -> Finite g := \block {
      \fun (finite: Finite f) \then
      \takefrom n: \Cast[N.Nat^] ({ n: N.Nat^ \where \exists \root.Space[V := V].Through[n := n].Factor f }) \by finite \then
      \takefrom factor: \parent.Through[n := n].Factor f \by \bysub(N.Nat^, { n: N.Nat^ \where \exists \root.Space[V := V].Through[n := n].Factor f }, n) \then
      \return Logic.existsIntro[N.Nat^, { n: N.Nat^ \where \exists \root.Space[V := V].Through[n := n].Factor g }] n
        (\exact(At[n := n, factor := factor].result, \parent.Through[n := n].Factor g))
    };
  }
}
\module Test {
  \import std.Data[].Nat[] \as N;
  \import std.Data[].FinSet[] \as Fin;
  \import std.Logic[].Proposition[] \as Logic;
  \inductive Point: \Set := | origin: Point;
  \import \root.Space[V := Point] \as S;
  \definition one: N.Nat^ := N.Nat^::succ N.Nat^::zero;
  \definition factor: S.Through[n := one].Factor S.identity := S.Through[n := one].Factor[S.identity] {
    into := \fun (x: Point)(i: Fin.Fin one) => x,
    out := \fun (a: Fin.Fin one -> Point) => a (Fin.zero N.Nat^::zero),
    equation := \fun (x: Point) => \refl(x)
  };
  \definition finite: S.Finite S.identity := Logic.existsIntro[N.Nat^, { n: N.Nat^ \where \exists \root.Space[V := Point].Through[n := n].Factor S.identity }] one
    (\exact(factor, S.Through[n := one].Factor S.identity));
  \definition transported: S.Finite S.identity := S.Transport[f := S.identity, g := S.identity, equal := \fun (x: Point) => \refl(x)].finite finite;
}
```

A11 の具体的な Atkinson 定理の適用は、余核の証明を作用素から独立した `CompactQuotient` 補題に分けて解消した。
上の単独例は checkpoint を再開せずに再現するため、#59 の checkpoint 再開時の名前空間修正だけでは解消しない。
両者の内部原因が共通かは確認していない。

## module を特殊化した関数の暗黙の eta 展開

宣言引数に依存する module の関数を、そのまま高階関数へ渡したい。
次の例は `--no-cache` でも `inferred: Set, expected: Nat^` で失敗し、生成された lambda では module 引数 `c` が新しい引数 `t` と同じ束縛位置を参照する。

```ref
\module With(c: std.Data[].Nat[].Nat^) {
  \import std.Data[].Nat[] \as N;
  \definition value[t: N.Nat^]: N.Nat^ := c;
}
\module Test {
  \import std.Data[].Nat[] \as N;
  \definition higher[f: N.Nat^ -> N.Nat^]: N.Nat^ := f N.Nat^::zero;
  \definition desired[c: N.Nat^]: N.Nat^ := higher (\parent.With[c := c].value);
}
```

現在は lambda を明示すると同じ計算を記述でき、次の例は `--no-cache` で成功する。

```ref
\module With(c: std.Data[].Nat[].Nat^) {
  \import std.Data[].Nat[] \as N;
  \definition value[t: N.Nat^]: N.Nat^ := c;
}
\module Test {
  \import std.Data[].Nat[] \as N;
  \definition higher[f: N.Nat^ -> N.Nat^]: N.Nat^ := f N.Nat^::zero;
  \definition working[c: N.Nat^]: N.Nat^ := higher (\fun (t: N.Nat^) => \parent.With[c := c].value t);
}
```

`smooth_partitions.Exponential.Flat.Polynomial.LimitRules.At` では係数を固定した補助 module に処理を分けている。
