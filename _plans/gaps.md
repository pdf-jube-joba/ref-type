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
