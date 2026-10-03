## record eta 則
record に対する eta がない。 `s = { fiel1 := 2 #field }` が示せない。

## 命題を条件とする集合値の構成

命題の証明を引数に取り、集合値を返す関数を書きたい。
位相空間の正規性から得られる開集合や Urysohn 関数を、正規性の証明と閉集合の証明を引数とする集合値の関数として構成できると、存在証明を何度も展開せずに利用できる。

> [!note]
> この引用欄は人間のメモです。
> 矛盾しなさそうなのは言われているんですが、こういう Prop -> Set はちょっと許しがたい。

## 命題値の関係を引数や field に持つ集合値の定義

二項関係をデータとして保持する `EquivalenceRelation` を `\structure` で定義し、その法則付きの値から商集合を構成したい。
また、次の関係の集合表示を `\definition` で書きたい。

```text
\definition RelToPair(A: \Set) (R: Relation[A]): RelPair A :=
  { x : Pair.Times^[A, A] \where R (fst A x) (snd A x) };
```

依存する関係を含む文脈付きの `\definition` と、sort を持たない structure の field として記述できる。
`Relation` の型族は `\definition Relation[Carrier: \Set]: \PropKind := Carrier -> Carrier -> \Prop;` と定義する。
宣言自体を通常の関数値に変換する場合は、その product 型の形成が必要になる。

## 関連型を隠した structure の存在量化

```text
\structure Relation { A: \Set, R: A -> A -> \Prop, }
\definition existsRelation: \Prop := \exists(r: Relation);
```

関連型を field ごとに隠した証人を保持したい。
現在の存在量化は Set の証人を要求するため、この signature を証人の型へ変換するには、関連型と関係を含む帰納型の sort と存在量化の規則を整合させる必要がある。
固定した関連型に対する構造は、sort を指定した structure の値表現として存在量化できる。

## 宣言された型からの証明引数の推論

証明の引数の型を、定義の宣言された型から推論して record の射影や存在証明の消去に使いたい。

```text
\definition andElim(P, Q, R: \Prop): (P -> Q -> R) -> And[P, Q] -> R :=
  \fun (curried: _) (value: _) => curried (value #left) (value #right);
```

現在の elaborator は射影を処理する時点で `value` の型を確定できず、この例には `value: And[P, Q]` が必要になる。
存在証明を `\takefrom` で消去する証明でも、同様に引数の型を明示する必要がある。
