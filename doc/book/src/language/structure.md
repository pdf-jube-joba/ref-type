# structure

関連する型・値・操作・法則をまとめる。
field の型は宣言順に先行 field に依存できる。

## 宣言の束

```text
\structure Relation {
  A: \Set,
  R: A -> A -> \Prop,
}
\definition Equality(A: \Set): Relation := Relation {
  A := A,
  R := \fun(x, y: A) => x = y,
};
\definition diagonal(r: Relation)(x: r.A): \Prop := r.R x x;
```

sort を指定しない signature は field の依存文脈に展開する。
引数・結果・入れ子の field にも使え、literal の各 member を具体化した型で検査する。
固定した型や値は parameter にできる。

```text
\structure BasedRelation[A: \Set] {
  relation: Relation,
  base: relation.A,
  map: A -> relation.A,
}
```

module parameter に渡す場合も同じ field の代入を使う。
structure を返す定義を引数として受け取る場合は、member ごとの関数型を形成し、通常の product rule と適合を検査する。

## 既定値と Program field

field に本体を付けると literal で省略できる。
上書きした値は、依存する後続 field の型と本体にも代入する。

```text
\structure Duplicate[A: \Set] {
  value: A,
  copy: A := value,
  same: copy = value := \refl(value),
}
\definition duplicate(A: \Set)(a: A): Duplicate[A] := Duplicate[A] { value := a };

\structure ProgramData {
  T: \VType,
  value: T,
  result: \F T := \return value,
}
\definition run(d: ProgramData): \F(d.T) := d.result;
```

Program の値型・値・計算は各カテゴリの規則で検査する。
計算 field の受け渡しには内部で thunk を使い、アクセスは元の計算を返す。
`std.Program.Correspondence` と `Machine` もこの signature を使う。

## sort を持つ record

束全体を等式や帰納法の対象にする場合は sort を指定する。
単一 constructor の帰納型と projection に展開し、field と sort の適合を検査する。

```text
\structure EqualPair[A: \Set]: \Set {
  first: A,
  second: A,
  same: first = second,
}
\definition equalPair(A: \Set)(a: A): EqualPair[A] := EqualPair[A] {
  first := a,
  second := a,
  same := \refl(a),
};
```

命題の証明を law、それ以外を data に分類する。
law があればデータの帰納型・法則の命題・法則を満たす値の refinement を生成する。
値から data と law の両方の field を参照できる。
別々に扱う場合はデータと法則を明示して定義する。

```text
\structure PairData[A: \Set]: \Set { first: A, second: A }
\structure PairLaws[A: \Set, p: PairData[A]]: \Prop { same: p.first = p.second }
\definition EqualPairs[A: \Set]: \Set :=
  \Cast[PairData[A]] ({ p: PairData[A] \where PairLaws[A, p] });
```

Program record の制限と projection は [型関連 item](types_and_items.md#program-の-record) を参照。

## 量化

宣言の束の全称量化は、field を順に束縛する依存 product に展開する。
関連型を持つ束の存在量化は、命題への消去を表す
`\forall(P: \Prop) -> (\forall(r: Relation) -> P) -> P` に展開する。

```text
\definition existsRelation: \Prop := \exists(r: Relation);
\definition witness(A: \Set): existsRelation := \exact(Equality A, Relation);
\definition repack(e: existsRelation): existsRelation := \block {
  \takefrom r: Relation \by e \then
  \return \exact(r, Relation)
};
```

`\exact` は member の適合を検査する。
`\take` / `\takefrom` は証人の field を局所文脈へ展開し、証人に依存しない命題を証明する。
sort が `\Set` の record には通常の集合の存在量化を使う。
