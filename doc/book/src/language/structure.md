# structure

structure は、関連する型、値、操作、法則をまとめる宣言の束である。
`\structure` で field の名前と型からなる signature を宣言し、literal や `\definition` でその実装を作る。
各 field の型は、先行する field に依存できる。

## 宣言と literal

```text
\structure Relation {
  A: \Set,
  R: A -> A -> \Prop,
}

\definition Equality(A: \Set): Relation := Relation {
  A := A,
  R := \fun(x, y: A) => x = y,
};
```

`Relation` は台集合とその上の二項関係を要求する。
literal の各 field は、先行 field を具体化した型に対して検査される。
実装を作る定義の引数と、signature の field はそれぞれの文脈で束縛される。

structure の field は `.` で参照する。

```text
\definition carrier(r: Relation): \Set := r.A;
\definition diagonal(r: Relation)(x: r.A): \Prop := r.R x x;
```

structure を引数に取る宣言は、field の依存する文脈へ展開して検査する。
適用時には実装の適合を検査し、field の対応を引数や結果へ代入する。
structure を返す定義の結果も、検査された field の対応として保持する。

## parameter と入れ子

signature に固定したい型や値は parameter にする。

```text
\structure RelationOn[A: \Set] {
  R: A -> A -> \Prop,
}

\definition onCarrier(r: Relation): RelationOn[r.A] := RelationOn[r.A] {
  R := r.R,
};
```

変換先の literal に元の field を渡すと、その型や操作を共有する。
parameter として指定した型や値の一致は、通常の conversion によって検査される。

field の型にも structure を指定できる。

```text
\structure BasedRelation {
  relation: Relation,
  base: relation.A,
}

\definition basedEquality(A: \Set)(a: A): BasedRelation := BasedRelation {
  relation := Equality A,
  base := a,
};

\definition atBase(b: BasedRelation)(x: b.relation.A): \Prop :=
  b.relation.R b.base x;
```

子の structure は、親と同じように field の依存文脈へ展開される。
parameter を持つ子の signature は、field の型を書く時点で具体化する。

## 既定の定義と法則

field に本体を付けると、literal で省略した場合の既定の定義になる。
証明も同じ signature の field として保持できる。

```text
\structure Duplicate[A: \Set] {
  value: A,
  copy: A := value,
  same: copy = value := \refl(value),
}

\definition duplicate(A: \Set)(a: A): Duplicate[A] := Duplicate[A] {
  value := a,
};
```

既定の定義は、literal で指定された field を代入した後に検査される。
既定値を上書きした場合、その値に依存する後続 field の型と本体にも代入が適用される。

## module と定義への受け渡し

module の parameter にも structure を指定できる。

```text
\module UseRelation(r: Relation) {
  \definition at(x: r.A): \Prop := r.R x x;
}

\module WithEquality(A: \Set) {
  \import \parent.UseRelation[r := Equality A] \as E;
  \definition at(x: A): \Prop := E.at x;
}
```

module の具体化では、structure の field を module の宣言文脈へ代入する。
structure 自体は module と同様に名前解決と代入で扱われ、field を通じて型や定義を参照する。

structure を返す定義を、別の定義の引数に渡すこともできる。

```text
\definition select(make: \forall(A: \Set) -> Relation)(A: \Set): Relation := make A;
\definition selected(A: \Set): Relation := select Equality A;
```

このような定義の signature は、各 field を返す依存する関数型へ展開される。
各関数型の形成には、基礎体系の product rule を適用する。

## Program の field

Program の値型、値、計算も field に保持できる。

```text
\structure ProgramData {
  T: \VType,
  value: T,
  result: \F(T) := \return value,
}

\definition programData(T: \VType)(value: T): ProgramData := ProgramData {
  T := T,
  value := value,
};

\definition run(d: ProgramData): \F(d.T) := d.result;
```

Program の各 field は、そのカテゴリの型付け規則で検査される。
計算 field を引数として受け渡すときは内部で thunk にし、field へのアクセスで元の計算を返す。
Program の field に対する reflection も、通常の `^` によって参照できる。

## sort を持つ値表現

束全体を通常の値として扱う場合は、structure の sort を指定する。

```text
\structure Pair[A: \Set]: \Set {
  first: A,
  second: A,
}

\definition pair(A: \Set)(a, b: A): Pair[A] := Pair[A] {
  first := a,
  second := b,
};
```

sort を持つ structure は、単一 constructor の帰納型と各 field の projection へ展開される。
field の型と指定した sort の適合は、帰納型の形成規則によって検査される。
生成した型には、通常の等式や帰納法を使える。
projection は `p.first` や `Pair[A]::first p` で参照する。

法則も同じ本体の field に書く。

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

各 field の型を検査し、命題の証明を law、それ以外を data に分類する。
law を含む宣言からは、データの帰納型、法則の命題、法則を満たす値の refinement を生成する。

データと法則のどちらの field も、値から `p.first`、`p.same` のように参照できる。

データと法則を個別に扱う場合は、それぞれを通常の宣言として定義する。

```text
\structure PairData[A: \Set]: \Set {
  first: A,
  second: A,
}
\structure PairLaws[A: \Set, p: PairData[A]]: \Prop {
  same: p.first = p.second,
}
\definition EqualPairs[A: \Set]: \Set :=
  \Cast[PairData[A]] ({ p: PairData[A] \where PairLaws[A, p] });

\definition equalPairs(A: \Set)(a: A): EqualPairs[A] := EqualPairs[A] {
  first := a,
  second := a,
  same := \refl(a),
};
\definition pairData[A: \Set](p: EqualPairs[A]): PairData[A] := p;
\definition pairLaws[A: \Set](p: EqualPairs[A]): PairLaws[A, p] :=
  \bysub(PairData[A], EqualPairs[A], p);
```

## 全称量化と存在量化

宣言の束に対する全称量化は、field を順に束縛する依存する product へ展開する。

```text
\definition diagonalIdentity: \forall(r: Relation) -> \forall(x: r.A) -> r.R x x -> r.R x x :=
  \fun(r: Relation)(x: r.A)(h: r.R x x) => h;
```

展開後の各 product の形成は、通常の product rule によって検査される。

関連型を含む束の存在命題は、命題への消去を表す全称量化へ展開する。
`\exists Relation` の表現は `\forall(P: \Prop) -> (\forall(r: Relation) -> P) -> P` である。

```text
\definition existsRelation: \Prop := \exists(r: Relation);
\definition witness(A: \Set): existsRelation := \exact(Equality A, Relation);
\definition repack(e: existsRelation): existsRelation := \block {
  \takefrom r: Relation \by e \then
  \return \exact(r, Relation)
};
```

`\exact` は field の適合を検査して存在証明を作る。
`\take` と `\takefrom` は、隠した field をローカルな宣言文脈へ展開し、証人に依存しない命題を証明する。
sort が `\Set` の structure の存在量化には、通常の集合に対する存在量化の規則を適用する。
