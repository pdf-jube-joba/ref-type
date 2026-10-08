現状の structure は、名前を束ねるためだけに使われる（場合によっては sort の指定ができる）ものになっている。
それは全然いいとして、構造の記述の方針を考えたい。
ついでに、できるなら構造間の変換も一般に定義したい。


## 構造に Carrier を入れるか parameter にするか
```
\structure A[Cr: \Set] {
  op: Cr,
}
```
vs
```
\structure A {
  Cr: \Set,
  op: Cr,
}
```

前者は Cr 上の構造っぽくて、後者は普通の数学的構造っぽい。

### これらの間の変換
```
\module Playground {
  \structure A[Cr: \Set] {
    op: Cr,
  }

  \structure ASet {
    Cr: \Set,
    op: Cr,
  }

  \definition toSet[Cr: \Set, data: A[Cr]]: ASet :=
    ASet { Cr := Cr, op := data.op };
  \definition fromSet[Cr: ASet]: A[Cr.Cr] :=
    A[Cr.Cr] { op :=  Cr.op };
}
```

まあできるが、毎回書かないといけない？めんどくさい。
自動で生成とか definition でできないのか。

AI によると、 sort が明示されていれば（ `\A[Cr: \Set]: \Set` なら）書けるらしい。
```
\structure Packed[F: \Set -> \Set] {
  Cr: \Set,
  data: F Cr,
}

\definition pack(F: \Set -> \Set)(Cr: \Set)(data: F Cr): Packed[F] :=
  Packed[F] { Cr := Cr, data := data };

\definition unpack(F: \Set -> \Set)(p: Packed[F]): F p.Cr :=
  p.data;
```

## law の扱い
`\strucuture` は全部入れれるので、 sort さえ気にしなければこれが書ける。
```
\structure A {
  Cr: \Set,
  op: Cr -> Cr -> Cr,
  law: \forall (a: Cr) -> op a a = a,
}
```
- `A: \Prop` にすると、対応する inductive type を作ろうとするので、射影 `Cr` や `op` に対応する射影がとれない（ `(A: \Prop) -> some` で `some: \Set` をやろうとするので）。

ただし、 law は分けたほうがいいという説もある。その方が取り回しがいいし、上のやつは sort ついてないことになってる。

## 構造の全体の扱い

## 内部に他の集合を持つ場合など
```
\structure fn[Cr: \Set]: \SetKind {
  Y: \Set,
  f: Y -> Cr,
}
```
これは書けなくはない。
ただこうなると対応する Pack は書けない。
```
\structure Packed[F: \Set -> \SetKind] {
  Cr: \Set,
  data: F Cr,
}
```

そもそも `F: \Set -> \SetKind` が書けないから。
```
Elaboration Error: Module parameter must have a type or proposition: upper sort has no classifier
rule: "Sort"
rule: "Product"
```

やっぱ、普通に \(*^s_{i}: *^s_{i+1}\) で階層にした方がよかったかも。
