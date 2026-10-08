現状の structure は、名前を束ねるためだけに使われる（場合によっては sort の指定ができる）ものになっている。
それは全然いいとして、構造の記述の方針を考えたい。
ついでに、できるなら構造間の変換も一般に定義したい。


## 構造に Carrier を入れるか parameter にするか
```
\structure A[Carrier: \Set] {
  op: Carrier,
}
```
vs
```
\structure A {
  Carrier: \Set,
  op: Carrier,
}
```

### これらの間の変換
```
\module Playground {
  \structure A[Carrier: \Set] {
    op1: Carrier,
  }

  \structure ASet {
    Carrier: \Set,
    op1: Carrier,
  }

  \definition toSet[Carrier: \Set, data: A[Carrier]]: ASet :=
    ASet { Carrier := Carrier, op1 := data.op1 };
}
```

まあできるが、毎回書かないといけない？めんどくさい。
自動で生成とか definition でできないのか。

AI によると、 sort が明示されていれば（ `\A[Carrier: \Set]: \Set` なら）書けるらしい。
```
\structure Packed[F: \Set -> \Set] {
  Carrier: \Set,
  data: F Carrier,
}

\definition pack(F: \Set -> \Set)(Carrier: \Set)(data: F Carrier): Packed[F] :=
  Packed[F] { Carrier := Carrier, data := data };

\definition unpack(F: \Set -> \Set)(p: Packed[F]): F p.Carrier :=
  p.data;
```

## law の扱い
`\strucuture` は全部入れれるので、 sort さえ気にしなければこれが書ける。
```
\structure A {
  Carrier: A,
  op: Carrier -> Carrier -> Carrier,
  law: \forall (a: Carrier) -> op a a = a,
}
```

ただし、 law は分けたほうがいいという説もある。その方が取り回しがいいし、上のやつは sort ついてないことになってる（はず）。

## 構造の全体の扱い

## "extended" な構造の扱い
```
\structure B[Carrieer: \Set] {

}
```
