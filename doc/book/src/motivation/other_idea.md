# 読みやすさのために形式化するうえでのベンチマーク的なもの
## sub group の定義と group 演算の書き方
> $G$ を群とする。
> $G$ の部分集合 $H$ が、 $1 \in H$ と $a, b \in H \implies a * b \in H$ を満たすとき
> $H$ は $G$ の部分群であるという。
> またこのとき、 $H$ を $G$ の演算を制限することで群とみなす。

- 台集合と数学的構造を同一視している。
- 演算子がオーバーロードされる。

## 同型の計算とか

## $=$ の両辺が関数のときに、それぞれ定義されるように定義域を狭める。

# アイディア
## とりあえず Trait と new type を使う？
Trait のようなものはほしい。
- dot notation (`a: T: Trait` について `a.method()`)
- associate method (`T: Trait` について `T::method()`)
- notation (`T: Specific-Trait` のときにのみ `a method b` など。)

普通に部分集合に Trait を定義することになると、
型の一意じゃなさと合わさってどの演算を使うかの解決が難しい。
なので、ある程度一意に定まる名前が付けられるようになった方がいい。
また、台は必ず集合と考えて、合成できるようにするのがいい？
それと、演算子と Trait を結び付けられるといい。
（ rust の std::ops のような感じ。）

モノイド：
```
Trait Monoid {
  method unit: Base;
  method mu: Base -> Base -> Base;
  law assoc: mu is associative;
  law unit: (x: Base) -> (mu unit x = x) /\ (mu x unit = x);
} with parse {
  - "1u" := Base
  - (expr0: Base) "*" (expr1: Base) := mu expr0 expr1
}
```
こう分けることもできる：
```
Trait Binary-Operator {
  method mu: Base -> Base -> Base;
}  with parse {
  - "1u" := Base
  - (expr0: Base) "*" (expr1: Base) := mu expr0 expr1
}

Trait Monoid: Binary-Operator {
  method unit: Base;
  law assoc: mu is associative;
  law unit: (x: Base) -> (mu unit x = x) /\ (mu x unit = x);
}
```

実装する側？
```
fn add: Nat -> Nat -> Nat := (n: Nat) => rec((m: Nat) => m, ... );
thm add-assoc: add is associative := ...;

impl Binary-Operator for Nat {
  method mu := add;
}

impl Monoid for Nat {
  method unit := Nat::Zero;
  law assoc := add-assoc
}
```

部分集合についての一般論
```
variable A: Monoid;

def is-close (H: Power A): Prop := (x, y: Ty(H)) -> Pred(H, x * y);

impl Monoid for Ty(H) where
  H: Power A s.t. is-close(H)
{

}
```
