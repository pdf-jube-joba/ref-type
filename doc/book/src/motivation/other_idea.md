# 読みやすさのために形式化するうえでのベンチマーク的なもの
## $\sqrt{2}$ の無理性
> もし $\sqrt{2}$ が有理数なら、整数 $a, b$ であって、
> $a^2 = 2 b^2$ かつ $a$ と $b$ は互いに素となる物が存在する。
> $a^2$ は偶数であるから $a$ は偶数である。
> 整数 $a'$ をとって $a = 2 a'$ とすると $2 a'^2 = b^2$ が成り立つ。
> $b^2$ は偶数であるから $b$ も偶数であるので、 $a$ と $b$ が互いに素という仮定に矛盾する。
> よって、 $\sqrt{2}$ は有理数ではない。

こんな感じで書けるといいのか？(seventeen proves of the world の informal を参考にした。)
```
theorem sqrt-irrational: (a, b: int) -> (coprime) -> (sqrt 2 = a / b) -> FALSE := {
  fix (a: int) (b: int) (h: sqrt 2 = a/ b);

  generality h: coprime a b rename (a0 @ a; b0 @ b) := {
    let a0: int := a div (gcd a b);
    let b0: int := b div (gcd a b);
    let h := gcd.coprime
  }

  have h1: 2 * (square b) = square a := reasoning! {
    (sqrt 2 = a / b) & from h
    => square sqrt 2 = square (a / b) & eq.apply-fn square
    => 2 = square (a / b) & eq.rewrite-l (l1 2)
    => 2 = (square a) / (square b) & (l2 a b)
    => 2 * (square b) = (square a) / (square b) * (square b) & eq.apply-fn ((b: real) => a * (square b))
    => 2 * (square b) = (square a) & eq.rewrite-r (l3 a b)
  } with {
    remark l1: (x: real_{> 0}) -> (square sqrt x = x) := { ... }
    remark l2: (a, b: int) -> (square (a / b) = (square a) / (square b)) := { ... }
    remark l3: (a, b: real) -> (a / b * b = a) := { ... }
  }

  lemma l1: (x: int) -> (\exists y, square x = 2 * y) -> (\exists x': int, x = 2 * x') := {
    fix (x: int);
    take y: int | h: square x = 2 * y;
    reasoning! {
      square x = 2 * y & from h
      => (\exists x', x = 2 * x') \/ (\exists y', x = 2 * y') & l1 x x y
    } either! {
      case1: (\exists x', x = 2 * x') {
        case1
      }
      case2: (\exists y', x = 2 * y') {
        case2
      }
    }
  } with {
    remark l1: (x, y, z: int) -> (x * y = 2 * z) -> (\exists x', x = 2 * m) \/ (\exists y', y = 2 * y') := { ... }
  }

  have h2: (\exists a': int, a = 2 * a) := reasoning! {
    2 * (square b) = (square a) & from h1
    => (2 * square b) mod 2 = (square a) mod 2 & eq.apply-fn ((a: int) => a mod 2)
    => 0 = (square a) mod 2 & eq.apply-l l1
    => (square a) mod 2 = 0 & eq.sym
    => \exists a': int, (square a) = 2 * a' & l2 (square a)
    => \exists a': int, a = 2 * a' & l3 a
  } with {
    remark l1: (x: int) -> ((2 * x) mod 2 = 0) := { ... }
    remark l2: (x: int) -> ((x mod 2 = m) -> (\exists m: int, x = 2 m)) := { ... }
    remark l3: (x: int) -> (\exists m: int, square x = 2 m) -> (\exists m: int, x = 2 m) := { ... }
  }

  take a': int, a = 2 * a';

  have h3: (\exists b': int, b = 2 * b') := {

  }

}
```

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
