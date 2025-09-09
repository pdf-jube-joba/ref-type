# 群と加群の定義
- モノイド・群・環
- 加群の定義
```
trait BinOp {
  var operation: Base -> Base -> Base;
} with parse {
  - (expr1 "*" expr2) := operation expr1 expr2
}

trait Monoid: BinOp {
  var unit: Base;
  law assoc: (x, y, z: Base) -> $(x * y) * z$ = $x * (y * z)$;
  law unitary: (x: Base) -> $1 * x$ = $x /\ $x * 1$ = $x$;
} with parse {
  - "1" := unit
}

property Commutative for Monoid {
  law commutative: (x, y: Base) -> $x * y$ = $y * x$
}

trait Group: Monoid {
  var inverse: Base -> Base;
  law inv: (x: Base) -> $x * x ^{-1}$ = unit /\ $x ^{-1} * x$ = unit
} with parse {
  - (expr "^{-1}") := inverse expr
}

trait Group-Module<G>: Commutative Monoid where G: Group {
  var action: G -> Base -> Base;
  law act: (g: G) -> (x, y: Base) -> $(g . x) * y$ = $g . (x * y)$
} with parse {
  - (expr0 "." expr1) := action expr0 expr1;
}
```
## 書いてみて思ったこと
- 単純に SET の $=$ が law に入っていると使いにくいはずなので、 by definition での同値を制約としてほしい。
  - constraint はそれ
- また、 Commutative Monoid のように（性質 構造）みたいに書くこともあるので、それ用の宣言もあってほしい
  - property はそれ

# モノイドの構成例
"具体的な"型に対しての定義の仕方：
```
fn add: nat -> nat -> nat := { ... }

impl BinOp for Nat {
  var OUT := Nat;
  var operation := add
} with parse {
  - (expr0 "+" expr1) := operation;
}

impl Monoid for Nat {
  var unit := 0;
  law assoc := assoc;
  law unitary := unitary;
}

impl Commutative Monoid for Nat {
  law commutative := comm;
}
```

可換な群はそれ自身を加群とみなす：
```
impl<M> Group-Module<M> for M where M: Group + Commutative Monoid  {
  var action := (m: M) => (x: M) => m * x;
  law act := <M as Monoid>::assoc;
}
```

## 書いてみて思ったこと
- Self と Base やらで、 definitional な equal が要求されるのがいつなのかをちゃんと考えないといけない。

# 積や部分に対して定義する
```


```
