# 全体で考慮する点
- 型の記法と trait の記法が混じっていてめんどくさい。 extend にした方がいいかも。
- haskell の type class みたいに、辞書渡し（ dictionary passing ）で定義する？
  - record 型を持つ言語への変換と考えてしまうらしい。直感にあっている。
- 型は交差しうることを考えると、 term のレベルから実装が一意に定まってほしいので、交差しうる型に対しては、実装が同じになっていることを課すべき
  - 「ある部分集合では効率的に計算できるアルゴリズムがある」状況を考えると、この"同じ"は functional extensionality にする？
  - `B1, B2: A` とかの状況で、それぞれ `impl T for ?` が `A, \Ty(B1), \Ty(B2)` それぞれにあるなら、そこにある var は equal up to fun extを課す。
    - axiom に fun ext を入れて、 prop のレベルで `=` にすればいいか。

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
- また、 Commutative Monoid のように（性質 構造）みたいに書くこともあるので、それ用の宣言もあってほしい。
  - property はそれ
- もうちょっと考える点：
  - trait ごとの method 名はかぶってもいい。
  - `trait A: B` で、すでにある trait の継承に対応する？
  - `trait A: B1 + B2` は？

# モノイドの構成例
"具体的な"型に対しての定義の仕方：
```
fn add: nat -> nat -> nat := { ... }

impl BinOp for Nat {
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
- trait と notation が対応しているほうがいいと思う。 Nat の add を `+` で書いて、それ以外の monoid を `*` で書くのはどうしてか考えないといけない。
  - 「comm なら `+` で、"そうじゃないなら" `*`」はいやだ。
    1. comm なら `+` と書いてもよい？ ... 一番ましか？
    2. Ring に対して `*` と `+` を与える。 ... Ring から Monoid にするのができなくなる。

# 積に対して定義する
```
inductive Product (A: Set) (B: Set): Set :=
  | pair: (a: A) -> (b: B) -> Product A B
  ;

impl BinOp for Product(A, B) where A: BinOp, B: Binop {
  var operation := (m1: Product(A, B)) => (m2: Product(A, B)) =>
    match m1 with
    | pair(a1, b1) =>
      match m2 with
      | pair(a2, b2) => pair($a1 * a2$, $b1 * b2$)
      end
    end;
}

impl Monoid for Product(A, B) where A: Monoid, B: Monoid {
  var unit := pair($1$, $1$);
  law assoc := {...}
  law unitary := {...}
}
```

## 書いてみて思ったこと
これは普通に定義できるように思えるが、
- `trait A: B` に対して `impl B for T where T2: B` と `impl A for T where T2: A` に課される一致を検査しなくていいのか？
  - `impl A for T where T2: A` と書いた時点で、 `T` には `B` の実装がついているはず。
    これがどう実装されているか（ `T2: B` からきているのか）は知らなくてもいい？
    - こうすると、 law で要求する proposition の型に `B` の実装の詳細が現れていないといけない。
      だから、 prover は当然、どこから `B` の実装を持ってくるかを決める必要がある。
    - このことを考えると、 `B` の実装は `impl B for T where T2: B` から来ているとしてしまった方が不都合がない。

# 部分集合に対して定義する
```
def is-close (A: BinOp) -> (H: \Power A) -> PROP := (x, y: \Ty(H)) -> \Pred(H, $x * y$);

impl Binop for \Ty(H) where
  - A: Binop
  - law is-close-sub: is-close A H
{
  var operation := (x, y: \Ty(H)) => $x * y$;
} with proof {
  - proof1: (x, y: \Ty(H)) -> \Pred(H, $x * y$) := {
    is-close-sub A H
  }
}
```

なんかすんなりと定義できてしまった...

# Trait を全部集めてくる？
```
Inductive Monoid-iso-maps (A: Monoid) (B: Monoid): SET(0) := record {
  - f: A -> B
  - g: B -> A
  - id-A: (x: A) -> g f x = x
  - id-B: (x: B) -> f g x = x
}

def Monoid-iso (A: Monoid) (B: Monoid): PROP :=
  // \exists f: A -> B, \exists g: B -> A, ((x: A) -> g f x = x) /\ ((x: B) -> f g x = x) のようにも定義できる。
  \exists Monoid-iso-maps(A, B);s

def Monoid-all: \Power Set := \{ T: Monoid \};
def Monoid-equal-class: SET(1) := rel.equiv.class Monoid-all Monoid-iso;
```

書けそうということはわかったが、これがどれぐらい使えるのかがわからない。
## 書いてて思ったこと
- 
