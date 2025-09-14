# $\sqrt{2}$ の無理性について。
`{...}` の部分は省略してる。
int と real の扱いも省略した。
書いてて思ったけど、省略したら意味ないところもあるのに、全部書こうとすると長すぎる。

## $\sqrt{2}$ の無理性をそれっぽく書く。
```
theorem sqrt-irrational: (a, b: int) -> (sqrt 2 = a / b) -> FALSE := {
  fix (a: int) (b: int) (h: sqrt 2 = a / b);

  generality h-gen: gcd a b = 1 [rename] (a0 @ a; b0 @ b; h0 @ h) := {
    let { a0 := a div (gcd a b); b0 := a div (gcd a b); h-gen} = gcd.mk-coprime a b
    have h0: sqrt 2 = a0 / b0 := {
      have ha: a = a0 * (gcd a b) & gcd.gcd-div a
      have hb: b = b0 * (gcd a b) & gcd.gcd-div b
      reasoning! {
        sqrt 2 = a / b & h
        => sqrt 2 = (a0 * (gcd a b)) / b & eq.rewrite-r.fn ((x: int) -> x / b) ha
        => sqrt 2 = (a0 * (gcd a b)) / (b0 * (gcd a b)) & eq.rewrite-r.fn ((x: int) -> (a0 * (gcd a b)) / x) hb
        => sqrt 2 = a0 * b0 & eq.rewrite-r l1 a0 b0 (gcd a b)
      } with {
        remark l1: (x: int) -> (y: int) -> (z: int) -> ((x * z) / (y * z) = x * y)
      }
    }
  }

  have h1: 2 * (b * b) = a * a := reasoning! {
    (sqrt 2 = a / b) & from h
    => (sqrt 2) * (sqrt 2) = (a / b) * (a / b) & eq.apply-fn square
    => 2 = (a / b) * (a / b) & eq.rewrite-l (l1 2)
    => 2 = (a * a) / (b * b) & (l2 a b)
    => 2 * (b * b) = (a * a) / (b * b) * (b * b) & eq.apply-fn ((b: real) => a * (b * b))
    => 2 * (b * b) = (a * a) & eq.rewrite-r (l3 a b)
  } with {
    remark l1: (x: real_{> 0}) -> ((sqrt x) * (sqrt x) = x) := { ... }
    remark l2: (a, b: int) -> ((a / b) * (a / b) = (a * a) / (b * b)) := { ... }
    remark l3: (a, b: real) -> (a / b * b = a) := { ... }
  }

  lemma c1: (x: int) -> (\exists y: int, x * x = 2 * y) -> (\exists x': int, x = 2 * x') := {
    fix (x: int);
    take y: int | h: square x = 2 * y;
    reasoning! {
      x * x = 2 * y & h
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
    remark l1: (x, y, z: int) -> (x * y = 2 * z) -> (\exists x': int, x = 2 * m) \/ (\exists y': int, y = 2 * y') := { ... }
  }

  have h2: (\exists a': int, a = 2 * a) := reasoning! {
    2 * (b * b) = a * a & h1
    => a * a = 2 * (b * b) & eq.sym
    => (\exists x': int, a = 2 * x') & c1 a (#exact (b * b))
  }

  take a': int | p1: a = 2 * a' & h2;

  have h3: (\exists b': int, b = 2 * b') := reasoning! {
    2 * (b * b) = a * a & h1
    => 2 * (b * b) = (2 * a') * (2 * a') & l1 a (2 * a') p1
    => 2 * (b * b) = 2 * a' * 2 * a' & Nat.mul.assoc
    => b * b = a' * 2 * a' & l2
    => b * b = 2 * a' * a' & Nat.mul.comm
    => (\exists x': int, b = 2 * x') & c1 b (#exact (a' * a'))
  } with {
    remark l1: (x: int) -> (y: int) -> (x = y) -> (x * x = y * y) := { ... }
    remark l2: (m: int_{> 0}) -> (x: int) -> (y: int) -> (m * x = m * y) -> x * y := { ... }
  }

  take b': int | p2: b = 2 * b' & h3;

  have h4: gcd a b > 1 := reasoning! {
    lemma l1: (a: int) -> (\exists x: int, a = 2 * x) -> (a mod 2 = 0) := { ... }
    have h1: a mod 2 = 0 := l1 a p1;
    have h2: b mod 2 = 0 := l1 a p2;
    gcd-cd a b h1 h2
  } with {
    remark gcd-cd: (a: int) -> (b: int) -> (a mod 2 = 0) -> (b mod 2 = 0) -> gcd a b > 1 := { ... }
  }

  FALSE := reasoning! {
    gcd a b > 1 & h4
    => 1 > 1 & eq.rewrite h-gen
    => FALSE & leq-self-neg
  } with {
    remark leq-self-neg: (n: int) -> (n > n) -> FALSE := { ... }
  }
}
```
## 書いてみて思ったこと
- take や exists の扱いがすごい難しそう。
  - take, exists については `|` を使って明示的に `h: P x` を導入しつつ、最後に prop なら受け入れる？
- rust に染まっているのかもしれないが、 マクロっぽいところは `!` を最後につけたりするのがいい？
  - それぞれのマクロはトークンの列を受け取ってそれを変形する
- 最終的にブロックは ゴール `P` の証明項を返すべきで、そこまでが文の列になっているといい？
- そもそも、部分集合がある時点で、証明項だけ与えても停止しないことがあるはずだが、その例になっていないから想像ができない。
- あと、"数式を書いていい部分"をマークするのもいいかも。
  - `$` で挟んだ部分ではパースをいい感じにする。
- それぞれの module で hammer を定義できるぐらい、マクロを強くするのもいいのかもしれない
  - 外部の証明探索ツールは、証明を自動生成するほうがいい。
