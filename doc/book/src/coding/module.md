# relation 用の module の定義
- 集合 $A$ 上の relation $R$ の性質の定義
- 他からどう使うか
- 商集合の定義など

```
module rel (
  var A: SET;
  var R: A -> A -> PROP;
) {
  definition reflexivity: PROP := (x: A) -> R x x;
  definition symmetricity: PROP := (x, y: A) -> R x y -> R y x;
  definition transitivity: PROP := (x, y, z: A) -> R x y -> R y z -> R x z;

  module quotient (
    assum refl: reflexivity;
    assum sym: symmetricity;
    assum trans: transitivity;
  ) {
    definition eq-class (a: A): \Power A := { x: A | R a x };
    definition eq-classes: \Power (\Power A) := { X: \Power A | \exists a, X = eq-class a}

    lemma eq-class-l1: (X, Y: Power A) -> (X = Y) -> (x: A) -> \Pred(A, X, x) -> \Pred(A, Y, x) := {
      fix (X, Y: \Power A), (h: X = Y), (x: A), (hX: \Pred(A, X, x));
      \id-elim X Y ((Z: \Power A) -> \Pred(A, Z, x));
    }
    lemma eq-class-l2: (a1, a2: A) -> eq-class a1 = eq-class a2 -> R a2 a1 := {
      fix (a1, a2: A), (h: eq-class a1 = eq-class a2);
      have h1: (x: A) -> R a1 x -> R a2 x := eq-class-l1 (eq-class a1) (eq-class a2) h;
      h1 a1 (refl a1)
    }

    definition quotient-map: (Y: SET) -> (f: A -> Y) -> ((x1, x2: A) -> R x1 x2 -> f x1 = f x2) -> \Ty(eq-classes) -> Y := {
      fix (Y: Set), (f: A -> Y), (h-a0: (x1, x2: A) -> R x1 x2 -> f x1 = f x2), X: \Ty(eq-classes);
      have h1: \exists a: A | h: X = eq-class a & \subset X eq-classes (\Power A);
      take a: A | h: X = eq-class a;
      f a
    } proof {
      - \exists a: A | h: X = eq-class a := { h1 }
      - (a1: A | X = eq-class a1) -> (a2: A | X = eq-class a2) -> f a1 = f a2 := {
        fix (a1: A | h1: X = eq-class a1), (a2: A | h2: X = eq-class a2);
        have hR: R a2 a1 := eq-class l2 _ _ _;
        eq.sym a2 a1 (h-a0 a2 a1)
      }
    }
  }
}
```

思いのほか本題以外が長くなったが、とりあえずこんな感じで定義しておくとする。
- module in module を許し、 parameter 部分（ module の sig? ）は最初に宣言しておく。

# 使う側？
```
definition nat-modulo (n: Nat): module := rel(A := Nat, R := (x1: Nat) -> (x2: Nat) -> ($x1 "mod" n$ = $x2 "mod" n$));
definition nat-module-quotient (n: Nat): module := (nat-modulo (n: Nat))::quotient(refl := ... sym := ... trans := ...);
```
この書き方は絶対おかしい。
もっといいものがあるはず？
AI の書き方を参考にする。
