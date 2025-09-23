対処したい問題：
- コード全体を適切に分割するための機構が欲しい
- 一般化された議論のパラメータに対して代入ができるとうれしい。

## アイディア
- 名前は `module` でも `theory` でもいいけれど、 `theory` にした。
- Coq だと variable や parameter や axiom が文中に書けるけど、これは読みづらくなるのでやめる。
  そういうパラメータ的なものは `theory` の引数として最初に集中させておく。
- ほかに使う theory も同様に、最初に集中させておく。
- 内部から使う場合は代入を全部して import したものからアクセスする。
- `A extend B` と書いたら、 `A` での宣言が使える。

## コード例

```
theory rel(
  var A: Set;
  var R: A -> A -> Prop;
) {
  definition refl: Prop := (x: A) -> R x x;
  definition sym: Prop := (x, y: A) -> R x y -> R y x;
  definition trans: Prop := (x, y, z: A) -> R x y -> R y z -> R x z;

  definition any: Prop := (x, y: A) -> R x y;

  theorem any-refl: any -> refl := {
    fix h: any, x: a;
    h x x   
  }
}

theory eq-rel(
  var p_refl: refl;
  var p_sym: sym;
  var p_trans: trans;
) extends rel {

  definition eq-cls1: (x: A) -> Power A := (x: A) => { y: A | R x y };
  definition eq-cls2: (x: A) -> Power A := (x: A) => { y: A | R y x };

  theorem eq-cls-coinside: (x: A) -> (eq-cls1 x = eq-cls2) := {
    fix x: A;
    // これ集合の extensionality が必要だわ
    have h: (y: A) -> Pred(A, eq-cls1 x, y) -> Pred(A, eq-cls1 x, y) := {
      fix y: A, p: Pred(A, eq-cls1 x, y);
      notice (Pred(A, eq-cls1 x, y)) is (R x y);
      notice (Pred(A, eq-cls2 x, y)) is (R y x);
      p_sym x y p;
    }

  }
}

theory dec-rel(
  var A: Set;
  var Rdec: A -> A -> Bool
) requires rel {

  definition b-to-p: (x: A) -> (y: A) -> Prop := (Rdec x y) = Bool()::True();
  
  definition Rdec-refl: Prop := (x: A) -> (Rdec x x) = Bool()::True();

  import rel(A := A, R := b-to-q) as rel-q;

  theorem refl-tp: Rdec-refl -> rel-q.refl := {
    fix p: Rdec-refl, x: A;
    p x;
  }
}
```