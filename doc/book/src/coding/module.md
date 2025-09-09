# relation 用の module の定義
- 集合 $A$ 上の relation $R$ の性質の定義
- 他からどう使うか
- 商集合の定義など

```
module rel {
  variable A: SET;
  variable R: A -> A -> PROP;

  definition reflexivity: PROP := (x: A) -> R x x;
  definition symmetricity: PROP := (x, y: A) -> R x y -> R y x;
  definition transitivity: PROP := (x, y, z: A) -> R x y -> R y z -> R x z;

  module quotient {
    assumption refl: reflexivity;
    assumption sym: symmetricity;
    assumption trans: transitivity;
  }
}
```
