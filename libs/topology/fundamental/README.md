# 基本亜群・基本群

実数の単位区間上の連続な道を、端点固定ホモトピーで割る。
群の演算には道を先に左、次に右の順にたどる規約を使う。

| module | 内容 |
| --- | --- |
| `Paths` / `Between` | 端点を指定した道、定数・反転、端点固定ホモトピーの同値関係と商 |
| `Paths.Concatenation` / `Homotopies` / `Classes` | 半区間の貼り合わせ、ホモトピーとの両立、商上の合成 |
| `Paths.GroupoidLaws` | 再パラメータ化による単位・逆・結合のホモトピー |
| `Groupoid` / `Maps` | 基本亜群、連続写像が誘導する写像と合成・単位・逆の保存 |
| `FundamentalGroup` / `Maps.Along` | `std.Alg.Alg.Group` と `algebra.Hom.GroupMap` としての基本群と誘導準同型 |
| `IntervalPaths` / `Examples` | 区間内の道の凸ホモトピーと区間の基本群の自明性 |
| `UnbasedPaths` / `Squares` | 基点を選ばない道、細分、正方形の辺 |
| `VanKampen.Cover.Descent` | 局所 holonomy の降下、ホモトピー不変性、一意性、基本群への準同型 |

## van Kampen の降下形

`VanKampen[A, source, G, group].Cover[family]` は任意の開被覆を扱う。
`SmallPath` は像が被覆の一つの要素に収まる道である。
`LocalFunctor` は小さい道の値、細分に関する積の法則、定数道の単位、同じ被覆要素に収まる正方形の境界に沿う積の一致を保持する。
値は `SmallPath` 自体に指定するので、重なりの上でも一致する。

開被覆の条件から、`Descent.extend` はこれらの局所データをすべての道に延長する。
`restricts` は小さい道での一致、`unique` は延長の一意性を証明する。
延長は道の連結を積に送り、端点固定ホモトピーで不変である。
`Descent.AtPoint.homomorphism` は基本群から指定した群への準同型を返す。

証明は区間の有限二分木細分、細分間での値の一致、正方形の有限細分と境界の積の貼り合わせから構成する。
二つの開集合の基本群から融合積を構成する API と、その通常の van Kampen の表示は別途必要である。

```sh
target/debug/cli libs/topology/fundamental --module fundamental_groups
```
