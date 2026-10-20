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
| `Neighborhoods` / `SimpleConnectivity` | 局所道連結性・半局所単連結性からの近傍基底、単連結性と基本群の自明性 |
| `Bridges` / `Holonomy` | 基点への道の選択、基本群の準同型からの holonomy と自然性 |
| `TwoOpenSets.vanKampen` | 二つの開集合の基本群の融合積としての van Kampen の定理 |
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
## van Kampen の定理

`TwoOpenSets[A, source, U, V].vanKampen` は基点と `Hypotheses` を量化する。
仮定は \(X=U\cup V\)、\(U,V\) の開性、\(U,V,U\cap V\) の道連結性、および基点が共通部分に属することである。
`Connected` はその部分集合内を通る連続な道で道連結性を表す。

結論 `At.Data.IsAmalgamatedProduct` は、包含による標準的な誘導準同型について
\[
\pi_1(X,b)\cong\pi_1(U,b)*_{\pi_1(U\cap V,b)}\pi_1(V,b)
\]
を融合積の普遍性で述べる。
任意の群と、共通部分で一致する二つの準同型に対して、両方を延長する基本群の準同型が存在し一意である。
`algebra.AmalgamatedProduct.Universal` がこの普遍性の API であり、`Other.canonicalIsomorphism` は同じ普遍性を満たす任意の別の群との標準同型を与える。

証明では共通部分で共有する基点への道を選び、二つの準同型から小さい道の holonomy を定める。
重なりでの一致、定数道、細分、正方形の境界の法則を証明して局所降下に渡す。
最後に両方の準同型への制限と、延長の一意性を証明する。

```sh
target/debug/cli libs/topology/fundamental --module fundamental_groups
```
