# 特異コホモロジーのカップ積

`Cochains[A, source, R, ring]` は可換環 \(R\) に値を取る特異余鎖とその積を扱う。
`Cup[p, q]` は単体の最初の \(p+1\) 頂点と最後の \(q+1\) 頂点への制限を使い、全特異単体上の値を自由加群から線形に延長する。

| module | 構成と証明 |
| --- | --- |
| `Cup.Bilinear` | 両変数での加法・スカラー倍との両立と、零との積。 |
| `Unit` | 定数 \(1\) の閉余鎖、左右の単位則。 |
| `Associativity` | 頂点列を三つに分ける制限の一致から得る結合則。 |
| `Pullback.Cup` / `Pullback.Unit` | 連続写像による引き戻しが積と単位を保つこと。 |
| `Leibniz` | \(\delta(\alpha\smile\beta)=\delta\alpha\smile\beta+(-1)^p\alpha\smile\delta\beta\)。 |
| `Cup.Closed` / `Boundaries` | 閉余鎖同士の積の閉性と、一方が境界で他方が閉じている場合の積が境界になること。 |
| `Cohomology.Cup` | 閉余鎖の商に降ろした双線形な積と、代表元での公式。 |
| `Cohomology.Unit` / `Cohomology.Associativity` | コホモロジー上の左右の単位則と結合則。 |
| `Cohomology.Pullback` | 可換環上で線形なコホモロジーの引き戻しと、積・単位の保存。 |

`Cohomology.Group n` と `moduleSpace n` は `singular_cohomology.Cochains.OverRing.With` のコホモロジーと加群構造である。
`Cohomology.Cup[p, q].onClasses` は、積が閉余鎖の実際のカップ積の類であることを示す。
次数の加法の等式による移送は `Cohomology.DegreeTransport` が扱う。

```sh
target/debug/cli libs/topology/singular/products --module singular_products.Cochains --diagnostics compact
```
