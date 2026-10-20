# リー群の基盤

`Dimension[n].OnManifold[M].LieGroup` は、Hausdorff・第二可算な滑らかな多様体 \(M\) 上の群構造で、積と逆元が滑らかなものとして定義する。
積の共同での滑らかさは、任意の有限次元滑らかな多様体からの滑らかな二つの写像の積が滑らかである、という条件で記述する。

| module | 内容 |
| --- | --- |
| `Smooth.Between` | 関数の滑らかさ、同じ関数を表す滑らかな写像の一意性、定数写像 |
| `Dimension.OnManifold.On` | 単位元の接空間、滑らかな共役写像、随伴線形写像 `Ad` |
| `Dimension.OnManifold.On.OneParameter` | 滑らかな一径数部分群、零での速度、積分データから得る `exp` |
| `Classical.On.Orthogonal` | 双線形形式を保つ可逆線形写像の群 |
| `Classical.On.Orthogonal.Special` | 指定次数の全交代形式を保つ部分群 |
| `Classical.On.Orthogonal.LieAlgebra` | 反対称な線形自己写像の部分リー代数 |
| `Euclidean[n]` | 標準内積、O(n)・SO(n)・\(\mathfrak{so}(n)\)、クリフォード代数と Pin・Spin・複素拡張の具体化 |

`Ad g` は共役写像 \(x\mapsto gxg^{-1}\) の単位元での微分である。
微分の値域となる接空間を、共役写像が単位元を固定する等式で単位元の接空間に移している。

`OneParameter.Integration` は、各接ベクトルをその零での速度に持つ一径数部分群の族である。
`OneParameter.exp integration v` は、その一径数部分群の時刻 \(1\) の値を返す。
任意のリー群に対する `Integration` の存在・一意性と、指数写像の滑らかさの証明は含まれていない。

`Euclidean[n].orthogonalGroup` と `specialOrthogonalGroup` は、線形写像を台に持つ群構造である。
SO(n) は次数 \(n\) の全交代形式を保つ条件を用いる。
`soLieAlgebra` は \(\langle Ax,y\rangle=-\langle x,Ay\rangle\) を満たす自己写像の交換子リー代数である。

O(n)・SO(n) のアトラスと積・逆元の滑らかさ、\(\mathfrak{so}(n)\) と単位元の接空間との同定、Pin・Spin の被覆に沿う多様体構造、有限中心商の多様体構造は構成していない。
したがって、これら六つの具体的な群に対する `LieGroup` の値はまだ公開していない。

```sh
cargo run -p cli -- libs/geometry/lie_groups --module lie_groups
```
