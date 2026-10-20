# リー群の基盤

`Dimension[n].OnManifold[M].LieGroup` は、Hausdorff・第二可算な滑らかな多様体 \(M\) 上の群構造で、積と逆元が滑らかなものとして定義する。
積の共同での滑らかさは、任意の有限次元滑らかな多様体からの滑らかな二つの写像の積が滑らかである、という条件で記述する。

| module | 内容 |
| --- | --- |
| `Smooth.Between` | 関数の滑らかさ、同じ関数を表す滑らかな写像の一意性、定数写像 |
| `Dimension.OnManifold.On` | 単位元の接空間、滑らかな共役写像、随伴線形写像 `Ad` |
| `Dimension.OnManifold.On.LocalProduct` | 単位元付近の積の滑らかな座標表示と、その微分から得る局所ベクトル場 |
| `Dimension.OnManifold.On.OneParameter` | 滑らかな一径数部分群、零での速度、積分データから得る `exp` |
| `Classical.On.Orthogonal` | 双線形形式を保つ可逆線形写像の群 |
| `Classical.On.Orthogonal.Special` | 指定次数の全交代形式を保つ部分群 |
| `Classical.On.Orthogonal.LieAlgebra` | 反対称な線形自己写像の部分リー代数 |
| `Euclidean[n]` | 標準内積、O(n)・SO(n)・\(\mathfrak{so}(n)\)、クリフォード代数と Pin・Spin・複素拡張の具体化 |
| `LocalHom` | 実数上の局所準同型、その一意な二進分割による大域延長 |

`Ad g` は共役写像 \(x\mapsto gxg^{-1}\) の単位元での微分である。
微分の値域となる接空間を、共役写像が単位元を固定する等式で単位元の接空間に移している。

`LocalProduct.VectorField` は、指定した接ベクトルと積のヤコビアンから座標ベクトル場を構成する。
`Initial.atInitial` は、その単位元での値が指定した接ベクトルの座標に一致することを示す。
`LocalCurve` は局所微分方程式の解から、単位元を通る滑らかな群上の曲線を構成する。
`Translation.Composition` は、結合則から局所平行移動の合成と微分の合成則を示す。
`VectorField.Product.equivariance` はベクトル場の左不変性を表す。
`LocalCurve.Uniform.On.Comparison.addition` は、平行移動した曲線と時刻をずらした曲線を同じ Picard 解と比較して局所加法則を証明する。
`Homomorphism` はその局所加法則を実数全体の群準同型へ延長する。

`LocalHom.On` は十分小さい \(t/2^k\) に対して \(f(t/2^k)^{2^k}\) を用いる。
`At.independent` は許される分割次数によらないことを、`Addition.law` は大域加法則を証明する。
`Uniqueness.equal` は局所準同型と一致する大域準同型の一意性を示す。

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
