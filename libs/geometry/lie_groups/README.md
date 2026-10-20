# リー群の基盤

`Dimension[n].OnManifold[M].LieGroup` は、Hausdorff・第二可算な滑らかな多様体 \(M\) 上の群構造で、積と逆元が滑らかなものとして定義する。
積の共同での滑らかさは、任意の有限次元滑らかな多様体からの滑らかな二つの写像の積が滑らかである、という条件で記述する。

| module | 内容 |
| --- | --- |
| `Smooth.Between` | 関数の滑らかさ、同じ関数を表す滑らかな写像の一意性、定数写像 |
| `Dimension.OnManifold.On` | 単位元の接空間、随伴線形写像 `Ad`、指数写像 `exp` と一径数部分群 `flow` |
| `Dimension.OnManifold.On.LocalProduct` | 単位元付近の積の滑らかな座標表示と、その微分から得る局所ベクトル場 |
| `Dimension.OnManifold.On.OneParameter` | 滑らかな一径数部分群、零での速度、積分データから得る `exp` |
| `Dimension.OnManifold.On.Integration` | 各接ベクトルを零での速度とする滑らかな一径数部分群の存在 |
| `Dimension.OnManifold.On.UniqueIntegral` | 同じ零での速度を持つ一径数部分群の一意性 |
| `Classical.On.Orthogonal` | 双線形形式を保つ可逆線形写像の群 |
| `Classical.On.Orthogonal.Special` | 指定次数の全交代形式を保つ部分群 |
| `Classical.On.Orthogonal.LieAlgebra` | 反対称な線形自己写像の部分リー代数 |
| `Euclidean[n]` | 標準内積、O(n)・SO(n)・\(\mathfrak{so}(n)\)、クリフォード代数と Pin・Spin・複素拡張の具体化 |
| `Euclidean.PinRepresentation` | twisted adjoint による Pin から O(n) への準同型と、Spin への制限 |
| `Euclidean.InnerProduct` | 内積の正定値性、非零ベクトルの正規化、反射の有理式による表示 |
| `Euclidean.SuccessorGeometry` | 次元を一つ増やした空間の直交補空間、最初の基底ベクトルを固定する変換の低次元への制限 |
| `OrthogonalAtlas.Dimension[n]` | O(n) の滑らかな多様体 `manifold` とリー群 `lieGroup` |
| `OrthogonalOrientation` | 行列式の滑らかさと、直交変換の行列式が \(\pm1\) になること |
| `SpecialOrthogonal[n]` | SO(n) の開部分群としての多様体 `manifold` とリー群 `lieGroup` |
| `CoefficientAtlas` | 点を分離する係数関数と局所座標から多様体・リー群を構成する一般のインターフェース |
| `PinSurjectivity` | 任意の直交変換の Pin への持ち上げ |
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
`Homomorphism.Smooth` は、二進分割ごとの開時間領域で滑らかな曲線を構成し、開被覆上で貼り合わせる。
`Generator.generates` は、その零での微分が元の接ベクトルに一致することを示す。
`On.integralExists` はチャートと局所微分方程式の解を選ぶ存在証明をまとめ、任意の接ベクトルに適用する。

`LocalHom.On` は十分小さい \(t/2^k\) に対して \(f(t/2^k)^{2^k}\) を用いる。
`At.independent` は許される分割次数によらないことを、`Addition.law` は大域加法則を証明する。
`Uniqueness.equal` は局所準同型と一致する大域準同型の一意性を示す。

`On.integralExists` と `On.integralUnique` により、各接ベクトル \(v\) を零での速度とする一径数部分群が一意に定まる。
`On.integral v` がその滑らかな写像を持つ一径数部分群、`On.flow v t` が時刻 \(t\) の値、`On.exp v` が時刻 \(1\) の値である。
`flowZero`、`flowAddition`、`flowGenerates` は、単位元・時間の加法・零での速度の法則を示す。
`OneParameter.Of.Coordinates.Field` は任意の一径数部分群を、その生成ベクトルの局所ベクトル場の解にする。
これに Picard 解の一意性を適用し、局所での一致を二進分割で実数全体に延長して一意性を得る。
`OneParameter.Integration` は一径数部分群の族を扱う構造で、`On.integration` がその標準の値である。

`Euclidean[n].orthogonalGroup` と `specialOrthogonalGroup` は、線形写像を台に持つ群構造である。
SO(n) は次数 \(n\) の全交代形式を保つ条件を用いる。
`soLieAlgebra` は \(\langle Ax,y\rangle=-\langle x,Ay\rangle\) を満たす自己写像の交換子リー代数である。
`cliffordScalarInjective` と `cliffordVectorInjective` は標準内積のクリフォード代数の標準写像の単射性を示す。
`PinRepresentation.map` は、生成ベクトル上の twisted adjoint と一致する直交変換を一意に選ぶ。
正の単位ベクトルには反射を、符号には恒等変換を対応させ、積・逆元による閉性から Pin 全体へ延長する。
`Kernel.iff` は核が正確に \(\{\pm1\}\) であることを示し、`PinSurjectivity.surjective n` は全射性を与える。
`homomorphism` は群準同型、`spinHomomorphism` は Spin に制限した準同型で、`spinOnVector` はその通常の共役作用による表示である。

`OrthogonalAtlas.atlasData` は、球面の立体射影と直交補空間への制限を使い、次元についての帰納法で O(n) の座標を構成する。
各段階で、局所表示とその逆、チャート族の被覆性、滑らかな行列の族に沿う座標の滑らかさを証明する。
`Euclidean.Atlas.On.FromPlots` は多様体から O(n) への写像の滑らかさを行列係数で判定し、`Lie` は積・逆元の滑らかさを示す。
`OrthogonalAtlas.Dimension[n].lieGroup` が、標準内積の直交群に対するその値である。

`OrthogonalOrientation.determinantSign` は、反射の行列式と次元についての帰納法から、任意の直交変換の行列式が \(\pm1\) になることを証明する。
行列式は多重線形形式の滑らかな評価として扱い、`SpecialOrthogonal[n]` はその正の部分を開部分群として構成する。
`SpecialOrthogonal[n].lieGroup` が SO(n) のリー群構造である。

\(\mathfrak{so}(n)\) と単位元の接空間との同定、Pin・Spin の被覆に沿う多様体構造、有限中心商の多様体構造は引き続き構成中である。

```sh
cargo run -p cli -- libs/geometry/lie_groups --module lie_groups
```
