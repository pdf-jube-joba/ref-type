# 関数解析

Dedekind 実数上のノルム空間、Hilbert 空間、線形汎関数を扱う。
`linear_algebra` の実ベクトル空間、`metric_spaces` の実数値距離、`calculus` の開集合上の部分微分を使う。

| module | 内容 |
| --- | --- |
| `Metric[Carrier]` / `Metric.Geometry[d]` | 収束・Cauchy 列・完備性、入れ子閉集合の共通部分、Baire の定理 |
| `Normed[V, space]` | ノルム、誘導距離、Banach 空間、ノルムの連続性 |
| `Normed.Operators` / `Operators.OpenMapping[f]` | 有界線形写像、距離評価、収束列の像、Banach 空間間の開写像定理 |
| `Normed.Hilbert[norm]` | 内積とノルムの整合性、完備性、表現ベクトルの一意性 |
| `Normed.Hilbert.Quadratic` | 平行四辺形恒等式、中点の二次形式、二次形式の連続性 |
| `Normed.Hilbert.Quadratic.Minimization` | 非空な閉中点凸集合でのノルムの最小点の存在 |
| `Normed.Hilbert.Riesz` | 有界実線形汎関数の内積による表現、表現ベクトルの構成 |
| `Order.Towers` / `Order.Maximality` | 包含順序上の増大的写像の不動点、極大鎖、Zorn の補題 |
| `Normed.HahnBanach` | 劣線形関数に支配された部分線形汎関数の全空間への延長 |
| `Normed.HahnBanach.OnSubspace` | 部分空間上の線形写像を引数に取る延長定理 |
| `Support[A]` | 台、コンパクト台、台の外での消滅、閉集合・コンパクト集合による台の評価 |
| `Continuous[A, topology]` / `Continuous.Uniform` | 連続関数、コンパクト台付き連続関数、同程度連続性、各点有界性、一様収束、一様位相 |
| `Continuous.ArzelaAscoli` | 閉関数族のコンパクト性と一般の関数族の相対コンパクト性を与える Arzelà–Ascoli の定理 |
| `Filters[A]` / `Filters.Compactness` | 超フィルターへの延長、写像による像、超フィルターの極限によるコンパクト性の特徴づけ |
| `Measure[A]` / `Measure.Integral` | σ 加法族、非負拡張実数値測度、零集合、単関数による非負積分、符号付き積分の条件 |
| `Powers` / `Measure.Lp` | 実数指数の正冪の関係、有限指数の \(L^p\)、\(L^\infty\) の同値類 |
| `Sobolev[n].On[U].WithMeasure` | 試験関数、弱微分、\(W^{k,p}\) の同値類 |
| `ScalarLimits` | 実数列の積の極限、閉半直線、二進幾何列の評価 |
| `Examples` / `Examples.Ascoli` | 実数直線の Hilbert 空間、恒等汎関数の Riesz ベクトル、Hahn–Banach、恒等写像の開性、有界な定数関数族の相対コンパクト性 |

## Hahn–Banach

`Sublinear` は \(p(0)=0\)、劣加法性、非負実数に関する正斉次性を持つ。
`LinearGraph` は部分空間上の線形汎関数のグラフであり、各点の値が \(p\) 以下であることを要求する。
`hahnBanach` はこのグラフと劣線形性から、全空間上の実線形汎関数を返す存在定理である。
`GlobalExtension` は元のグラフとの一致、加法性、斉次性、支配条件をまとめる。

証明は実数の下限から一方向への延長値を構成し、部分延長の鎖の合併に Zorn の補題を適用する。
`OnSubspace[subspace]` の `Functional` と `hahnBanachOnSubspace` を使うと、既存の `linear_algebra` の部分空間・線形写像から直接適用できる。

## Hilbert 空間と Riesz 表現

`Hilbert[inner]` は \(\langle x,x\rangle=\lVert x\rVert^2\) と誘導距離の完備性を要求する。
`Riesz.Functional` はノルム評価を持つ実線形汎関数である。
`riesz` は各汎関数 \(f\) に対して
\[
f(x)=\langle y,x\rangle\qquad(x\in V)
\]
を満たす \(y\) の存在を証明する。
`vector` は一意選択でそのベクトルを構成し、`vectorLaw` が表現式、`representingVectorUnique` が一意性を与える。

証明では閉アフィン集合 \(f^{-1}(1)\) 上のノルムの最小点を構成する。
平行四辺形恒等式から最小化列が Cauchy 列になることを示し、完備性で極限を取り、最小点の核への直交性から表現を得る。
零汎関数は別に扱う。
`Examples.identityVector` は実数直線の恒等汎関数の表現ベクトルが \(1\) であることを検査する。

## 開写像定理

`Operators.OpenMapping[f].openMapping` は実 Banach 空間の間の有界全射線形写像が開写像であることを証明する。
引数は定義域と値域の完備性、全射性、定義域の開集合であり、その像が値域で開集合になる。
`unitLifting` は原点のある近傍に属するベクトルが、定義域の開単位球内に逆像を持つという量的な形を与える。

証明では像を近似できる集合が閉じていることを示し、値域の Baire の定理から原点の近傍を得る。
近似の誤差を二進的に縮め、定義域の入れ子閉球の共通部分から正確な逆像を構成する。
`Metric.Geometry.Baire` には開稠密集合の可算共通部分の稠密性と、可算閉被覆の少なくとも一つが内点を持つ形を用意する。

## Arzelà–Ascoli

`Continuous.Uniform.topology` は実数値連続関数の一様位相である。
定義域は任意のコンパクト位相空間でよく、空間が空の場合も含む。
`Continuous.ArzelaAscoli.arzelaAscoliClosure` は、同程度連続で各点有界な関数族の閉包が一様位相でコンパクトになることを証明する。
`arzelaAscoli` はさらに関数族が閉集合である場合、その関数族自体がコンパクトになる形である。

証明は超フィルターを使う。
各点の値をコンパクトな実閉区間に入れて極限を取り、同程度連続性から極限の連続性を示す。
定義域の有限部分被覆によって各点での収束を一様収束へ移し、超フィルターによるコンパクト性の特徴づけを適用する。
`Examples.Ascoli` は、絶対値が \(1\) 以下の定数関数族について前提を検証し、この定理を適用する。

## 測度、\(L^p\)、Sobolev 空間

`Measure.Value` は非負拡張実数を下方に開いた実数の切断で表し、無限大も含める。
測度は σ 加法族と可算加法性を持つ。
`Null` は可測零集合に含まれる集合を表し、`AlmostEqual` は相違点集合が零集合であることを表す。

`Integral.lowerIntegral` は互いに素な可測集合と非負係数による有限単関数を使う非負積分である。
`Integral.Finite` は関数の非負性と積分の有限性を要求する。
`Integral.HasIntegral` は絶対可積分性と正負部分の積分の差を表し、`integralUnique` が積分値の一意性を示す。
`lowerIntegralMono` は下積分の単調性、`finiteMono` は非負関数の有限性の下方継承を示す。
`Integral.integral` は可積分関数の積分を与え、`Integral.Null.quotientIntegral` はほとんど至る所一致する代表元の商上の積分である。
`Measure.Finite` は可測集合について測度の有限加法性と単調性を示し、`Measure.AlmostEverywhere` は零集合の有限合併と a.e. 一致の同値関係を示す。

`Powers.Exponent` は実数 \(p\ge1\) である。
`PositivePower[a,p,y]` は非負実数の \(y=a^p\) を自然数冪の有理数比較で表す。
`Lp.Finite[p].Space` は可測で \(p\) 次モーメントが有限な関数の、ほとんど至る所の一致による商である。
`LInfinity` は本質的有界な可測関数についての同じ商である。
これらは関数空間の定義であり、ノルムや完備性をまとめた構造ではない。

Sobolev 空間はユーザーが指定する測度を引数に取る。
開集合 \(U\subset\mathbb R^n\) 上の試験関数には、全次数の連続な部分微分族とコンパクト台を要求する。
弱微分は各試験関数に対する
\[
\int_U u\,D^\alpha\varphi\,d\mu
=(-1)^{|\alpha|}\int_U g\,\varphi\,d\mu
\]
で定義し、次数 \(k\) 以下の弱微分が \(L^p\) に属する関数を同値類にする。
通常の \(W^{k,p}(U)\) には Lebesgue 測度を渡す。
このパッケージは Euclid 空間上の Lebesgue 測度の構成を含まない。

## 検査

```sh
cargo run -p cli -- libs/analysis/functional --module functional_analysis
cargo run -p cli -- libs/analysis/functional --module functional_analysis.Examples
```

workspace の `libs/refcache/` を共有する。
