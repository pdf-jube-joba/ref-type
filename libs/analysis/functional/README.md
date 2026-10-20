# 関数解析

Dedekind 実数上のノルム空間、Hilbert 空間、線形汎関数を扱う。
`linear_algebra` の実ベクトル空間、`metric_spaces` の実数値距離、`calculus` の開集合上の部分微分を使う。

| module | 内容 |
| --- | --- |
| `Metric[Carrier]` | 収束・Cauchy 列・完備性、極限の一意性、収束列の Cauchy 性 |
| `Normed[V, space]` | ノルム、誘導距離、Banach 空間、ノルムの連続性 |
| `Normed.Operators` | 有界線形写像、距離評価、Cauchy 列・収束列の像 |
| `Normed.Hilbert[norm]` | 内積とノルムの整合性、完備性、表現ベクトルの一意性 |
| `Normed.Hilbert.Quadratic` | 平行四辺形恒等式、中点の二次形式、二次形式の連続性 |
| `Normed.Hilbert.Quadratic.Minimization` | 非空な閉中点凸集合でのノルムの最小点の存在 |
| `Normed.Hilbert.Riesz` | 有界実線形汎関数の内積による表現、表現ベクトルの構成 |
| `Order.Towers` / `Order.Maximality` | 包含順序上の増大的写像の不動点、極大鎖、Zorn の補題 |
| `Normed.HahnBanach` | 劣線形関数に支配された部分線形汎関数の全空間への延長 |
| `Normed.HahnBanach.OnSubspace` | 部分空間上の線形写像を引数に取る延長定理 |
| `Support[A]` | 台、コンパクト台、台の外での消滅、閉集合・コンパクト集合による台の評価 |
| `Continuous[A, topology]` | 連続関数、コンパクト台付き連続関数、同程度連続性、各点有界性、一様収束と極限の連続性 |
| `Measure[A]` / `Measure.Integral` | σ 加法族、非負拡張実数値測度、零集合、単関数による非負積分、符号付き積分の条件 |
| `Powers` / `Measure.Lp` | 実数指数の正冪の関係、有限指数の \(L^p\)、\(L^\infty\) の同値類 |
| `Sobolev[n].On[U].WithMeasure` | 試験関数、弱微分、\(W^{k,p}\) の同値類 |
| `ScalarLimits` | 実数列の積の極限、閉半直線、二進幾何列の評価 |
| `Examples` | 実数直線の Hilbert 空間、恒等汎関数の Riesz ベクトル、具体的な Hahn–Banach の利用 |

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

## 測度、\(L^p\)、Sobolev 空間

`Measure.Value` は非負拡張実数を下方に開いた実数の切断で表し、無限大も含める。
測度は σ 加法族と可算加法性を持つ。
`Null` は可測零集合に含まれる集合を表し、`AlmostEqual` は相違点集合が零集合であることを表す。

`Integral.lowerIntegral` は互いに素な可測集合と非負係数による有限単関数を使う非負積分である。
`Integral.Finite` は関数の非負性と積分の有限性を要求する。
`Integral.HasIntegral` は絶対可積分性と正負部分の積分の差を表す。

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
