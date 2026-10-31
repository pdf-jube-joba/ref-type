# Schwartz 空間と Fourier 変換

有限次元の実・複素 Schwartz 関数、Lebesgue 積分による Fourier 変換、Schwartz 保存、Gaussian 変換、近似単位による反転公式を構成する。
次元は任意の自然数であり、0 次元も含む。

規約は
\[
K(x,\xi)=e^{-i\sum_jx_j\xi_j},\qquad
\widehat f(\xi)=\int_{\mathbb R^n}f(x)K(x,\xi)\,dx
\]
である。
`Translation.translate a f` は \(x\mapsto f(x+a)\) を表す。

| API | 内容 |
| --- | --- |
| `ComplexCalculus` | 複素値関数の実変数微分、和・積・合成・共役 |
| `Phase.Global` / `Exponential` | 局所 ODE 解から構成した \(e^{it}\)、複素指数関数、加法・共役・絶対値 |
| `Euclidean[n].Schwartz` / `seminorm` | 実 Schwartz 関数、重み付き上限半ノルム |
| `Euclidean[n].Complex` | 複素 Schwartz 関数、複素絶対値による半ノルムと複素斉次性 |
| `Euclidean[n].Operations` / `CoordinateMultiplication` / `Translation` | 加法・スカラー倍・反復微分・座標乗算・平行移動による Schwartz 保存 |
| `Euclidean[n].Integrability` | Schwartz 関数と全ての重み付き偏微分の L1 代表元 |
| `Euclidean[n].Integral` | 任意の複素 L1 代表元の積分 Fourier 変換、連続性・線形性 |
| `Euclidean[n].Transform` / `Identities` | Fourier 変換の滑らかさ、微分・座標乗算・平行移動公式 |
| `Euclidean[n].Transform.Preservation.value` | Fourier 変換を Schwartz 空間の自己写像として構成 |
| `Euclidean[n].Convolution.convolve` / `Complex.function` | 実・複素 Schwartz 畳み込み、微分・可換性 |
| `Euclidean[n].Convolution.Complex.Fourier` | \(\widehat{f*g}=\widehat f\,\widehat g\) |
| `Euclidean[n].Gaussian` | \(G_n(x)=e^{-\sum_jx_j^2/2}\)、Schwartz 性・正の積分・Fourier 公式 |
| `Euclidean[n].Gaussian.Density` | 正規化 Gaussian 密度と積分 1 |
| `Euclidean[n].Gaussian.Approximation` | 正規化 Gaussian 近似単位の各点収束 |
| `Euclidean[n].Inversion` | 反転公式、Schwartz 値の逆写像、左右の逆恒等式 |
| `Normalization` | Gaussian 積分による \(\pi\)、次元ごとの積分、\((2\pi)^{-n}\) |
| `Examples[n]` | 任意の次元・関数・周波数に対する検査対象の利用例 |

`Directions` は座標の有限リストであり、`jet f d` はその順序で反復した偏微分である。
半ノルムは
\[
p_{m,d}(f)=\sup_x(1+\sum_jx_j^2)^m|D^df(x)|
\]
を上限完備性から構成する。
`Schwartz` の仮定は滑らかさと全ての \(m,d\) に対するこの有界性である。
複素関数の実部・虚部の和による評価は補助評価であり、複素半ノルム自体には複素絶対値を使う。

`Transform.Identities.spatialDerivative` は \(\widehat{\partial_jf}(\xi)=i\xi_j\widehat f(\xi)\) を証明する。
`coordinateReal` / `coordinateImaginary` は \(\partial_{\xi_j}\widehat f=-i\widehat{x_jf}\) の両成分の等式である。
`translation` は \(\widehat{f(\mathord\cdot+a)}(\xi)=e^{i a\cdot\xi}\widehat f(\xi)\) を証明する。
`Convolution.partialFunction` と `Convolution.Complex.partial` は畳み込みの偏微分を第 2 因子に移す。
`Convolution.Complex.commutative` により両因子を交換できる。

## Gaussian と正規化

\[
M_n=\int G_n(x)\,dx,\quad c=M_1,\quad \pi=\frac{c^2}{2},\quad
M_n=c^n=(\sqrt{2\pi})^n
\]
という Gaussian 積分による定義を採用する。
`Mass.positive`、`Factorization.law`、`Normalization.dimension` と `squareRoot` はそれぞれ正値性、積への分解、次元公式と平方根公式を証明する。
数値定数や Gaussian 積分の評価を仮定する公理は追加していない。

\[
\widehat{G_n}(\xi)=M_nG_n(\xi),\qquad
H_\varepsilon(x)=\frac{G_n(x/\varepsilon)}{\varepsilon^nM_n},\qquad
\int H_\varepsilon=1
\]
を `Gaussian.Fourier.formula` と `Gaussian.Density` が与える。
`Gaussian.Approximation.approximateIdentity` は
\[
\frac1{M_n}\int G_n(y)f(x-2^{-k}y)\,dy\longrightarrow f(x)
\]
を証明する。

反転の主定理は
\[
f(x)=\frac1{(2\pi)^n}\int\widehat f(\xi)e^{i x\cdot\xi}\,d\xi
\]
である。
`Inversion.inverse` が右辺を定義し、`theorem` がその等式を証明する。
`inverseSchwartz`、`inverseValue`、`leftInverse`、`rightInverse` は同じ逆写像を Schwartz 関数として与える。

## 証明の構成

`Decay` は dyadic box の指示関数の単調増加和から可積分な共通上界を構成し、Schwartz 可積分性を導く。
積分下微分では `lp_spaces.On.Differentiation.derivative` の差分商支配条件を平均値定理で満たし、連続性には `On.Parametric.continuous` を使う。
部分積分は Lebesgue 積分の平行移動不変性を微分して証明する。
Fourier 保存は \((1-\Delta)^m\) の Fourier 公式と L1 評価による。
Gaussian の反復微分には具体的な Hermite 多項式を構成する。
畳み込み公式と Gaussian 正則化の積分交換は既存の Fubini 定理から導く。
反転では正則化された積分の Gaussian 近似単位による極限と、Fourier 側の支配収束による極限を一致させる。

```ref
\import fourier_schwartz.Euclidean[n := n] \as E;
\import E.Complex[] \as S;
\import E.Transform[] \as Fourier;
\import E.Inversion[] \as Inversion;

\definition transformed[f: S.Function]: S.Function := Fourier.Preservation[].value f;
\definition recovered[f: S.Function][x: E.Point]:
  Inversion.inverse (transformed f) x = S.value f x := Inversion.theorem f x;
```

```sh
target/release/cli libs/analysis/fourier_schwartz --module fourier_schwartz --memory-mib 12288 --diagnostics compact --cache-stats
python3 scripts/check_all.py --initial-memory-mib 12288 --memory-mib 12288
```
