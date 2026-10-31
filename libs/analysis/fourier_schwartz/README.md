# Fourier 核と Schwartz 半ノルム

A06 の実装途中である。
複素指数関数、Schwartz 半ノルム、Schwartz 関数と重み付き全偏微分の L1 可積分性、Fourier 変換の滑らかさと Schwartz 保存を提供する。
微分・座標乗算・平行移動の公式と、平行移動不変性・積分下微分から導く部分積分を証明した。
畳み込み公式、Gaussian の変換、近似単位による反転公式は未実装である。
Gaussian 自体の滑らかさ・全ての多項式重みに対する減衰・Hermite 多項式による反復微分・Schwartz 性は構成済みである。

核と変換の規約は
\[
K(x,\xi)=e^{-i\sum_j x_j\xi_j},\qquad
\widehat f(\xi)=\int_{\mathbb R^n}f(x)K(x,\xi)\,dx
\]
である。
反転公式とその定数の証明はまだ含まない。

| API | 内容 |
| --- | --- |
| `ComplexCalculus` | 実部・虚部による複素値関数の実微分、和・積・合成・共役の微分 |
| `Phase.Global.value` / `derivative` / `addition` / `negative` / `modulus` | 局所 ODE 解から二倍角で構成した \(e^{it}\)、微分・加法・共役・絶対値 1 |
| `Phase.Global.Smooth` | 実部・虚部の滑らかさ |
| `Exponential.value` / `addition` | \(e^{\operatorname{Re}z}e^{i\operatorname{Im}z}\) と加法公式 |
| `Euclidean[n].Kernel` | 複素指数による Fourier 核、対称性・加法・反転・絶対値・滑らかさ |
| `Euclidean[n].Schwartz` / `seminorm` | 実 Schwartz 関数と重み付き上限 |
| `Euclidean[n].Operations` | 加法・スカラー倍・偏微分、半ノルムの三角不等式・斉次性・偏微分による添字移動 |
| `Euclidean[n].Complex` | 実部・虚部が Schwartz である複素関数、複素絶対値による半ノルム |
| `Euclidean[n].Integral.transform` | Lebesgue 測度上の任意の複素 L1 代表元の Fourier 変換 |
| `Euclidean[n].Integral.Continuity` | 共通可積分支配関数から証明した変換の連続性 |
| `Euclidean[n].Integral.Identities` | 原点での積分との一致、加法・複素スカラー倍との交換 |
| `Euclidean[n].Decay` / `Integrability` | dyadic box envelope の単調収束から構成した重み付き全偏微分の L1 可積分性 |
| `Euclidean[n].CoordinateMultiplication` / `Translation` | 座標乗算・平行移動による Schwartz 保存、移動幅に一様な可積分上界 |
| `Euclidean[n].IntegrationByParts` | Schwartz 偏微分の積分が 0 になる定理 |
| `Euclidean[n].Modulation` | Fourier 核との積の Schwartz 保存 |
| `Euclidean[n].Transform` / `Identities` | 滑らかさ、微分・線形性・平行移動の公式 |
| `Euclidean[n].Transform.Preservation.value` | Fourier 変換を Schwartz 空間の自己写像として構成 |
| `Examples[n]` | 任意の次元・関数・周波数を使う検査対象の利用例 |

`Directions` は座標の有限リストであり、`jet f d` はその順序で反復した偏微分である。
実半ノルムは
\[
p_{m,d}(f)=\sup_x(1+\sum_jx_j^2)^m|D^df(x)|
\]
として上限完備性から構成する。
`Schwartz` の定義では、滑らかさと全ての \(m,d\) での有界性だけを要求する。
複素半ノルムにも同じ式と複素絶対値を使い、`Complex.homogeneous` は複素スカラー \(c\) に対する \(p_{m,d}(cf)=|c|p_{m,d}(f)\) を証明する。

`Integral.section` は実部・虚部それぞれの積の可積分性を構成する。
`Integral.Continuity` は核の両成分の絶対値が 1 以下であることを使い、\(|\operatorname{Re} f|+|\operatorname{Im} f|\) を共通支配関数として `lp_spaces.On.Parametric.continuous` を適用する。
入力関数の可積分性は既存の `measure_convergence.On.Complex.Representatives` によって表す。
`Integrability.complex` は Schwartz 関数からこの型を構成する。

```ref
\import fourier_schwartz.Euclidean[n := n] \as E;
\import E.Integral[] \as Fourier;
\import Fourier.Identities[] \as Identities;
\import complex.Complex[] \as C;
\import C.Def[] \as D;

\definition addition[f, g: Fourier.Input][xi: E.Point]:
  Fourier.transform (Fourier.addInput f g) xi =
    D.add (Fourier.transform f xi) (Fourier.transform g xi) :=
  Identities.addition f g xi;
```

```sh
target/release/cli libs/analysis/fourier_schwartz --module fourier_schwartz --memory-mib 12288 --diagnostics compact --cache-stats
python3 scripts/check_all.py --initial-memory-mib 12288 --memory-mib 12288
```
