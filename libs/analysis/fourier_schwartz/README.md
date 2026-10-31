# Fourier 核と Schwartz 半ノルム

A06 の実装途中である。
現在は複素指数関数、Schwartz 関数の半ノルム、複素 L1 上の積分 Fourier 変換とその連続性・線形性を提供する。
Schwartz 関数の可積分性、座標乗算・平行移動・畳み込みとの交換、Fourier 変換による Schwartz 空間の保存、Gaussian の変換、近似単位による反転公式は未実装である。

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
現時点でこの型を `Schwartz` から自動的に構成する API は含まない。

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
