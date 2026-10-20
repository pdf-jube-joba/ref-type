# 積分

Dedekind 実数の有界閉区間上で、リーマン積分とその \(L^1\) 完備化によるルベーグ積分を扱う。
実数の評価と極限には `real.Analysis.Estimates` / `Sequence` を使う。

| module | 内容 |
| --- | --- |
| [Real](src/Real.ref) | 実数の演算、端点と順序を持つ `Interval` |
| `Real.Division` | 二等分のタグ付き分割、リーマン和とその法則 |
| `Real.Division.Bounds` / `Mesh` / `Refinement` | 一様評価、分割幅、細分化に伴う誤差 |
| `Real.Division.Prefix` | 途中で切った区間の長さと和、細分化の評価と増分評価 |
| `Real.Riemann[interval].Def` / `Prop` | 有界性、積分の条件・一意性、定数関数、\(L^1\) の評価 |
| `Real.Riemann[interval].Uniform.Of` | 一様連続な有界関数の積分と原始関数の構成 |
| `Real.Riemann[interval].Continuous.Of` | 閉区間上の連続関数の可積分性、微分の基本定理 |
| `Real.Lebesgue[interval].Def` / `Prop` | \(L^1\) Cauchy 列の商、積分の構成、代表列によらないこと |
| `Vector[n, interval].Of` / `Comparison` | 有限次元ベクトル値の積分、原始関数、座標ごとの微分、ノルム評価 |

## リーマン積分

\(a\le b\)、\(x_{n,k}=a+(b-a)k/2^n\)、任意のタグ \(\xi_k\in[x_{n,k},x_{n,k+1}]\) に対し、
\[
S_n(f;\xi)=\sum_{k=0}^{2^n-1}(x_{n,k+1}-x_{n,k})f(\xi_k)
\]
とする。
`HasIntegral[f, I]` は区間上の有界性と、すべてのタグについてこの和が一様に I へ収束する条件である。
`Function` は関数・積分値・その証明をまとめる。
定数 c の積分は \((b-a)c\) で、長さ零の区間も含む。

`Continuous.Of[f].integral` は、閉区間上の連続関数のリーマン和が Cauchy 列になることを証明し、その極限から構成する。
区間のコンパクト性から有界性と一様連続性を導き、任意のタグに対する収束も示す。
`primitive` は分割和を任意の終点で切った和の極限で、左端で零、右端で積分値に一致する。
`fundamentalTheorem` は \(a<x<b\) で \(F'(x)=f(x)\) を証明する。
この証明では細分化の一様評価と、小区間の傾きを用いる増分評価を使う。
`Uniform.Comparison.primitiveBound` は入力関数の一様な差から原始関数の差を評価する。
ベクトル値の場合も同じ評価を最大値ノルムについて証明し、次元零を含めて扱う。

## ルベーグ積分

同じタグ付き分割で \(|f-g|\) の和を評価し、`SmallL1`、Cauchy 条件、差が零へ収束する同値関係を定義する。
`Representation` はリーマン可積分関数の \(L^1\) Cauchy 列、`Function` はその同値類である。
各元の積分値は代表列のリーマン積分値の極限として一意選択で構成し、`IntegralLaw` がすべての代表列について同じ極限を要求する。

`ofRiemann` はリーマン可積分関数を定数列の同値類に送り、`riemannAgreement` が積分値の一致を証明する。
`riemannLebesgueAgreement` は関数と積分値を直接量化した一致定理である。
[積分の性質](src/Real/Riemann/Prop.ref) に定数と区間についての法則をまとめる。
