# 積分

Dedekind 実数の有界閉区間上で、リーマン積分とその \(L^1\) 完備化によるルベーグ積分を扱う。
実数の評価と極限には `real.Analysis.Estimates` / `Sequence` を使う。

| module | 内容 |
| --- | --- |
| [Real](src/Real.ref) | 実数の演算、端点と順序を持つ `Interval` |
| `Real.Division` | 二等分のタグ付き分割、リーマン和とその法則 |
| `Real.Riemann[interval].Def` / `Prop` | 有界性、積分の条件・一意性、定数関数、\(L^1\) の評価 |
| `Real.Lebesgue[interval].Def` / `Prop` | \(L^1\) Cauchy 列の商、積分の構成、代表列によらないこと |

## リーマン積分

\(a\le b\)、\(x_{n,k}=a+(b-a)k/2^n\)、任意のタグ \(\xi_k\in[x_{n,k},x_{n,k+1}]\) に対し、
\[
S_n(f;\xi)=\sum_{k=0}^{2^n-1}(x_{n,k+1}-x_{n,k})f(\xi_k)
\]
とする。
`HasIntegral[f, I]` は区間上の有界性と、すべてのタグについてこの和が一様に I へ収束する条件である。
`Function` は関数・積分値・その証明をまとめる。
定数 c の積分は \((b-a)c\) で、長さ零の区間も含む。

## ルベーグ積分

同じタグ付き分割で \(|f-g|\) の和を評価し、`SmallL1`、Cauchy 条件、差が零へ収束する同値関係を定義する。
`Representation` はリーマン可積分関数の \(L^1\) Cauchy 列、`Function` はその同値類である。
各元の積分値は代表列のリーマン積分値の極限として一意選択で構成し、`IntegralLaw` がすべての代表列について同じ極限を要求する。

`ofRiemann` はリーマン可積分関数を定数列の同値類に送り、`riemannAgreement` が積分値の一致を証明する。
`riemannLebesgueAgreement` は関数と積分値を直接量化した一致定理である。
[利用例](../../tests/projects/library/src/root.ref) は定数・長さ零の区間・代表列の同値性・一致定理を検査する。
検査方法は [ライブラリ一覧](../README.md#型検査) を参照。
