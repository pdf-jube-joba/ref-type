# 積分

Dedekind 実数の有界閉区間上で、リーマン積分とルベーグ積分を扱う。
ルベーグ積分には、リーマン可積分関数の空間を \(L^1\) で完備化し、積分をその上に延長する構成を使う。
この構成の背景は [Richard Melrose の講義資料](https://math.mit.edu/~rbm/18-102-Sp16/Chapter2.pdf)にある。

| モジュール | 内容 |
| --- | --- |
| `Real` | 実数の演算、端点と順序を持つ `Interval` |
| `Real.Division` | 二等分のタグ付き分割、リーマン和、和の線形性・単調性・距離の評価 |
| `Real.Riemann[interval].Def` | 有界性、リーマン積分の条件、積分値付きの関数、\(L^1\) の近さ |
| `Real.Riemann[interval].Prop` | 積分値の一意性、定数関数、積分値の距離と \(L^1\) の近さの関係 |
| `Real.Lebesgue[interval].Def` | \(L^1\) Cauchy 列、同値関係、完備化の元、積分の仕様 |
| `Real.Lebesgue[interval].Prop` | 同値関係の法則、ルベーグ積分の構成、代表列によらないこと、リーマン積分との一致 |

実数の評価は `real.Analysis.Estimates`、実数列の収束と極限は `real.Analysis.Sequence` を使う。
これらは積分に依存しない共通の実数解析である。

## リーマン積分

\(a\le b\) に対し、\(x_{n,k}=a+(b-a)k/2^n\) とする。
各小区間のタグ \(\xi_k\in[x_{n,k},x_{n,k+1}]\) を任意に選び、
\[
  S_n(f;\xi)=\sum_{k=0}^{2^n-1}(x_{n,k+1}-x_{n,k})f(\xi_k)
\]
と置く。
`Division.Tags` はこのタグを二分木として保持し、`Level` と `Valid` は深さとタグの所属を検査する。

`Riemann.Def.HasIntegral[f, I]` は \(f\) が \([a,b]\) 上で有界であり、
\[
  \forall\varepsilon>0\;\exists N\;\forall n\ge N\;\forall\xi,
  \quad |S_n(f;\xi)-I|<\varepsilon
\]
が成り立つことを表す。
二等分を繰り返した等分割で、任意のタグについて一様に収束する形のリーマン積分の定義である。
`Riemann.Def.Function` は関数、積分値、この条件の証明をまとめる。
定数 \(c\) の積分値は \((b-a)c\) であり、\(a=b\) の場合も含む。

## ルベーグ積分

タグ付き和
\[
  A_n(f,g;\xi)=\sum_k(x_{n,k+1}-x_{n,k})|f(\xi_k)-g(\xi_k)|
\]
を用い、`SmallL1 f g epsilon` は十分大きいすべての \(n\) とすべてのタグに対して \(A_n(f,g;\xi)<\varepsilon\) となることを表す。
リーマン可積分関数に対するこの判定を用いて、\(L^1\) Cauchy 列と、その差が \(L^1\) で零に収束する同値関係を定義する。

`Lebesgue.Def.Representation` はリーマン可積分関数の \(L^1\) Cauchy 列であり、`Lebesgue.Def.Function` はその同値類である。
`equivalentClasses` は同値な列から同じ元が得られることを証明する。
各代表列 \((f_n)\) のルベーグ積分値は
\[
  \int_{[a,b]}[f_n]\,d\lambda=\lim_{n\to\infty}\int_a^b f_n(x)\,dx
\]
として構成する。
`IntegralLaw` は同じ同値類のすべての代表列がこの値に収束することを要求する。

同じ分割の和に対する
\[
  |S_n(f;\xi)-S_n(g;\xi)|\le A_n(f,g;\xi)
\]
を帰納法で証明し、`integralClose` によって積分値の距離を評価する。
これにより \(L^1\) Cauchy 列の積分値も Cauchy 列になる。
`real.Analysis.Sequence.limitLaw` は完備性から極限を構成し、`representativesAgree` は同値な代表列の極限値が等しいことを示す。
`candidateExists` と `candidateUnique` を用いた一意選択が `integral` を定義する。
`integralOfClass` は任意の代表列から構成した元の積分値を、その列の積分値の極限と結び付ける。

## 一致定理

`ofRiemann` はリーマン可積分関数を定数列の同値類へ送る。
`riemannAgreement` は任意の `Riemann.Def.Function` に対して
\[
  \operatorname{integral}(\operatorname{ofRiemann}(f))=f.\operatorname{integral}
\]
を証明する。
関数と積分値を直接量化した `riemannLebesgueAgreement` は、リーマン積分の条件から対応するルベーグ積分の元と同じ積分値の存在を示す。

```text
\import integration.Real[] \as I;
\import I.Riemann[interval := interval].Def[] \as Riemann;
\import I.Lebesgue[interval := interval].Def[] \as Lebesgue;
\import I.Lebesgue[interval := interval].Prop[] \as Integral;

\definition agreement: \forall (f: Riemann.Function) ->
  Integral.integral (Integral.ofRiemann f) = f.integral :=
  Integral.riemannAgreement;
```

[ライブラリの利用例](../../tests/projects/library/src/root.ref)は、単位区間の定数、負の定数、長さ零の区間、代表列の同値類の一致と一般の一致定理を検査する。

```sh
cargo run --quiet --bin cli -- libs/integration
cargo run --quiet --bin cli -- tests/projects/library
```
