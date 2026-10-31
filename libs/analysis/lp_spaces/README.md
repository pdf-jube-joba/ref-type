# Lp 空間

`lp_spaces.On[A, mu]` は任意の測度空間で、既存の `functional_analysis.Measure.Lp.Finite` の商を使う。
有限指数 \(1\le p<\infty\) の実線形・ノルム構造、Hölder・Minkowski、完備性、実・複素 \(L^2\) の Hilbert 構造と可積分単関数の稠密性を提供する。
既存の `LInfinity` 商についても essential supremum ノルムと実 Banach 空間構造を与える。
これらに測度の有限性・σ 有限性・完備性は要求しない。

| API | 内容 |
| --- | --- |
| `Powers.value` / `Powers.law` / `Powers.Unique.unique` | 非負実数の冪、既存の有理数冪比較との一致と一意性 |
| `Powers.Algebra` / `Powers.Convergence` | 冪の積・反復・順序・根と数列極限 |
| `Powers.Young.inequality` | 共役な有限正指数の Young 不等式 |
| `On.Finite[p]` | 既存商、加法・逆元・スカラー倍、代表元の標準モーメントとノルム値 |
| `On.Infinity.Vector.space` / `Norm.structure` / `Completion.complete` | 既存 L∞ 商の実ベクトル・ノルム・Banach 構造 |
| `On.Endpoint.inequality` / `rightInequality` | L1–L∞ と L∞–L1 の積の可積分性と Hölder の評価 |
| `On.Finite[p].Vector.space` | 既存商の実ベクトル空間構造 |
| `On.Norm[p].norm` / `metric` | Minkowski を含むノルム空間と誘導距離 |
| `On.Holder[exponents]` | 共役指数の積の可積分性と Hölder の評価 |
| `On.Norm[p].Dominated[d].theorem` | 共通の Lp 支配関数の下でのノルム収束 |
| `On.Completion[p].complete` | 任意の Cauchy 列に対する商内の極限の存在 |
| `On.Hilbert.inner` / `hilbert` | 積の積分による実 L2 内積と Hilbert 構造 |
| `On.Complex.Geometry.norm` / `On.Complex.Inner.inner` / `On.Complex.Complete.hilbert` | 任意の測度上の複素 L2 のノルム・内積・完備性 |
| `On.Complex.Characterization.equivalence` | 実部・虚部の L2 条件と、複素可測かつ絶対値の L2 条件の同値 |
| `On.SimpleApproximation[p].dense` | L1 可積分な実単関数による Lp 近似 |
| `On.Pullback[p, map]` | 測度保存写像の引き戻し、a.e. 商上の定義・ノルム・距離の保存 |
| `Euclidean[n].Translation[p].continuous` / `Group.continuousAt` | 有限 p の Lebesgue Lp における平行移動の ε–δ ノルム連続性、合成則と等長性 |
| `Euclidean[n].Compact[p]` | コンパクト台付き連続・滑らかな関数の可測性・有界性・Lp 代表元 |
| `Euclidean[n].Approximation[p].smoothDense` / `continuousDense` | Euclid の Lebesgue 測度、有限実指数 `1 ≤ p < ∞` での C∞ コンパクト台・連続コンパクト台関数の稠密性 |
| `Examples[A, mu, p]` | 一般の代表元・商・指数を使う検査される利用例 |

補助の非負指数 API は零底を零とする `PositivePower.atZero` の規約に従う。
Lp の指数とノルムの根の指数は正である。

`On.ConjugateExponents` は既存の有限指数二つと \(p^{-1}+q^{-1}=1\) をまとめる。
`Holder.representative` は実際の点ごとの積の可積分代表で、積の可測性も関数の可測性から証明する。

完備性の証明は Cauchy 列から二進的に小さい差分を持つ部分列を選び、絶対差分の部分和の p 乗に単調収束を適用する。
a.e. 極限を例外零集合上で零にした可測代表を構成するため、元の測度が完備である必要はない。
単関数近似は正・負部分に対する既存の有限単関数近似を使い、各段階の L1 可積分性を別に示す。

```ref
\import lp_spaces.On[A := A, mu := mu] \as L;
\import L.Finite[p := p] \as F;
\import L.Finite[p := p].Vector[] \as V;
\import L.Norm[p := p] \as N;
\import functional_analysis.Normed[V := F.Space, space := V.space] \as Normed;

\definition complete: Normed.IsBanach N.norm := L.Completion[p := p].complete;
```

複素 L2 の内積は第二変数について線形で、点ごとの `conj(f) * g` の積分である。
実部・虚部の Cauchy 列の実 L2 極限から複素 L2 の極限を構成する。

Euclid 上の稠密性は、任意の Lp 関数の箱による切り詰め、単関数の有限セル分解、測度の正則性、G01 の滑らかな cutoff と Lp の優収束から証明する。
この稠密性は有限 p に限定され、L∞ については主張しない。`EuclideanExamples[n, p]` が一般の次元・指数・商の元を使う検査対象の利用例である。

L∞ の完備性は、列の各項と全ての差分の上界に対する可算例外集合をまとめ、その外で点ごとの Cauchy 極限を取り、可測な零集合上で零にした代表を構成して証明する。

A05 の後続作業は、近似単位・平滑化である。

通常検査はリポジトリのルートから実行する。

```sh
target/release/cli libs/analysis/lp_spaces --module lp_spaces --diagnostics compact --no-progress --memory-mib 12288
source /workspace/ref-type-env.sh && cargo build -p cli --release --locked && python3 scripts/check_all.py --initial-memory-mib 12288 --memory-mib 12288
```
