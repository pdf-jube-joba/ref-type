# L² Fourier 変換と乗算作用素

A06 の [fourier_schwartz](../fourier_schwartz/README.md) の Lebesgue 積分による Fourier 変換を、既存の [lp_spaces](../lp_spaces/README.md) の `On.Complex.Space` 上のユニタリ同型に延長する。
次元は任意の自然数であり、0 次元も含む。
内積は第二変数について線形である。

A06 の規約に合わせ、Gaussian 質量を \(M_n=(\sqrt{2\pi})^n\) として
\[
\mathcal F f=M_n^{-1}\widehat f,
\qquad
\mathcal F^{-1}f=M_n\,\widehat{\ }^{-1}f
\]
と正規化する。
`Schwartz.coefficient` が \(M_n^{-1}\) を、`Unitary.forward` と `backward` が延長後の二つの写像を与える。

| API | 内容 |
| --- | --- |
| `Euclidean[n].Embedding` | Schwartz 関数から既存の複素 L² 商への線形写像 |
| `Parseval[f, g].law` | 非正規化変換に対する \(\langle\widehat f,\widehat g\rangle=M_n^2\langle f,g\rangle\) |
| `Schwartz.parseval` / `norm` | 正規化後の内積・ノルム保存 |
| `CompactEmbedding[f]` / `Density.dense` | コンパクト台滑らかな関数の Schwartz 性と複素 L² 内の稠密性 |
| `Extension[map, preserves]` | 稠密部分上の等長写像の、近似列に依存しない完備空間への延長 |
| `Unitary.forward` / `backward` | 既存の複素 L² 上の互いに逆な複素線形写像 |
| `Unitary.operator` / `inverseOperator` | ノルム上界 1 の有界線形作用素 |
| `Unitary.norm` / `parseval` / `adjoint` | ノルム・内積保存と \(\mathcal F^*=\mathcal F^{-1}\) |
| `Multiplication.Symbol` / `By[symbol]` | 有界可測な複素関数による L² 上の乗算 |
| `Multiplier[symbol].value` / `bound` | \(T_a=\mathcal F^{-1}a\mathcal F\)、\(\|T_af\|_2\le C\|f\|_2\) |
| `Multiplier[symbol].adjoint` | \(T_a^*=T_{\overline a}\) |
| `Conjugation.value` / `fourier` | 商上の複素共役と \(\mathcal F\overline f=\overline{\mathcal F^{-1}f}\) |
| `Weights.Weight` / `Weighted[weight]` | \(w\ge1\) で可測な有界逆数を持つ重みの Fourier 空間 |
| `Weights.Integer[m]` / `Integer[m].ofSchwartz` | \(w_m(\xi)=(1+|\xi|^2)^m\) の重み付きノルム |
| `Integer[m].norm` | \(\|w_m\mathcal Ff\|_2=\|(1-\Delta)^mf\|_2\) |
| `Derivatives.Comparison[m].derivative` | \(|d|\le2m\) の全反復偏微分に対する \(\|D^df\|_2\le\|w_m\mathcal Ff\|_2\) |
| `Expansion.comparison` | 逆向きの、有限個の整数階微分ノルムの和による評価 |
| `Examples[n]` | 任意の次元・L² 類・Schwartz 関数・記号を使う検査される利用例 |

`Weighted.Vector` は \(w\mathcal Ff\) に対応する既存の L² の元である。
ノルム・内積・完備性はその L² 構造から得られ、`physical` が \(\mathcal F^{-1}(w^{-1}u)\) として元の関数空間へ埋め込む。
`injective` はこの埋め込みの単射性を、`controlsPhysical` は \(\|f\|_2\le\|f\|_w\) を証明する。
`Input` と `ofFunction` は、任意の L² 代表元と、その重み付き積が L² であることの証拠をこの空間へ送る。
`inputFrequency` と `inputPhysical` によりその対応を確認できる。

`Expansion.derivativeSum` は
\[
B_0(f)=\|f\|_2,\qquad
B_{m+1}(f)=B_m(f)+\sum_jB_m(\partial_j^2f)
\]
で定義する。
したがって \(B_m\) は \(2m\) 階以下の実際の偏微分の L² ノルムを有限回加算した量であり、
\[
\|D^df\|_2\le\|w_m\mathcal Ff\|_2\le B_m(f)
\quad (|d|\le2m)
\]
が得られる。

Parseval の証明は、Schwartz 関数の L¹ 性と有界性から L² 代表元を構成し、積分の Fubini 交換と A06 の反転公式を使う。
延長では二進誤差の Schwartz 近似列を取り、等長性で Fourier 像の Cauchy 性を証明する。
完備性で得た極限が全ての近似列に共通であることから写像を一意に定義する。
整数階微分の評価では微分記号の絶対値の二乗を \((1+|\xi|^2)^{|d|}\) で評価し、実際の L² ノルムの単調性に移す。
新たな数学公理は追加していない。

```sh
target/release/cli libs/analysis/fourier_l2 --module fourier_l2 --memory-mib 8192 --diagnostics compact --no-progress --cache-stats
python3 scripts/check_all.py --initial-memory-mib 12288 --memory-mib 12288
```

固定ソースの A07 全22モジュールをソースから再検査し、依存970モジュールを再利用した。
A06・Lp・複素 Hilbert 空間の回帰検査と、通常の全11,729対象の検査も終了コード0で完了した。
通常全体検査は新規11,337・再利用392、保存失敗・破損読み取りは0、worker 回復は1である。
最後の既存パッケージ `compact_support_k` はメモリ割当失敗後に checkpoint 35685 から再開し、全対象の受理を確認した。
