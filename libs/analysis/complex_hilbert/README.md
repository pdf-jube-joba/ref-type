# 複素 Hilbert 空間

A19 の作業中パッケージである。
複素ノルム空間を実スカラー制限によって既存の実関数解析へ接続し、複素 Riesz 表現、有界随伴、閉部分空間への直交射影を構成する。

## 実装状況

| 要件 | 状態 |
| --- | --- |
| 複素ノルム空間・Hilbert 空間と実関数解析への接続 | 実装・検査済み |
| 複素 Riesz 表現の構成・表現式・一意性 | 実装・検査済み |
| 有界作用素の随伴、同じ評価定数での有界性、随伴等式・一意性 | 実装・検査済み |
| 閉部分空間への縮小的・冪等・自己随伴な直交射影 | 実装・検査済み |
| 直交補と商の比較 | 商ノルムを構成し、等長線形同型と最小ノルム代表を実装・検査済み |
| 有限階数の因子分解、零作用素、和、前後の合成 | 実装・検査済み |
| コンパクト作用素と有限階数近似の比較 | 未実装 |
| コンパクト作用素の和・合成・ノルム極限・随伴による閉性 | 未実装・検査未実行 |
| 恒等作用素のコンパクト性から有限次元性 | 未実装・検査未実行 |

## 公開 API

| module | 内容 |
| --- | --- |
| `Scalars` | 複素積の実部・虚部、\(i\) 倍の実部、\(\lvert\operatorname{Re}z\rvert\le\lvert z\rvert\) |
| `Space[V, space]` | 複素ベクトル空間の実スカラー制限、複素斉次性を持つノルム |
| `Space.Hilbert[norm, inner]` | 既存の Hermitian 内積の実部、ノルムとの整合性、完備性、実 Hilbert 構造 |
| `Space.Hilbert.Riesz` | 有界複素線形汎関数の Riesz ベクトル、表現式、存在、一意性 |
| `Space.Hilbert.Estimates` | 平方完成、実部内積の Cauchy–Schwarz 評価 |
| `Space.Operators[W, target, norm, targetNorm]` | 有界複素線形作用素、実有界作用素への変換 |
| `Space.Operators.Adjoints[inner, targetInner]` | 随伴の構成・複素線形性・有界性・一意性 |
| `Space.Hilbert.Subspaces` | 閉部分空間、位相的閉性からの接続 |
| `Space.Hilbert.Subspaces.In[S].Projection[complete]` | 閉部分空間上の Riesz 表現からの直交射影 |
| `Projection.Complement` / `Complement.Norm` | 直交補、補射影、商ノルム、等長線形同型、最小ノルム代表 |
| `FiniteRank[V, W, source, target]` | 有限自由空間を通る因子分解、和・合成の因子分解 |
| `Examples` | 零 Hilbert 空間、Riesz、恒等作用素の随伴、全空間への射影、商との比較、零作用素と和の有限階数性 |

内積は第二変数について複素線形とする。
Riesz ベクトルは \(f(x)=\langle y,x\rangle\)、随伴は
\[
\langle Tx,y\rangle=\langle x,T^*y\rangle
\]
を満たす。
有界作用素 \(T\) の評価定数 \(c\ge0\) から、同じ定数で
\(\lVert T^*y\rVert\le c\lVert y\rVert\) を証明する。

Riesz 表現は実部の有界実線形汎関数に既存の実 Riesz 定理を適用し、\(i\) 倍で評価することで虚部の等式を回復する。
随伴の行汎関数の有界性は、正値内積の平方完成から証明した実部内積の Cauchy–Schwarz 評価による。

閉部分空間はノルム収束列に関して閉じた線形部分空間である。
`closedOfTopological` が通常のノルム位相における閉性をこの条件へ移す。
制限した Hilbert 空間の完備性を証明し、その Riesz 表現から射影を構成する。
射影の存在や随伴の存在を構造の仮定には含めない。

`FiniteRank.Through[n].Factor f` は \(V\to\mathbb C^n\to W\) の線形因子分解を保持する。
有限階数性はこの因子分解があることを表す代数的性質であり、有界性やコンパクト性を定義に含めない。

## コンパクト性に必要な共通 API

現行の `metric_spaces.MetricSpace.Compactness` は Lebesgue 数と一様連続性を扱い、全有界性と完備性からのコンパクト性を公開していない。
`functional_analysis.Normed` には有限次元ノルム空間の閉球のコンパクト性や有限次元部分空間の閉性がない。
次の共通 API が、標準の「単位球の像の閉包がコンパクト」という定義と Hilbert 空間上の有限階数近似を結ぶために必要である。

| 配置案 | 最小 API | 用途 |
| --- | --- | --- |
| `metric_spaces.MetricSpace.Compactness` | 有限 \(\varepsilon\)-ネットによる `TotallyBounded metric S`、コンパクト集合の全有界性、完備空間での全有界集合の閉包のコンパクト性 | 作用素像の相対コンパクト性とノルム極限を扱う |
| `functional_analysis.Normed.FiniteDimensional` | 既存の有限基底とノルムから、閉有界球のコンパクト性と有限次元線形部分空間の閉性を証明する | 有限階数作用素のコンパクト性、有限ネットが張る空間への射影を扱う |

これらの共通 API の構築は未着手である。
共通 API の整備後に、有限階数近似との同値、コンパクト性の四つの閉性、恒等作用素からの有限次元性を完成させる。

## 検査

```sh
cargo build -p cli --locked
mkdir -p work
target/debug/cli libs/analysis/complex_hilbert --module complex_hilbert --full-check-local --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/a19-target-final.json
target/debug/cli libs/analysis/complex_hilbert --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/a19-dependencies-final.json
```

workspace の `libs/refcache/` を共有する。
全要件が完了するまでは Draft として扱う。
