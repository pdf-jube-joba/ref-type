# 複素 Hilbert 空間

複素 Hilbert 空間とコンパクト作用素を扱う。
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
| コンパクト作用素の定義、零値作用素、像の全有界性 | 実装・個別検査済み |
| コンパクト作用素と有限階数近似の同値 | 実装・個別検査済み |
| コンパクト作用素の和、前後合成、ノルム極限、随伴による閉性 | 実装・個別検査済み |
| 恒等作用素のコンパクト性から有限次元性 | 恒等写像の有限座標を通る因子分解として実装・個別検査済み |

## 公開 API

| module | 内容 |
| --- | --- |
| `Scalars` | 複素積の実部・虚部、\(i\) 倍の実部、\(\lvert\operatorname{Re}z\rvert\le\lvert z\rvert\) |
| `Space[V, space]` | 複素ベクトル空間の実スカラー制限、複素斉次性を持つノルム |
| `Space.Hilbert[norm, inner]` | 既存の Hermitian 内積の実部、ノルムとの整合性、完備性、実 Hilbert 構造 |
| `Space.Hilbert.Riesz` | 有界複素線形汎関数の Riesz ベクトル、表現式、存在、一意性 |
| `Space.Hilbert.FiniteProjection` | 有限集合を固定する有限階数自己随伴射影の構成 |
| `Space.Hilbert.RankOne` | 単位ベクトルによる直交射影、縮小性、有界性、有限階数因子分解 |
| `Space.Hilbert.Estimates` | 平方完成、実部内積の Cauchy–Schwarz 評価 |
| `Space.Operators[W, target, norm, targetNorm]` | 有界複素線形作用素、実有界作用素への変換 |
| `Space.Operators.Continuous` | 有界作用素の連続性 |
| `Space.Operators.Compact` / `Compact.After` / `Compact.Before` / `Compact.Addition` / `Compact.Limit` / `Compact.Approximation` / `Compact.FiniteRank` / `Compact.Adjoint` / `Compact.Identity` | 単位球の像の閉包によるコンパクト性、零値作用素、像の全有界性、和、有界作用素との前後合成、ノルム極限、有限階数近似、随伴、有限次元性 |
| `Space.Operators.Adjoints[inner, targetInner]` | 随伴の構成・複素線形性・有界性・一意性 |
| `Space.Hilbert.Subspaces` | 閉部分空間、位相的閉性からの接続 |
| `Space.Hilbert.Subspaces.In[S].Projection[complete]` | 閉部分空間上の Riesz 表現からの直交射影 |
| `Projection.Complement` / `Complement.Norm` | 直交補、補射影、商ノルム、等長線形同型、最小ノルム代表 |
| `FiniteRank[V, W, source, target]` | 有限自由空間を通る因子分解、和・合成の因子分解 |
| `Examples` | 零 Hilbert 空間、Riesz、恒等作用素の随伴、全空間への射影、商との比較、零作用素と和の有限階数性、コンパクト作用素の和・合成・随伴・ノルム極限、恒等作用素の有限次元性 |

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

## コンパクト性と有限次元性

コンパクト作用素は、閉単位球の像の閉包がコンパクトである有界線形作用素と定義する。
有限ネットを固定する有限階数自己随伴射影を構成し、コンパクト作用素を有限階数作用素で一様近似する。
有限階数作用素のコンパクト性は、有限個の像の生成元を固定するコンパクト射影と前合成から得る。
階数 1 射影のコンパクト性は、像を二つのコンパクトな実線分の和に含めて証明する。
随伴は有限階数射影近似とノルム極限からコンパクトになる。

`Compact.Identity.FiniteDimensional` は恒等写像が有限個の複素座標を通って因子分解するという線形 retract であり、恒等作用素のコンパクト性から構成する。

距離空間の `Compactness.TotalBounded` と `Compactness.RelativelyCompact` は有限ネットと相対コンパクト性を扱う。
`functional_analysis.Metric.Geometry.TotalBoundedCompact` は、完備空間において全有界集合の閉包がコンパクトであることを証明する。

## 検査

```sh
cargo build -p cli --locked
mkdir -p work
target/debug/cli libs/analysis/complex_hilbert --module complex_hilbert --full-check-local --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/a19-target-final.json
target/debug/cli libs/analysis/complex_hilbert --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/a19-dependencies-final.json
```

workspace の `libs/refcache/` を共有する。
対象・依存先・回帰検査の結果は [検査記録](../../../benchmarks/records/complex-hilbert/README.md) を参照。
