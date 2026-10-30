# Fredholm 作用素と指数

複素 Hilbert 空間の有界線形作用素について、Atkinson の定理と整数指数の四つの法則を実装する。
核は線形写像の核、像は実際の線形像、余核は像による商空間である。
有限次元性は恒等写像が有限個の複素座標を経由して因子分解することで定義し、そこから実際の基底を構成する。
追加公理は使わず、既存の関数の外延性を利用する。

## 公開 API

以下の `At` は `Space[V, space, norm].Operators[W, target, targetNorm].At[f]`、`H` はその `Hilbert[inner, targetInner]` を表す。

| API | 内容 |
| --- | --- |
| `Operators.After` / `Ideal` | コンパクト作用素の左右イデアル性、コンパクト差による同値関係と合成の整合性 |
| `At.kernel` / `image` / `CokernelSpace` | 実際の核、像、商余核。`kernelClosed` と `ClosedRange` も公開する |
| `At.Parametrix` / `HasParametrix` | 左右の誤差がコンパクトな逆作用素候補と、その存在 |
| `H.Fredholm` | 閉像と有限次元の核・余核 |
| `H.atkinsonEquivalence` / `fredholmOfParametrix` / `atkinson` | parametrix から Fredholm 性を導く |
| `H.parametrixExists` / `FromFredholm` | Fredholm 作用素から有限階数の左右誤差を持つ有界 parametrix を構成する |
| `At.Index.Decomposition` | 実際の核・商余核の基底を保持する |
| `At.Index.fromDecomposition` / `independent` | 基底から整数の次元差を計算し、基底からの独立性を示す |
| `H.index` / `indexFromDecomposition` | Fredholm 性から得る標準の指数と、与えた分解での計算式 |
| `At.Composition.Hilbert.fredholm` / `indexComposition` | 合成の Fredholm 性と \(\operatorname{ind}(gf)=\operatorname{ind}f+\operatorname{ind}g\) |
| `H.DirectSum.At.fredholm` / `indexDirectSum` | 構成した Hilbert 直和上の作用素と指数の直和則 |
| `H.Change.fredholm` / `H.CompactPerturbation.indexInvariant` | コンパクト摂動に対する Fredholm 性と指数の不変性 |
| `H.indexLocallyConstant` | 正の作用素ノルム近傍を構成し、その中で Fredholm 性と指数が一定になることを示す |
| `Operators.Hilbert.Family.At.locallyConstant` | 任意の位相空間をパラメータとするノルム連続族の局所定数性 |
| `FiniteSpace` | 有限次元空間の基底、次元の一意性、部分空間、同型による移送、有限次元空間を経由する写像 |
| `Sum` / `Sum.MapsTo` | Hilbert 直和の内積・ノルム・完備性、座標射影・包含、有界な直和写像 |
| `Space.Hilbert.Trace` | 有限階数トレース、因子分解からの独立性、加法性、スカラー倍、巡回性 |

`H.FiniteParametrix` と `H.defectIndex` は、有限階数の左右誤差からトレースの差を取る補助 API である。
`H.Compare.independent` と `H.Defect.calculate` により、parametrix の選択から独立で、実際の核・余核の整数の次元差に一致する。

## 最小利用例

[Examples.ref](src/Examples.ref) は零 Hilbert 空間上の恒等作用素で、Atkinson の両方向、実際の核・余核の基底、指数の計算、合成則、直和則、コンパクト摂動不変性、ノルム近傍と連続族の定理を適用する。
基底を与えた指数の計算は次の形で使う。

```ref
\definition decomposition: Index.Decomposition := Index.Decomposition {
  kernelFrame := K.Zero[].frame (\fun (x: Identity.KernelSpace) => Z.isZero x),
  cokernelFrame := Q.Zero[].frame quotientTrivial,
};
\definition indexZero: Fredholm.index fredholm = Integers.zeroInteger :=
  Fredholm.indexFromDecomposition fredholm decomposition;
```

一般の有限次元分解では `FiniteSpace.Frame` に基底を渡す。
`fromDecomposition` は \(\dim\ker f-\dim(W/\operatorname{im}f)\) を `std.Arithmetic.Int.Integer` として返す。

## 証明の構成

`FromFredholm` は核の直交補から閉像への制限を全単射とし、有界逆写像定理と像への直交射影から parametrix を構成する。
左右の誤差は核と余核を経由するため有限階数になる。
逆方向は右誤差の有限階数近似と Neumann 逆作用素で閉像を示し、コンパクトな左右誤差を核と閉像の直交補へ制限して有限次元性を得る。
余核への移送は、商に恒等作用素を誘導するコンパクト作用素を扱う独立した `CompactQuotient` 補題に分けている。

指数の法則は有限階数トレースの巡回性と核・余核の基底での計算式から得る。
ノルム近傍では Neumann 逆作用素で有限階数 parametrix を補正する。
コンパクト摂動は有限階数近似とその近傍の定理に帰着する。
`Limits.Near` は単位球全体での一様なノルム差であり、`Family.NormContinuous` はその正の半径ごとに開近傍を要求する。
直和には内積から平方根でノルムを構成し、成分ごとの Cauchy 列から完備性を示す。

## 検査

```sh
source /workspace/ref-type-env.sh
cargo build -p cli --release --locked
target/release/cli libs/analysis/fredholm_operators --module fredholm_operators --full-check-local --diagnostics compact --cache-stats --time-limit-seconds 300 --report-json work/a11-target.json
python3 scripts/check_all.py
```

結果と再現条件は [検査記録](../../../benchmarks/records/fredholm-operators/README.md) に記録する。
