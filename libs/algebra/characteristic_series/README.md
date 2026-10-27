# 対称多項式と特性級数

有理数上の対称多項式、有限精度の形式的冪級数、Chern 指標と Todd・L・A-hat の乗法列を構成する。
依存先は `std` と `algebra` である。

## 公開 API

| module | 内容 |
| --- | --- |
| `Rational` | 既存の有理数の商から構成した可換環、正整数の逆数、非零有理数の逆数 |
| `Polynomials[n]` | \(n\) 個の形式変数を持つ有理係数多項式、置換不変な多項式の型、基本対称式、評価、和・積・負号・定数 |
| `Symmetric[R, ring]` | 根の列からの基本対称式と置換不変性、係数変更との自然性 |
| `Symmetric.Newton.PowerSums` | 通常の冪和と、任意の根数・任意次数での Newton 恒等式 |
| `Series[R, ring]` | 有限係数列の切断、和・積・スカラー倍・負号・冪、単位級数の逆、零定数項の級数への合成 |
| `Series.Finite` | 既存の `algebra.Polynomial.Over.Finite` の係数演算と切断演算の一致 |
| `FormalSeries` | 任意の非零定数項を持つ有理係数級数の逆、積の法則、切断整合性 |
| `Exponential` | 階乗の逆数による形式的指数と切断整合性 |
| `Characteristic` | Chern・Todd・L・A-hat の生成級数、精度変更との整合性、次数8までの係数表 |
| `Genus[R, ring, coefficient]` | 根ごとの因子の有限多項式、乗法列、Chern 指標の加法列、置換不変性、有限係数表現と切断 |
| `Genus.DegreeEight` | 基本対称式によるコホモロジー次数8までの普遍公式 |
| `Examples` | 対称多項式、空の根族、二つの線の Todd 多項式、幾何級数の逆、精度変更の利用例 |

`Polynomials[n].SymmetricPolynomial` は有理数上の評価が根の置換に不変な多項式の部分型である。
基本対称式は根の列について再帰的に構成し、隣接交換と列への付加から生成した置換について不変性を証明する。
`Symmetric.Change.elementaryNatural` が形式多項式と評価後の基本対称式を結ぶ。

Newton 恒等式は \(p_k=\sum_i x_i^k\)、\(e_0=1\) として
\[
\sum_{i=0}^{n}(-1)^i e_{n-i}p_{i+1}=(n+1)e_{n+1}
\]
を証明する。
証明は \(E(t)=\prod_i(1+x_i t)\) の係数列と \(\sum_i x_i/(1+x_i t)\) の畳み込みを使い、根の追加について帰納する。

## 精度と演算

`Series.cut n p` は次数 \(0,\ldots,n-1\) の \(n\) 個の係数を保持し、不足する係数を0で補う。
`extend n m` は精度 \(n+m\) を表す。
`cutPlus`・`cutScale`・`cutTimes` と `Laws.cutInverseUnit`・`Laws.cutCompose`、`FormalSeries.cutInverse`、`Exponential.cutExp` が精度を下げる計算との整合性を与える。
`trimPlus`・`trimScale`・`trimTimes` と `sameInverse`・`sameCompose` は、入力の不要な高次係数に結果が依存しないことを示す。

`Series.inverseUnit n u` は \(1+t u(t)\) の逆である。
`FormalSeries.inverse n a u` は \(a+t u(t)\) の逆で、`a` は非零有理数の部分型である。
両者について元の級数との積が1になることを証明する。
`Series.compose n p u` と `Exponential.exp n u` は、それぞれ \(p(tu(t))\) と \(\exp(tu(t))\) の切断である。

`Genus.product` と `Genus.sum` は既存の抽象多項式環の元を返す。
`productRepresentation`・`sumRepresentation` が有限係数列による表現を与え、`finiteBridge`・`finiteSumBridge` が切断級数での計算と一致させる。
`multiplicative` は根の列の連結に対する積の法則、`additive` は Chern 指標の和の法則である。

## 次数4・8の計算

Chern 根 \(x_i\) のコホモロジー次数を2、\(c_j=e_j(x_i)\)、\(p_j=e_j(x_i^2)\) とする。
`Characteristic.Tables` は \(t^4\) までの次の係数表を検査する。

| 級数 | \(t^0\) | \(t^1\) | \(t^2\) | \(t^3\) | \(t^4\) |
| --- | --- | --- | --- | --- | --- |
| \(e^t\) | 1 | 1 | \(1/2\) | \(1/6\) | \(1/24\) |
| \(t/(1-e^{-t})\) | 1 | \(1/2\) | \(1/12\) | 0 | \(-1/720\) |
| \(t/\tanh t\) | 1 | 0 | \(1/3\) | 0 | \(-1/45\) |
| \((t/2)/\sinh(t/2)\) | 1 | 0 | \(-1/24\) | 0 | \(7/5760\) |

生成級数は任意精度で構成する。
Todd は \((1-e^{-t})/t\) の単位逆、L は \(\cosh t\) と \(\sinh(t)/t\) の単位逆の積、A-hat は \(\sinh(t/2)/(t/2)\) の単位逆である。

`Genus.DegreeEight` の `*Finite` は、有限多項式の係数を次の普遍公式で計算する。
\[
\begin{aligned}
\operatorname{ch}&=r+c_1+\frac{c_1^2-2c_2}{2}
 +\frac{c_1^3-3c_1c_2+3c_3}{6}
 +\frac{c_1^4-4c_1^2c_2+2c_2^2+4c_1c_3-4c_4}{24},\\
\operatorname{Td}&=1+\frac{c_1}{2}+\frac{c_1^2+c_2}{12}
 +\frac{c_1c_2}{24}
 +\frac{-c_1^4+4c_1^2c_2+3c_2^2+c_1c_3-c_4}{720},\\
L&=1+\frac{p_1}{3}+\frac{7p_2-p_1^2}{45},\\
\widehat A&=1-\frac{p_1}{24}+\frac{7p_1^2-4p_2}{5760}.
\end{aligned}
\]
これらの等式は次数8で切った等式である。
根の数について帰納し、次数ごとの根追加の等式を可換環の法則と有理数の具体的計算で証明する。

## 証明の生成と検査

`tools/generate.py` は係数表と普遍公式の等式証明を生成する。
生成した `.ref` は通常の検査対象であり、Python の計算結果を公理や判定規則として取り込まない。
有理数の計算は既存の商 API、同分母加算、分数の拡大を通して検査し、大きい交差積の直接簡約を避ける。
環の計算は結合・交換・分配・逆元の法則から成る明示的な等式証明である。

リポジトリのルートから実行する。

```sh
python3 libs/algebra/characteristic_series/tools/generate.py
cargo build -p cli --locked
mkdir -p work
./target/debug/cli libs/algebra/characteristic_series --module characteristic_series --full-check-local --cache-stats --report-json work/l04-target.json
./target/debug/cli libs/algebra/characteristic_series --cache-stats --report-json work/l04-dependencies.json
```

キャッシュは workspace 共通の `libs/refcache/` を利用する。
精度の表記と再開・資源制限の詳細は [CLI の利用方法](../../../src/USAGE.md#検査とキャッシュ) を参照。
