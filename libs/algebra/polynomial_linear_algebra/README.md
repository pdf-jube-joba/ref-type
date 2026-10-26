# 多項式と線形写像の因子分解

`Field[K := K, field := field]` は任意の体上の多項式、商環、線形写像の核の分解を扱う。
多項式の型は [algebra.Polynomial.Over](../basic/README.md) の自由可換環による `Carrier` そのものである。
係数列の演算・モニック化・モニック除法は既存の `galois.Field.Over.Polynomial.Raw` を再利用する。
データと法則を分けた refinement により、商・Bézout 係数・分解・線形写像を証明付きの値として渡せる。

## 除法と互除法

| API | 内容 |
| --- | --- |
| `Euclid.divide` | 昇順の係数列と非零な除数から商・余りの存在を証明する。 |
| `DivisionResult` | 商、余り、非零の最高次係数とモニック化した除数、余りの次数境界、除法の等式。 |
| `Euclid.exists` | 余りの係数列の長さについて強い帰納法を使う拡張互除法。 |
| `Gcd` / `Bezout` / `Divides` | 公約多項式、その二つの整除証明、Bézout 係数と等式。 |
| `Euclid.greatest` | 任意の公約多項式が構成した公約多項式を割ることを証明する。 |
| `Representatives.exists` | すべての抽象多項式に有限係数列の表示があることを証明する。 |
| `Representatives.gcdExists` / `divisionExists` | 抽象多項式を入力に取る互除法・除法。 |

係数列は末尾の零を許す。
`DivisionResult.normal` は除数を \(c\,m(X)\) と表示し、\(c\ne0\)、\(m\) は係数列の末尾に最高次係数 \(1\) を付けたモニック多項式である。
`degreeBound` は余りの係数列の長さが \(\deg m\) 以下であること、`bound` はその長さが入力の除数の係数列より短いことを表す。
後者を互除法の停止証明に使う。
公約多項式は単元倍を固定せず、最大性と Bézout 等式を公開する。
零多項式の組も扱い、除法の非零条件は命題内で量化する。

## 商環と中国剰余定理

`Principal[d := d]` は主イデアル \((d)\) による商環を作る。
加群の商の同値関係と加法を `module_theory` から再利用し、積との整合性を証明して `algebra.Quotient.Rings` で商環を構成する。
`projection` は環準同型で、`classEqual` / `equalDivisible` と `classZero` / `zeroDivisible` は商での等式と整除を両方向に結び付ける。

`Coprime p q` は \(up+vq=1\) を満たす Bézout 係数の存在である。
`Chinese[p := p, q := q]` の `forwardMap` は

\[
K[X]/(pq)\longrightarrow K[X]/(p)\times K[X]/(q)
\]

という環準同型である。
`intersection` は \((p)\cap(q)=(pq)\) の整除方向を、`injective` は比較写像の単射性を証明する。
`Of[b := b]` は逆写像と両側逆写像の等式を構成する。
`Of.explicit` は剰余類 \(([a],[c])\) の逆像が \([vqa+upc]\) であることを示す。
逆像は一意で、代表元の選択から独立である。

## 多項式の作用と核の分解

`Evaluation` は可換な係数環から、中心的な係数写像を持つ任意の結合環への一変数多項式の代入を構成する。
式の像同士が可換であることを帰納的に証明して、既存の自由可換環の商に降ろす。
`Field.Action[V := V, space := space].At[T := T]` は既存の `lie_algebras.Field.Endomorphisms` の結合代数へ代入し、`evaluate`、`apply` と多項式環上の加群 `module` を公開する。

`Primary[V := V, space := module]` は多項式環上の任意の加群に適用できる。
\(up+vq=1\) に対し、`projection p q b` は \(vq\) の作用、`complementary` は \(up\) の作用である。
`decompose` は \(\ker(pq)\) の元を二つの核の元に分解する。
`At[p := p, q := q, b := b].isomorphism` は

\[
\ker(pq)\cong\ker p\oplus\ker q
\]

を多項式加群の線形同型として与える。
`onKernel` / `onOtherKernel`、`uniqueLeft` / `uniqueRight`、`idempotent`、`independent` は射影の像・消失・一意性・冪等性・Bézout 係数からの独立性を証明する。
`invariant` は各核が任意の多項式の作用、特に \(X\) の作用で不変であることを示す。

## 特性多項式と Cayley–Hamilton

`At[n := n]` の行列の添字は行、列の順で、`characteristic A` は多項式環上の行列式 \(\det(XI-A)\) である。
`cayleyHamilton` はこの多項式を `matrix_invariants.Ring.At.linear A` に代入すると零写像になることを、任意の行列とベクトルについて証明する。
`MatrixModule.determinantTrick` は任意の多項式加群における随伴行列の作用を扱う。
その恒等式を標準基底に適用し、有限和による復元から Cayley–Hamilton を導く。
行列式と随伴行列の証明は [matrix_invariants](../matrix_invariants/README.md) を再利用し、零次元も含む。

`Finite[n := n, V := V, space := space].On[b := b, T := T]` は既存の有限基底を入力に取り、座標表示の特性多項式と抽象線形写像の Cayley–Hamilton を構成する。
`Factorization` は多項式の互いに素な二因子への分解を証明付きで表す。
`At.On[A := A].Splitting[factors := factors]` は特性多項式の因子分解から `split`、線形な `projection`、`idempotent`、`inKernel`、`unique`、`invariant` を構成する。

## 自然性と係数変更

`Change[L := L, target := target, f := f]` は係数の環準同型 \(f:K\to L\) を多項式環へ延長する。
定数・変数・和・積・符号反転との整合性と、Bézout 等式・互いに素な因子の保存を公開する。
`Intertwining` は加法・スカラー倍を保ち、二つの線形写像を絡める半線形写像を扱う。
`naturality` は多項式の生成元についての帰納法で代入との可換性を証明し、`projectionNatural` はそこから核への射影との可換性を導く。
恒等な係数変更は `IdentityChange.mapIdentity` で比較できる。

## 利用例と検査

[Field/Examples.ref](src/Field/Examples.ref) は任意の体上の二座標空間に \(T(a,b)=(0,b)\) を取り、\(X\) と \(1-X\) に対応する射影が \((a,b)\mapsto(a,0)\) であることを計算する。
同じ因子での除法・互除法・中国剰余定理の逆写像も利用する。
[Examples.ref](src/Examples.ref) は実数から複素数への係数変更と射影の可換性、零次元の特性多項式、非零な二次元冪零行列への Cayley–Hamilton の適用を検査する。

```sh
cargo build -p cli --locked
target/debug/cli libs/algebra/polynomial_linear_algebra --memory-mib 8192 --cache-stats
```

workspace の共有キャッシュを使って対象と全依存を検査する。

対象と全依存の通常検査は1,469 module 中972 module を検査し、497 module を共有キャッシュから再利用して成功した。
12,109 ソース検査ステップ、最大 RSS 約972 MiB、worker 復旧・重複検査・失われたステップはすべて0であった。
既存 `galois` の初回一括展開で `definition local context is outside reference scope` が発生したため、`galois` 全体を個別に検証してから依存キャッシュを復元した。
処理系の変更は含まない。
対象の `--full-check-local` も415ステップの再検査と1,399 module の依存キャッシュ再利用で成功し、その後の無変更検査でも合格を確認した。
