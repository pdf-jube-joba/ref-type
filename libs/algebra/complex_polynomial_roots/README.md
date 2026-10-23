# 複素多項式の根群と有限対称積

公開入口は `complex_polynomial_roots.Roots`。
[K13](../fundamental_algebra/README.md) の完全分解、重複度を保つ根リストの並べ替え、根から係数を作る `RootProduct` を使う。
次数 \(n\) のモニック多項式の係数空間は、最高次の \(1\) を省いた昇順の係数 \(\mathbf C^n\) に通常の積位相を入れたものである。
零次元は定数多項式 \(1\) と空の根族を表す。

## 係数と根族

`Roots.Vector n` は `Fin n -> Complex`。
`polynomial n p` は係数から作る既存の抽象多項式、`product n a` は \(\prod_i(X-a_i)\) である。

| API | 内容 |
| --- | --- |
| `MonicCoordinates.injective` | 同じ次数の係数が同じ抽象多項式を表せば、すべての係数が等しい。 |
| `MonicCoordinates.rootBound` | 根 \(z\) に対する \(\lvert z\rvert<1+\sum_i\lvert p_i\rvert\)。 |
| `At[n].coefficients` / `factorization` | 根の対称式による係数と、一次因子の積との一致。 |
| `At.onto` | K13 の完全分解から、任意の係数に根の有限列を与える。 |
| `At.Equivalent` / `Family` / `family` | 根の並べ替えによる有限対称積と商写像。 |
| `At.coefficientMap` / `roots` | 根族と係数の両方向の写像、`coefficientsRoots` と `rootsCoefficients` による逆写像の等式。 |
| `At.Unordered.forget` / `injective` / `polynomialOf` | K13 の任意の長さの有限根族への埋め込みと因子積の一致。 |
| `At.Naturality.coefficientNatural` / `rootsNatural` | 体の自己同型による根と係数の移送との可換性。 |

`At[n]` は `Roots.At[n := n]` の略である。
`At.topology` は係数・順序付き根の通常の積位相、`At.symmetricTopology` はその並べ替えによる商位相。
`At.Topological.homeomorphism` は有限対称積と係数空間の同相である。
`continuous`、`coefficientContinuous`、`rootsContinuous` は各写像の連続性を個別に使える。
根の上界によって、係数の十分小さい近傍の逆像を根のコンパクトな箱に収める。
この評価から `closedMap` と `quotientMap` を証明し、係数から根族への逆写像の連続性を導く。

## 分離領域の因子

`Separated[U := U, V := V]` は二つの領域を取り、\(U\) に入る根を重複込みで選ぶ。
`At[n].laws` は \(U,V\) が互いに素な開集合であることから、選択が領域内で局所的に一定になることを証明する。
より一般の Boolean 選択は `Filtering[test := test]` から使える。

```ref
\import complex_polynomial_roots.Roots[] \as R;
\import R.Separated[U := U, V := V] \as Separation;
\import R.Filtering[test := Separation.test].At[n := n].Regions[U := U, V := V] \as Regions;
\import Regions.Cluster[k := k] \as Cluster;
```

`Regions.RootLaws[k, a]` は、中心の根列が \(U\cup V\) に入り、\(U\) 内に重複込みで \(k\) 個の根があるという中心での条件である。
`Regions.contains` と `Regions.open` は、その条件を保つ係数の開近傍 `Domain k` を構成する。
同じ係数を表す根列についての条件の独立性は `Regions.invariant` が保証する。
したがって領域内の根数は局所的に一定であり、重根が複数の根へ分かれても合計の重複度は保存される。

`Cluster.Base` はこの開領域に入る係数の部分空間。
`Cluster.value` は \(U\) 内の根すべての積に等しい次数 \(k\) のモニック因子の係数で、`coefficients` は通常の `Vector k` としての値を返す。
`exists`、`unique`、`onRoots` は実際の根の選択からの構成・順序からの独立性・計算則を与える。
`Cluster.continuous` はこの因子の係数の連続性、`decomposition` は残りの根の因子との積が元の多項式になることを証明する。
複数の離れた根群には、各群と残りの領域の組に適用できる。
`Cluster.Families[X].pullback`、`regular`、`natural` は任意の連続な係数族への適用と底空間の写像との可換性を与える。

## 利用例と検査

[Examples.ref](src/Roots/Examples.ref) は実部の正負の領域で \(1,-1\) を分離し、次数1の連続な因子を構成する。
同じ領域内の二重根 \(1,1\) には次数2の因子を構成し、重複度の違いを実際の根リストで検査する。
任意の二次モニック多項式から順序を持たない根族への連続性と、零次元の同相も含む。

```sh
cargo build -p cli --locked
target/debug/cli libs/algebra/complex_polynomial_roots --memory-mib 8192 --cache-stats
target/debug/cli libs --module complex_polynomial_roots --memory-mib 8192 --cache-stats
```

共有キャッシュを使い、対象の構成・証明・利用例と全依存パッケージを検査する。

対象と全依存の検査は新規27 module・380ソース検査ステップを検査し、依存1,456 module を再利用して成功した。
固定した最終ソースでの workspace 全体の検査も、68 package・6,936 module の検証済みキャッシュを再利用して成功した。
worker は1、復旧・重複・再実行・失われたステップ・キャッシュ保存失敗はすべて0で、最大 RSS は対象約1,114 MiB、workspace 約1,426 MiBであった。
処理系と依存先の証明は変更していない。
