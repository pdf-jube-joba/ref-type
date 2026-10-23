# 複素多項式の根と因数分解

パッケージ名は `fundamental_algebra`、公開入口は `Complex`。
L02 の [polynomial_linear_algebra](../polynomial_linear_algebra/README.md) と [galois](../galois/README.md) の多項式環・係数列・正規化・次数帰納法を使い、構成済みの複素数体について代数学の基本定理を証明する。

## 一般の多項式

多項式の台集合は `algebra.Polynomial.Over` を `complex.Complex.Algebra.field` の可換環に適用したもの。
評価は既存の `galois.Field.Over.Polynomial.AbstractEvaluation.apply` を使う。

| API | 内容 |
| --- | --- |
| `Complex.General.Nonconstant` | どの定数多項式とも等しくないこと。 |
| `General.growth` | 非定数多項式と任意の実数 \(M\) に対し、正の半径 \(r\) と \(\lvert z\rvert\ge r\Rightarrow\lvert p(z)\rvert>M\) を与える。 |
| `General.Growth[p, form]` | 正規形から得る具体的な半径と、その正値性・無限遠での評価。 |
| `General.minimum` | 零多項式・定数を含む任意の多項式の絶対値が大域的最小値を取る。 |
| `General.root` | 任意の非定数複素多項式の根が存在する。 |
| `Complex.Roots.exists` | 正次数のモニック係数列の根が存在する。 |
| `Roots.minimumRoot` | 正次数のモニック多項式の絶対値の最小点では、値が零になる。 |
| `Roots.closed` | 複素数体全体の `AlgebraicallyClosed`。 |

`Complex.Normalization.exists` は任意の非零多項式を、非零の先頭係数とモニック係数列へ変換する。
係数列は既存 API と同じ昇順で、モニック形式では先頭の \(1\) を省略する。
例えば \(X^2+1\) は `[one, zero]` である。

## 重複度と順序によらない表示

| API | 内容 |
| --- | --- |
| `Complex.Factorization.monic` | 次数帰納法によるモニック多項式の完全分解、根リストの長さと次数の一致。 |
| `Factorization.exists` | 非零多項式を \(c\prod_i(X-a_i)\)、\(c\ne0\)、に分解する。 |
| `Factorization.Uniqueness.result` | 二つの分解の先頭係数が等しく、根リストは並べ替えで一致する。 |
| `Factorization.Families.Permutation` | 根を一つずつ取り除いて照合する有限リストの並べ替え関係。 |
| `Families.unique` / `independent` | 根の積の等しさと並べ替え関係の両方向。 |
| `Families.Quotient.Family` / `family` | 並べ替えで割った有限根族と、リストからの写像。 |
| `Families.Quotient.product` / `productOf` | 代表元によらない因子積と、リストでの計算則。 |
| `Families.Quotient.injective` | 因子積から有限根族が一意に決まる。 |
| `Factorization.Unordered.exists` / `unique` | 非零多項式の先頭係数と有限根族による表示の存在・一意性。 |

根リストは同じ根の出現をすべて保持する。
並べ替え関係は同じ根を一個ずつ除去するため、根の重複度も一意性に含まれる。
零多項式は一般の最小値定理で扱い、非零な先頭係数を要求する因数分解定理の対象からは除く。
`Complex.Naturality` は体の自己同型による根の移送、根族から得る係数と因数分解の可換性を既存の `RootProduct.natural` と接続する。

## 証明の構成

`Bounds` は Horner 評価と逆三角不等式から、係数の絶対値和に基づく増大評価を証明する。
`Minimum` は閉区間の積のコンパクト性と連続関数の最小値定理を使い、十分大きい正方形上の最小値を大域的最小値へ拡張する。
`Difference` と `FirstTerm` は \(p(a+X)-p(a)=X^n h(X)\)、\(n>0\)、\(h(0)\ne0\)、を構成する。
`UnitRoots` と `Directions` は単位円の平方根と指数の偶奇による帰納法から、最低次項を減少させる方向を作る。
`Variation.Decrease` は二乗ノルムの恒等式と連続性を使い、任意に小さい正の移動量で値を減らす。
これが非零な最小値と矛盾することから根の存在を得る。
分解には既存の `Splitting.splitsOverClosed` の次数帰納法を再利用し、一意性は一次因子の消去と根の除去による帰納法で証明する。
新たな公理や処理系の変更は含まない。

## 利用例と検査

[Complex/Examples.ref](src/Complex/Examples.ref) で、\(X^2+1\) の根の存在と完全分解、二根の交換による有限根族の一致、二重根と単根の有限根族が異なることを検査する。
非モニックな \(i(X^2+1)\) の分解と順序によらない表示、零・定数多項式への最小値定理の適用も含む。
公開 API は [Complex.ref](src/Complex.ref) の子 module から import できる。

```sh
cargo build -p cli --locked
target/debug/cli libs/algebra/fundamental_algebra --memory-mib 8192 --cache-stats
target/debug/cli libs/algebra/fundamental_algebra --full-check-local --memory-mib 8192 --cache-stats
```

workspace の共有キャッシュを使い、対象・全依存と利用例を検査する。

対象の `--full-check-local` は32 module・399ソース検査ステップを再検査し、依存1,424 module の検証済みキャッシュを再利用して成功した。
最大 RSS は約1,120 MiB、worker は1、復旧・重複・失われたステップはすべて0であった。
無変更の通常検査は全1,456 module をキャッシュから再利用し、ソース再検査0ステップで成功した。
workspace からの `--module fundamental_algebra` による登録・依存閉包の検査と、既存 `polynomial_linear_algebra` の全1,424 module のキャッシュ回帰検査も成功した。

固定次数の有限対称積と係数空間の同相、分離領域の根数と因子の連続性は [complex_polynomial_roots](../complex_polynomial_roots/README.md) を参照。
