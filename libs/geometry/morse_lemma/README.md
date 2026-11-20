# Morse 補題と慣性指数

Dedekind 実数上の有限次元の対称双線形形式と滑らかな関数を扱う。
零次元も含む。
入口は `morse_lemma` であり、微分と滑らかな写像は `calculus`、局所逆写像とパラメータ付き陰関数は `inverse_implicit` と共有する。

## 双線形形式と慣性指数

`Inertia[n].Form` は既存の `linear_algebra.Commutative.Form.Bilinear` である。
`Symmetric` は引数交換による不変性、`Nondegenerate` は全てのベクトルを消すベクトルが零であることを表す。
`normalFormExists` は任意の非退化対称形式から `NormalForm[h]` を構成する。

`NormalForm` の `sign: Fin n -> Bool` は負の座標を `true` で表す。
`change.forward` は標準座標から元のベクトルへの線形同型であり、`formula` は
\[
h(Cv,Cw)=\sum_i\epsilon_i v_iw_i,\qquad \epsilon_i\in\{-1,1\}
\]
を証明する。
`Normalized[h, normal].formula` は `change.backward` を使った元の座標での公式である。

分解の存在は次元について帰納する。
偏極恒等式から非等方ベクトルを取り、Euclidean 正規化と直交補の枠で第一座標を選ぶ。
その座標に対する shear で交差項を消し、残りの形式の非退化性を証明して帰納を適用する。
各非零対角係数は実数の平方根で正規化する。

`Inertia[n].Index` は負・正の座標数を数える。
負部分空間の射影の trace と Gram–Schmidt による像の枠から、任意の可逆な合同に対して負部分空間の次元を比較する。
逆の合同から反対向きの比較を得て、正規形の選び方によらず両指数が一致することを証明する。

| API | 内容 |
| --- | --- |
| `Index.negative` / `positive` | 符号関数の負・正の座標数 |
| `Index.NonsingularForm` | 対称性と非退化性を満たす形式 |
| `Index.negativeIndex` / `positiveIndex` | 一意性付き選択による数値指数 |
| `Index.negativeIndexOfNormal` / `positiveIndexOfNormal` | 任意の正規形の符号数との一致 |
| `Index.negativeIndexInvariant` / `positiveIndexInvariant` | 一般の可逆な線形合同による不変性 |
| `Index.indexDimension` | 負指数と正指数の和が次元に一致すること |
| `MatrixForm[n]` | 行列の形式への変換、対称性、非零行列式からの非退化性 |
| `MatrixForm.Quadratic` / `Congruence` | 二重和による表示と行列合同の形式への接続 |
| `MatrixForm.HalfCongruence` | 形式を正の定数 \(1/2\) 倍しても指数が変わらないこと |

## 滑らかな形式族

`Normalization[d, n].On[U].At[A, a].localExistence` は滑らかな対称行列族 \(A(x)\) と非特異な \(A(a)\) に対し、開近傍上で
\[
A(x)=C(x)^T A(a)C(x),\qquad C(a)=I
\]
となる滑らかな行列族を構成する。
`localInvertibleExistence` は近傍上での \(C(x)\) の非特異性も保持する。

構成は行列空間を有限次元 Euclidean 空間に符号化し、\(B=A(a)\) として多項式写像
\[
F(H)=2BH+H^TBH
\]
に逆関数定理を適用する。
零での微分は \(H\mapsto2BH\) である。
対称行列 \(A(x)-B\) の局所逆像では反対称部分の比較から \(BH=H^TB\) が従い、\(C=I+H\) が所要の合同を与える。

`IndexFamily[d, n].On[U, A, a].localExistence` はこの合同と慣性指数の不変性から、開近傍上の負・正指数の局所定数性を証明する。
返される `Local` は開集合、包含、基点の所属、各点での分類済み形式、および中心との指数の等式を保持する。

## 関数の局所正規形

`Euclidean[n].Function[U, f]` は滑らかなスカラー関数の勾配と Hessian を構成する。
`Critical x` は全偏導関数の消滅であり、全微分の消滅との同値性も証明する。
`Nondegenerate x` は実際の勾配写像の微分の行列式が非零であることを表す。
`hessianEntriesValue` はこの微分の行列成分と選んだ二階偏導関数の一致を、`hessianSymmetric` は Schwarz の定理による対称性を証明する。

`Hadamard[n, U, f, a].localExistence` は臨界点の近傍上に滑らかな対称係数 \(B_{ij}(x)\) を構成し、
\[
f(x)=f(a)+\sum_{i,j}B_{ij}(x)(x_i-a_i)(x_j-a_j),\qquad B(a)=\tfrac12\operatorname{Hess}_a f
\]
を証明する。
係数は直線 homotopy 上の Hessian の重み付き積分 \(\int_0^1(1-t)\operatorname{Hess}f(a+t(x-a))\,dt\) である。
閉区間上の連続関数の Riemann 積分から、積分下偏微分、全偏導関数の同時連続性、係数の滑らかさを順に証明する。
二次の Taylor 恒等式は微積分の基本定理と積の微分則から導く。

`NormalForm[n, U, f, a].localExistence` の入力は `Critical a` と `Nondegenerate a` である。
得られる `Local` は開近傍 `domain` と零を含む開集合 `target`、元の定義域への包含、滑らかな両側逆 `equivalence`、基点を零へ送る等式、および
\[
f(x)=f(a)+\sum_i\epsilon_i y_i(x)^2
\]
を保持する。
`equivalence.forward` が Morse 座標、`equivalence.backward` が元の近傍へのパラメータ表示である。
`Indices[local].negative` と `positive` は、正規形の負・正の符号数が元の Hessian の指数に一致することを証明する。
Taylor 係数族を局所合同で正規化し、\(x\mapsto C(x)(x-a)\) の基点での可逆な微分からこの微分同相を構成する。

`CriticalPoints[n, U, f].At[a].isolated` は非退化臨界点の孤立性を証明する。
返される近傍の `unique` は、その中の任意の臨界点が基点と等しいことを述べる。
この証明は勾配写像の局所逆を用いる。
`CriticalPoints.index` と `coindex` は Hessian の数値指数、`At[a].locallyConstant` は開近傍上での両指数の局所定数性である。

## パラメータ

`Parametric[p, n].Function[U, f]` は座標を \((p,q)\) に分け、未知変数 \(q\) の方向の勾配と Hessian を使う。
`criticalBranchExists` は非退化臨界点を通る滑らかな臨界点族 \(q=c(p)\) を陰関数定理から構成する。
`CriticalBranch` はグラフの滑らかさ、元の近傍への所属、臨界性、基点での一致、局所一意性を保持する。

`Morse[a].localExistence` はこの臨界点族を構成し、パラメータを保つ局所座標を与える。
新しい座標では
\[
f(p,q)=f(p,c(p))+\sum_i\epsilon_i z_i(p,q)^2
\]
となる。
`FiberHadamard` は滑らかな臨界点族を中心とする Taylor 係数を構成し、`FiberCoordinates` は \(q-c(p)\) の滑らかさと未知変数方向の微分が恒等写像であることを証明する。
`Indices[a].locallyConstant` は未知変数方向の Hessian 族の両指数の局所定数性である。
`Morse[a].Indices[local]` はパラメータ付き正規形の符号数と元の未知変数方向の Hessian の指数を結ぶ。

## 利用例

独立した関数の例は `Examples` にある。
各例は偏導関数と Hessian を計算し、非退化性を明示的な逆行列で証明してから局所定理を適用する。

例えば `morse_lemma`、`calculus`、`std` に依存する package から、非線形例の証明を使って局所座標の存在を得る。

```ref
\module Example {
  \import std.Data[].Nat[] \as N;
  \definition dimension: N.Nat^ := N.Nat^::succ N.Nat^::zero;
  \import calculus.Real[].Multivariable[n := dimension].Open[] \as Open;
  \import morse_lemma.Examples[].Nonlinear[] \as Nonlinear;
  \import morse_lemma.NormalForm[n := dimension, U := Open.whole,
    f := Nonlinear.function, a := Nonlinear.point] \as Morse;
  \definition coordinatesExist: \exists Morse.Local :=
    Morse.localExistence Nonlinear.critical Nonlinear.nondegenerate;
}
```

| 例 | 内容 |
| --- | --- |
| [Examples.Nonlinear](src/Examples/Nonlinear.ref) | \(f(t)=(t+t^2)^2\) の零での正規形と孤立性 |
| [Examples.Saddle](src/Examples/Saddle.ref) | \(f(u,v)=uv\) の非退化な鞍点 |
| [Examples.Parametric](src/Examples/Parametric.ref) | \(f(p,q)=(q-p^2)^2\) の臨界点族 \(q=p^2\) とパラメータ付き正規形 |
| [Examples.ZeroDimension](src/Examples/ZeroDimension.ref) | 零次元の定数関数 |
| [Inertia.Examples](src/Inertia/Examples.ref) | 零次元、負の直線、混合符号平面、shear で引き戻した形式 |
| [Inertia.Index.Examples](src/Inertia/Index/Examples.ref) | 零次元・負の直線・鞍点の指数の数値計算 |

## 検査

```sh
cargo build -p cli --release --locked
target/release/cli libs/geometry/morse_lemma --full-check-local --memory-mib 4096 --cache-stats --time-limit-seconds 1800 --report-json work/g13-target.json
python3 scripts/check_all.py libs --memory-mib 4096 --cache-budget-mib 12288 --min-free-mib 512 --time-limit-seconds 3600 --state-dir work/g13-repository-check
cargo test --workspace --locked -j 4
```

共有キャッシュを使用し、対象の全 module と読み込む依存閉包を検査する。
`--full-check-local` では対象 package の証明を再検査し、依存先の整合するキャッシュを再利用する。
2026-11-19 の対象再検査は、137 module 全てと依存閉包を含む 1,926 module について accepted になった。
全体検査は既存の `euclidean_sobolev/Euclidean/Order/Weight.ref:14` で停止した。
成功・失敗・未到達の範囲は [検査記録](VALIDATION.md) に記す。
