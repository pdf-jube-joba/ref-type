# Fredholm 作用素と指数

A11 は特殊化時の型エラーでブロックされており、完了していない。
汎用の証明を検査できる範囲と、具体的な作用素への適用の失敗を区別する。

## 実装した内容

| API | 内容 |
| --- | --- |
| `Space.Operators` | 有界複素線形作用素の和・負・差・零・外延性 |
| `Space.Operators.After` | 合成、コンパクト作用素の左右イデアル性、コンパクト差に関する合成の整合性 |
| `Space.Operators.Ideal` | コンパクト差による同値関係、コンパクト摂動による同値性 |
| `Space.Operators.At` | 実際の線形核・像・商としての余核、核の閉性、左右の誤差と parametrix |
| `At.Perturbation` / `At.Composition` | コンパクト差に関する parametrix の移送と合成 |
| `FiniteSpace` | 恒等写像の有限階数因子分解から基底を構成し、基底によらない次元を得る |
| `FiniteSpace.Subspace` / `Through` | 有限次元部分空間、有限次元空間を経由する写像の有限階数性 |
| `Space.Hilbert.FiniteSubspace` | 有限次元部分空間への射影と閉性 |
| `Space.Hilbert.FixedSubspace` | コンパクト写像に固定される閉部分空間の有限次元性 |
| `Space.NearIdentity` / `At.Inverse` | 半縮小写像からの逆写像と有界逆写像定理 |
| `At.Hilbert` | 閉像と有限次元の核・余核による Fredholm 性、parametrix からの構成と逆方向 |
| `At.Index` | 核・余核の実際の基底から整数指数を計算し、基底からの独立性を証明する API |
| `Space.Hilbert.Trace` | 有限階数トレース、因子分解からの独立性、加法性、スカラー倍、巡回性 |

`FiniteSpace.FiniteDimensional` は恒等写像が有限個の複素座標を経由して因子分解することを表す。
`frameExists` は座標空間上の冪等写像の像の基底から元の空間の基底を構成する。
`dimensionIndependent` は既存の複素次元の一意性を使う。

`At.Index.Decomposition` は、与えた作用素の核と商余核の基底を保持する。
`fromDecomposition` は \(\dim\ker T-\dim\operatorname{coker}T\) を `std.Arithmetic.Int.Integer` として返す。
`independent` と `calculate` は証拠の選択からの独立性と計算式を与える。

## Atkinson の証明の構成

`FromFredholm` は核の直交補から閉像への制限を全単射とし、有界逆写像定理と像への直交射影から parametrix を構成する。
左右の誤差は核と余核を経由するため有限階数になる。

`FromParametrix` は右誤差を有限階数作用素で半径 \(1/2\) 未満に近似し、残差を Banach の不動点定理で反転する。
有限階数の右誤差を持つ右 parametrix が得られるので、元の作用素の像を有限次元の閉部分空間の逆像として記述する。
核の有限次元性は左誤差の制限、余核の有限次元性は閉像の直交補への右誤差の射影から得る。
これらの汎用宣言は検査できたが、下記の具体的適用が失敗するため、公開可能な完了実装とはしていない。

## 未完了と阻害要因

`Examples` の零 Hilbert 空間上の恒等作用素に `fredholmOfParametrix` を適用すると、特殊化後の定義本体の検査で、元の `Fredholm(V, space, norm, W, target, targetNorm, f)` が残り、具体的な `Point` と `identity` に対応する結論と変換可能にならない。
独立したキャッシュでも同じ失敗を確認した。
命題の structure を論理積に変更し、型引数を明示し、公開定理を汎用モジュールへ移す回避も試した。
`Space.Operators.Hilbert.atkinson` は最後の移動案である。

指数の合成則・直和則・コンパクト摂動不変性・ノルム連続族での局所定数性は未実装である。
特殊化の失敗を回避して具体的な利用例を完成できるまで、A11 の完了やマージの根拠にはできない。

## 検査

```sh
source /workspace/ref-type-env.sh
cargo build -p cli --release --locked
target/release/cli libs/analysis/fredholm_operators --module fredholm_operators --full-check-local --diagnostics compact --cache-stats --time-limit-seconds 300 --report-json work/a11-target.json
target/release/cli libs/analysis/fredholm_operators --module fredholm_operators.Examples --full-check-local --diagnostics compact --time-limit-seconds 300 --report-json work/a11-examples.json
python3 scripts/check_all.py
```

結果と再現条件は [検査記録](../../../benchmarks/records/fredholm-operators/README.md) に記録する。
