# クリフォード代数とクリフォード群

`Field[K, field].On[V, space].Of[form]` は双線形形式から \(q(v)=\operatorname{form}(v,v)\) を取り、クリフォード代数を構成する。
係数環上の非可換な自由結合環を、生成ベクトルの線形性と \(\iota(v)^2=q(v)1\) の関係で割る。

| module / 宣言 | 内容 |
| --- | --- |
| `Of.Carrier` / `Of.algebra` | 商の台集合と結合代数構造 |
| `Of.iota` / `Of.injection` | 生成ベクトルの標準写像とその線形性 |
| `Of.cliffordRelation` | \(\iota(v)^2=q(v)1\) |
| `Of.Universal` | 中心的な係数写像と線形な生成元の像から得る一意な準同型 |
| `Of.Relations` | 偏極から得る反交換関係、生成ベクトルの三重積 |
| `Of.Grading` | 生成ベクトルを反転する対合的代数自己同型、可逆元への作用、twisted adjoint |
| `Of.commutatorLieAlgebra` | 交換子リー代数 |
| `Of.Pin` | Pin・Spin と複素拡張、その群構造 |
| `Of.Pin.Grading` / `Of.Pin.Reflection` | 対合による Pin の保存と Spin の固定、正負の単位ベクトルの twisted adjoint の反射公式 |
| `Circle` | \(z\overline z=1\) を満たす複素数の群 \(U(1)\) |
| `ComplexExtension.By` | 中心的な位数 \(2\) の元を使う \((G\times U(1))/\langle(-1,-1)\rangle\) |
| `Field.Block` | 係数代数上の Clifford ブロック作用素、その線形性と二乗公式 |
| `Euclidean[n]` / `Euclidean.Successor` | 標準内積の Clifford 代数と、直前の代数の二つのコピーへの作用 |
| `EuclideanFaithfulness.faithful` | 全次元におけるスカラーと生成ベクトルの標準写像の単射性 |

`Of.injection` は標準写像の線形写像としての名前である。
標準内積の場合には `EuclideanFaithfulness.faithful n` がスカラーと生成ベクトルの単射性を与える。
証明は零次元で実数への普遍写像を使い、次元を増やすごとにブロック作用素の定数ベクトルへの作用から係数と生成ベクトルの先頭・残りの座標を復元する。
普遍性は商の構成から証明する。
`Of.Induction` はスカラー・生成ベクトルと代数演算による構造帰納法、`Of.HomExt` は生成元上の一致による準同型の一意性を与える。
`Euclidean.Successor.NormalForm` は \(j(a)+j(b)e_0\) の存在と一意性を証明し、`Spanning.recover` がその再構成を与える。
`EuclideanCoordinates.coordinates` は標準形から実数の係数座標を再帰的に構成し、`injective` はその単射性を証明する。
`NormalForm.Grading` と `NormalForm.Reversion` は二成分による次数自己同型と反自己同型の表示を与える。
`EuclideanCenter.law` は生成ベクトルの twisted centralizer がスカラーに限られることを示す。
`Of.Reversion` はスカラーとベクトルを固定して積の順序を逆にする写像である。
`Euclidean.PinNorm.norm` は Pin 上で reversion が逆元に一致すること、`scalarSign` はスカラー元が \(\pm1\) に限られることを示す。
`Relations.anticommutator` は、標数に関する追加条件を使わずに
\[\iota(u)\iota(v)+\iota(v)\iota(u)=\bigl(\operatorname{form}(u,v)+\operatorname{form}(v,u)\bigr)1\]
を導く。
`Grading.map` は係数を固定し、生成ベクトルを \(-\iota(v)\) に送る自己同型で、`involutive` はその二乗が恒等写像になることを示す。
`Grading.action g x` は \(\alpha(g)xg^{-1}\) であり、群の積と作用の合成が一致する。

Pin は \(q(v)=1\) または \(q(v)=-1\) のベクトルに対応する可逆元と、スカラー \(-1\) から生成する。
`Euclidean.PinWords` は Pin の元の単位ベクトルによる語表示を証明する。
`PinWords.Parity.fixedIff` は、偶数部分が次数自己同型の固定部分に一致することを示す。
Spin は単位ベクトルの偶数個の積と \(-1\) から生成する。
スカラーの符号を明示的に含めることで、零次元でも \(\{\pm1\}\) を含む規約にする。
`Pin.inclusion` は Spin から Pin への包含である。
`PinC` と `SpinC` は直積を対角の符号で割った商で、積・逆元が代表元によらないことを証明している。
`ComplexExtension.By.Lift` はこの商からの写像の普遍性を与える。
`ComplexRepresentation` は Pin に埋め込まれた群の複素拡張を、クリフォード代数の二成分で忠実に表示する。
`Algebra` は積・逆元の多項式による表示、`Phase` は位相成分の二乗を二成分から復元する公式を与える。

`geometry/lie_groups` の `Euclidean[n]` は標準内積を渡す。
この具体化は \(v^2=\|v\|^2\) の規約を使うため、`Pin` は \(\mathrm{Pin}^{+}(n)\) である。
負の形式を渡すと \(v^2=-\|v\|^2\) の規約になる。

ここで構成する `group` は群構造である。
有限次元の場合のアトラス、直交群への被覆写像、これらのリー群構造は、このパッケージでは構成していない。

```sh
cargo run -p cli -- libs/algebra/clifford --module clifford
```
