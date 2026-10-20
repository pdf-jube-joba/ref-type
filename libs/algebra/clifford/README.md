# クリフォード代数とクリフォード群

`Field[K, field].On[V, space].Of[form]` は双線形形式から \(q(v)=\operatorname{form}(v,v)\) を取り、クリフォード代数を構成する。
係数環上の非可換な自由結合環を、生成ベクトルの線形性と \(\iota(v)^2=q(v)1\) の関係で割る。

| module / 宣言 | 内容 |
| --- | --- |
| `Of.Carrier` / `Of.algebra` | 商の台集合と結合代数構造 |
| `Of.iota` / `Of.injection` | 生成ベクトルの標準写像とその線形性 |
| `Of.cliffordRelation` | \(\iota(v)^2=q(v)1\) |
| `Of.Universal` | 中心的な係数写像と線形な生成元の像から得る一意な準同型 |
| `Of.commutatorLieAlgebra` | 交換子リー代数 |
| `Of.Pin` | Pin・Spin と複素拡張、その群構造 |
| `Circle` | \(z\overline z=1\) を満たす複素数の群 \(U(1)\) |
| `ComplexExtension.By` | 中心的な位数 \(2\) の元を使う \((G\times U(1))/\langle(-1,-1)\rangle\) |

`Of.injection` は標準写像の線形写像としての名前で、単射性の証明は公開していない。
普遍性は商の構成から証明する。

Pin は \(q(v)=1\) または \(q(v)=-1\) のベクトルに対応する可逆元と、スカラー \(-1\) から生成する。
Spin は単位ベクトルの偶数個の積と \(-1\) から生成する。
スカラーの符号を明示的に含めることで、零次元でも \(\{\pm1\}\) を含む規約にする。
`Pin.inclusion` は Spin から Pin への包含である。
`PinC` と `SpinC` は直積を対角の符号で割った商で、積・逆元が代表元によらないことを証明している。

`geometry/lie_groups` の `Euclidean[n]` は標準内積を渡す。
この具体化は \(v^2=\|v\|^2\) の規約を使うため、`Pin` は \(\mathrm{Pin}^{+}(n)\) である。
負の形式を渡すと \(v^2=-\|v\|^2\) の規約になる。

ここで構成する `group` は群構造である。
有限次元の場合のアトラス、直交群への被覆写像、これらのリー群構造は、このパッケージでは構成していない。

```sh
cargo run -p cli -- libs/algebra/clifford --module clifford
```
