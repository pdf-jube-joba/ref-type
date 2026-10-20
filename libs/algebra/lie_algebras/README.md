# リー代数

`Field[K, field]` は任意の体上のリー代数を扱う。
`LieAlgebra V space` はベクトル空間上の双線形かつ交代的な括弧積で、Jacobi 恒等式を満たすものとして定義する。
Jacobi 恒等式は \([x,[y,z]]=[[x,y],z]+[y,[x,z]]\) の形を使う。

| module | 内容 |
| --- | --- |
| `Field.On` | 反対称性、線形写像 `ad`、導分則、`adRepresentation` |
| `Field.On.Of` | 部分リー代数の誘導されたベクトル空間と括弧積 |
| `Field.Hom` | 括弧積を保つ線形写像 |
| `Field.Abelian` | 零の括弧積 |
| `Field.Associative` | 結合代数の交換子 \([x,y]=xy-yx\)、導分則と Jacobi 恒等式の証明 |
| `Field.Endomorphisms` | 線形自己写像の結合代数と交換子リー代数 |

交代性から反対称性を導くため、標数 \(2\) も含めて定義を使える。
`geometry/lie_groups` の `Classical.On.Orthogonal.LieAlgebra` は、反対称な自己写像が交換子で閉じることを証明し、\(\mathfrak{so}(n)\) を具体化する。

```sh
cargo run -p cli -- libs/algebra/lie_algebras --module lie_algebras
```
