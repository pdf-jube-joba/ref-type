# 整数次数のテンソル鎖複体

`tensor_chains.TensorChain` は、可換環上の整数次数鎖複体のテンソル total と外積を構成する。
一般の二重複体の total には、各整数対角上の有限台直和を使う。

- `Grading` は標準整数加法、対角 `Index n`、次数を下げる写像、`complement n p` とその次数恒等式を公開する。
- `BoundedDiagonal.At[n, leftBound, rightBound]` は両因子の次数 bound を保持する有限対角を構成し、`finite` と `includes` で有限性と包含を証明する。
- `Over[R, ring].Tensor[C, D]` はテンソル二重複体を構成する。
- `Total[C].complex` は微分 \(d_h+(-1)^p d_v\) とその二乗零の証明を持つ。
- `Tensor[C, D].TotalTerm[p, q].differential` は純テンソルに対する微分公式を公開する。
- `Exterior[C, D, p, q].map` は \(H_p(C)\otimes H_q(D)\to H_{p+q}(C\otimes D)\) であり、`onClass` はサイクルの代表元上の式である。
- `ExteriorTransport[C, D, p, q].onClass` は、次数の等式に沿って移送した外積の類と、指定した対角の類を比較する。
- `CycleProductNaturality[C, D, E, F, p, q].With[f, g].Exterior.naturality` は両因子の複体写像による外積の自然性を示す。
- `Map`、`End`、`TensorMapping`、`TensorIdentity`、`TensorComposition` は total の誘導写像と恒等・合成の法則を扱う。
- `TensorSquare[A, B, C, D, E, F].With[a0, a1, b0, b1, g]` は左因子の四角形と右因子の鎖写像をテンソル total の四角形に移す。
  `Commutes` は左因子での二つの合成の一致であり、`square` はその証明から total の全次数・全元での一致を返す。
- `Row[E, p].complex` は次数 \(n\) の項を \(E_{n-p}\)、微分を \((-1)^p d_E\) とする整数移動である。
  `Row[E, p].Homology[n].isomorphism` は \(H_{n-p}(E)\cong H_n(\mathrm{Row}_p(E))\) を、`onClass` は代表元上の式を公開する。

外積の構成では左右の境界が零になることを示してから、サイクルのテンソル積からホモロジーのテンソル積へ降下させる。
整数次数の移動では `Chain.Prior` の型移送も比較し、サイクルと境界の同型からホモロジー比較を得る。

```sh
cargo run -p cli -- libs/algebra/homological/tensor_chains --module tensor_chains.TensorChain
```
