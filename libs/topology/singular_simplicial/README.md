# 有限順序付き単体複体

`Complex[d].Object` は頂点集合 \(\{0,\ldots,d\}\) の部分集合からなる面族で、部分集合について閉じている。
`Complex[d].On[K].Simplex n` は面を張る狭義単調な \((n+1)\) 頂点列である。
`Finiteness[n]` は各次数の単体の有限性と \(n>d\) での消滅を示す。

`Realization` は面のアフィン包の合併を標準単体の部分空間として構成する。
`Chains.comparison` は各向き付き単体をそのアフィン特異単体へ送り、面の公式から鎖写像になる。
`Chains.integerComparison` は同じ写像を整数次数で公開する。
`Chains.With` は任意の整数加群係数で余鎖への引き戻しを与える。

`Realization.Stars` は正の重心座標による開被覆を与える。
面に対応する星の共通部分は、その面の重心への線形ホモトピーで可縮になる。
`Cech` は順序付きの被覆添字と共通部分内の特異単体から二重複体を作る。
縦方向はこの可縮性で、横方向は最小の被覆頂点を付け加える作用素で解消する。
二つの増大写像と、特異単体を含む面の単体的な担体を保つホモトピーから、アフィン比較を同定する。

`Chains.HomotopyEquivalence.existence` と `integerExistence` は、前向き写像が実際のアフィン比較である鎖ホモトピー同値の存在を示す。
`quasiIsomorphism` と `At[z].isomorphism` は整数次数のホモロジー比較を公開する。
`Chains.With[coefficients].Comparison.At[n].isomorphism` の前向き写像は、余鎖の制限が誘導するコホモロジー写像である。

`Coordinates.Indexing` は各次数の単体を有限順序集合で列挙するデータであり、`indexingExistence` がその存在を示す。
`Coordinates.With[indexing].Bounded.model` は境界行列を持つ有界有限自由複体である。
`Comparison.equivalenceExists` はこの行列模型から実際の特異鎖複体への比較を与える。

`Cup[R, ring].Product[p, q]` は前半と後半の頂点列による Alexander–Whitney 積を定義する。
`Compatibility.law` はアフィン比較による特異余鎖の制限がこの積を厳密に保つことを示す。

`Complex[d].LineGraph[V, E]` は、頂点ラベルと重複のない順序付き辺対から一次元の複体を構成する。
`With[graph].Chains.Zero` と `One` は、頂点・辺上の自由加群から実際の単体鎖群への同型を与える。
`Higher[n].vanishes` は二次以上の鎖群の消滅を、`Boundary.law` は境界が終点から始点を引く接続行列であることを示す。
