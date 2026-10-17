# 有限 CW 複体と特異鎖

`On[A, source, complex]` は、実際のユークリッド閉球を特性写像の定義域とする有限 CW 複体を扱う。
`complex` の条件には、特性写像の連続性、開胞体上での逆写像の連続性、胞体像の閉性、境界が低次元胞体に入ること、胞体分解を用いた弱位相が含まれる。

- `Filtration.Stage[limit]` は、次元が `limit` 未満の胞体からなる骨格である。
- `Layer[n].sequence` は、隣接する骨格の特異鎖に対する短完全列である。
- `Layer[n].Basis.isomorphism` は、\(n\) 次元胞体を基底とする自由アーベル群と骨格の相対特異ホモロジーを結ぶ。
  基底は閉球と境界の向き、穿孔近傍の変形収縮、切除から構成する。
- `Cellular.complex` の境界は、相対ホモロジーの連結写像と一つ下の相対群への射影の合成である。
- `Cellular.Representatives.selectionExists` は、各胞体の相対基本類について、胞体境界と整合する特異鎖の代表を選ぶ。
  `Selected[selection].integerMap` と `equivalenceExists` が特異鎖との比較を与える。
- `Selected[selection].With[coefficients].At[z].isomorphism` は、任意の係数加群に対するコホモロジーの比較である。
  `Homology[coefficients].At[z].isomorphism` は、比較鎖写像と係数加群のテンソル積からホモロジーを比較する。
- `Selected[selection].Coefficients[input, output, coefficientMap].cochainNaturality` は、係数準同型と比較コチェイン写像が可換であることを示す。
- `Selected[selection].Native[e].Diagonal.map` は、特異鎖の Alexander–Whitney 対角を比較同値で胞体鎖へ移す。
  `Diagonal.Cup[R, ring, p, q].realizes` と `agreement` は、この対角による積と特異コホモロジーの積の一致を与える。
- `Naturality[B, target, targetCW].Chosen[sourceSelection, targetSelection].Chain[e].Along[f, continuous].With[coefficients].At[z].naturality` は、選んだ鎖ホモトピー逆から構成した実際の胞体鎖写像と特異コホモロジーの比較を結ぶ。
  `recoveryExists` が必要な逆の存在を与える。
  `Along[f, continuous].Homology[coefficients].At[z].naturality` は、実際の比較写像 \(\chi\otimes\mathrm{id}\) の誘導写像によるホモロジーの自然性を与える。
- `Naturality[B, target, targetCW].Chosen[sourceSelection, targetSelection].Coefficients[input, output, coefficientMap].At[z].Along[f, continuous]` は、実際の連続写像から胞体コホモロジーの引き戻しを構成し、比較同型との自然性を与える。
- `CellCollapse[cell, member, point].Pair.Basis.Incidence[sourceCell].Degree.Normalized[k, positive, h].Spherical.incidence` は、正の次元で胞体境界行列の成分が実際の球面間写像の次数であることを示す。
  球面間写像は貼り付け写像と他の胞体の圧縮から構成し、同相写像の向きも補正する。
  `CellCollapse[cell, member, point].Positive[k, positive].Orientation.existence` が、向きを補正した同相写像の存在を与える。
- `ZeroCollapse[cell].Basis.Incidence[sourceCell].Degree.incidence` は、\(1\) 次元胞体の境界成分を実際の \(S^0\) 上の次数と同定する。
  `endpoints` はこの成分を正の端点の指示値から負の端点の指示値を引いた整数として与える。
- `Coordinates.indexingExistence` と `With[indexing].Bounded.model` は、有限胞体の列挙と整数境界行列を与える。
  `Bounded.Compared[selection].equivalenceExists` は、この有限行列模型を実際の特異鎖に比較する。

`DiskLocal[n].Attachment[neighborhood]` は、一つの閉球の貼り付けを直接扱う。
入力は特性写像、穿孔近傍の実際の変形収縮、開球と補空間の同相写像であり、相対ホモロジーの比較はこれらから導く。
`DiskSphere[n].Quotient.homeomorphism` は、\(D^{n+1}/\partial D^{n+1}\) と \(S^{n+1}\) の同相写像である。

直和、相対鎖の分裂、切除の自然性、代表鎖の補正などの共通補題は `singular_cellular_algebra` に分けている。
