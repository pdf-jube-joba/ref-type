# 境界・角付き多様体

有限次元 Dedekind 実数空間の開集合と、選んだ座標が非負である象限との共通部分を局所模型に使う。
`Dimension.Manifold` はこの模型への局所同相、開被覆、滑らかに延長できる遷移写像、Hausdorff 性、第二可算性を持つ。
制約を一つ選べば半空間、全部選べば象限、空にすれば通常の開集合になる。

| module | 公開する構成と法則 |
| --- | --- |
| `Model[n]` | 座標制約、象限、活性座標、面、内向き接錐、接線部分空間、実際の部分空間位相 |
| `Dimension[n].Quadrant[C, U]` | 任意の開集合と象限との共通部分の角付き多様体 |
| `Dimension.Chart.At.Extension` | 基点の通常の開近傍上で遷移写像と一致する滑らかな延長 |
| `Extensions.Local` / `ConeMap.On` | 延長によらない微分、および象限を保つ写像の微分による接錐の保存 |
| `Tangent[n].On[M].At[x]` | チャートとベクトルの商による接空間、ベクトル空間構造、座標線形同型 |
| `Tangent.On.At.Cones` | 座標によらない `Inward`、`Outward`、`Tangential`、`Boundary` と各チャートでの判定 |
| `SmoothMap[n, m].Between[M, N]` | 連続写像と局所的な滑らかな延長による滑らかな写像 |
| `MapIdentity` / `MapComposition` | 恒等写像、合成と延長の連鎖律 |
| `Differential[n, m].Between[M, N]` | 接空間間の実際の線形写像と接錐保存、定義域・標的両側の座標変更則 |
| `Immersion` / `Neat` | immersion、像への同相を伴う埋め込み、neat embedding と法線方向の座標判定 |
| `Face[n, r].On[C, U]` | 右の \(r\) 座標を零に固定した面、残る象限制約、滑らかな埋め込みと面の接束 |
| `Face.On.At` | 面の包含の微分と法線座標の核の互いに逆な対応、周囲の任意のチャートでの核の判定 |
| `Face[n, r].Global[F, M]` | 埋め込まれた大域的な面の局所正規形と像の条件 |
| `Boundary[n].Of[M].Build[cover]` | 半空間チャートで被覆された境界の通常の \(n\) 次元多様体と、その接束 |
| `Product[n, m].Of[M, N]` | 積位相、積チャート、第二可算性、積の境界の両因子による判定 |
| `Interior[n].Of[M].Build[]` | 内部への制限から作る、飽和アトラスを持つ既存の `manifolds` の多様体 |
| `Boundaryless[n].Of[M]` | 既存の境界なし多様体を空の座標制約で角付き多様体にする構成と同相、境界が空であること |
| `Sublevel[n].Of[U, f].Build[regular]` | 正則な非負領域の半空間チャート、境界の零点判定、境界多様体と接束 |
| `Sublevel.Of.Face[regular]` | 同じ零集合の G02 正則値多様体、包含の埋め込み、接空間と実際の微分の核との線形同型 |
| `Disk[n]` / `Interval[]` / `Cylinder[n].On[M]` | 閉円板 \(D^{n+1}\)、区間 \([-1,1]\)、既存の多様体と区間の積 |

## 座標不変性

滑らかさの入力は開集合上への延長の存在である。
延長の微分の一致や接錐の保存は入力に含めない。
`Model.Extension` は、境界でも使える正の座標方向の差商から延長の偏微分の一致を証明する。
`Extensions.Local` は異なる開近傍を交わらせ、全微分の一致へ持ち上げる。
遷移写像の逆と合成にこれを適用し、接空間の同値関係、座標線形同型、微分の座標変更則を導く。

`Model.RayControl` は各活性座標で非負なベクトルに対し、短い正の半直線が象限内に留まることを証明する。
`OneSided` の片側最小値の微分不等式を使って `ConeMap` が接錐の保存を証明する。
これによって `Cones.criterion` は一つのチャートの判定をすべてのチャートへ運び、`Lineality.criterion` は接方向を活性座標の零条件と同一視する。
ここで `Inward` と `Outward` は弱い接錐であり、接方向を含む。
正則な定義関数については `Sublevel.Of.Face.Kernel` が正・負・零の微分による厳密な内向き・外向き・接方向を公開する。

`Neat.Laws` は埋め込み、境界の逆像条件、標的の接方向を法とする微分の全射性、接方向の逆像条件で定義する。
`Neat.At.Coordinates.criterion` は全射性を活性座標での法線方程式と同値にする。
恒等写像は `NeatIdentity` で具体化する。

## 面と例

`Boundary.Build` の `cover` は境界上の半空間チャートによる被覆である。
角付き多様体の角では `Face.On` が残りの非負制約を引き継ぎ、面自体を角付き多様体として構成する。
`Face.Global` の局所正規形は、面の像が選んだ法線座標を零に固定した集合と一致することまで含む。
`Product.Boundary.criterion` と `Product.Of.At.boundaryCriterion` は
\(\partial(M\times N)=(\partial M\times N)\cup(M\times\partial N)\) の座標表示と内在的表示を与える。
積チャートの制約は両因子の制約の直和なので、両方の面が交わる場所には両方の制約が残る。

`Sublevel` は零点で定義関数の微分が全射であることを仮定する。
G02 の `Submersion.localExistence` が返す実際の局所微分同相を使い、領域を半空間に直す。
`Disk[n]` では \(1-\sum_i x_i^2\) を使い、球面上の動径微分から全射性を証明する。
`Disk.boundary` は上の一般の境界構成、`regularBoundary` は G02 の正則値構成による球面である。
`Interval.At.criterion` は境界が二つの端点であることを示し、`Cylinder.On.At.criterion` は積の境界が二つの端面であることを示す。

[Examples.ref](src/Examples.ref) は半直線、二次元象限、象限の境界面の埋め込み、円板、区間、帯、内部の通常の多様体を具体化する。
`Examples.Nonlinear` は半直線上の \(t\mapsto t^2\) の滑らかさと微分を検査する。
`Examples.EmptyCoordinates` は零次元円板と空の座標集合を扱う。

## 検査

```sh
cargo build -p cli --release --locked
target/release/cli libs/geometry/boundary_manifolds --module boundary_manifolds --full-check-local --memory-mib 12288 --cache-stats
python3 scripts/check_all.py --initial-memory-mib 12288 --memory-mib 12288 --cache-budget-mib 12288 --min-free-mib 512
```

最終ソースの検査条件と結果は[検査記録](../../../benchmarks/records/boundary-manifolds/README.md)に記録する。
