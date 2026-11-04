# collar と境界の貼り合わせの構成

G04 の実装途中の package である。
局所 collar、位相的な比較・一様化、および大域的な滑らかな押し込みホモトピーは証明済みである。
コンパクトな境界付き多様体の大域 collar の存在、指定された collar の相対的延長、大域的な滑らかな貼り合わせと double、積多様体の角の大域的な丸め、collar を保つ写像の滑らかな貼り合わせは未実装である。
これらを仮定した存在定理や、計画全体の完了は公開していない。

| module | 証明した内容 |
| --- | --- |
| `Boundary[n].On[M]` | 接錐で定めた境界の閉性と、コンパクトな多様体の境界のコンパクト性 |
| `ChartMap[n].On[M].Of[c]` | チャートの逆座標写像の滑らかさと単射性 |
| `LocalCollar[n].On[M]` | 半空間チャートで被覆された境界の各点における局所 collar の存在 |
| `LocalCollar.On.In.Topology` | 局所 collar の像が開集合であることと、その像への実際の同相、零の時間座標と境界との同値 |
| `LocalPush[n].On[a,q]` | G01 の bump による法線方向への滑らかな局所移動、初期値、bump が零の場所での恒等性、半空間の保存と厳密な内向き移動 |
| `LocalPush.On.Bounds` / `LocalPush.On.Derivative` | 移動量の上界、チャート内に留まる評価、時間零での微分の明示式 |
| `GlobalPush[n].On[M]` | コンパクト台の座標移動を多様体全体の滑らかな写像へ延長し、各境界点を動かす局所族と、コンパクトな境界全体を動かす一つのホモトピーと、境界全体で初期速度が横断的なホモトピーを構成 |
| `GlobalPush.On.In.Velocity` | 初期速度の内向き性と、bump が正の場所での厳密な内向き性 |
| `PushHomotopy` | 時間を共有する滑らかな有限合成、初期値の保存、内点の保存、境界に残る点の固定、開被覆による大域化 |
| `BoundaryInclusion` | G03 で構成した境界多様体を角付き多様体として扱ったときの、元の多様体への滑らかな包含 |
| `InwardNeighborhood` | コンパクトな境界について、時間零で包含に一致し、正の時刻では内点に入る実際の滑らかな写像 \(\partial M\times[0,1)\to M\) の存在 |
| `InitialJet` / `HomotopyVelocity` | 初期値が恒等である写像の空間方向の微分、座標に依存しない時間方向の初期速度と内向き性、任意の空間速度を加えたときの微分 |
| `SmoothChainRule` / `ProductDifferential` / `PairDifferential` | 角付き多様体の微分の連鎖律、積の接ベクトルの分解、積へ値を取る写像の微分 |
| `HomotopyCompositionVelocity` / `ConeAddition` | 合成の初期速度が和であることと、内向き速度を加えたときの厳密な内向き性の保存 |
| `TransverseHomotopy` | 局所的に横断的な押し込みが与えられた場合の、コンパクトな境界上の大域的な横断的押し込みへの合成 |
| `BoundaryDifferential` | 境界包含の微分の単射性と、その像が境界に接する接ベクトル全体であること |
| `HalfSpaceJet` | 境界超平面を固定する滑らかな写像の微分の明示式、法線方向の微分が非零の場合の実際の逆行列と局所逆写像 |
| `HalfSpaceSigns` / `ScalarIncreasing` / `SectionIncreasing` | 正の法線偏微分から、平均値の定理を用いて法線座標の符号を保つ近傍を構成 |
| `HalfSpaceInverse` | 境界超平面を固定し、初期の法線微分が正である写像の、半空間を保つ局所微分同相 |
| `CompactStrip[T,B,X].On[...]` | コンパクトな底空間上で、初期単射性と零時刻付近の局所単射性から時間幅を一様化する定理 |
| `TopologicalCollar.On.Of.Relative` | 既存の collar とコンパクトな境界について、指定された開近傍に入るパラメータ近傍の存在 |
| `TopologicalCollar.On.Comparison` | 既存の二つの位相的 collar の像の間の、境界を固定する同相 |
| `Seam.Embedded` | 境界の両側の包含が単射な場合の商の同値類の分類、同じ側の単射性、両側の点の一致条件 |
| `Seam.Map` | 境界上の可換性から誘導される商空間の写像、その値と連続性 |
| `HalfSpaceDouble[n]` | 半空間の double と座標空間の同相、および商空間そのものの滑らかな多様体構造 |
| `Reflection.Orientation` | 法線反射の行列式が \(-1\) であることと、任意の最高次交代形式の符号反転 |
| `RoundedCorner[n].AtScale[epsilon]` | 自由な \(n\) 座標を伴う局所模型 \(u>0,uv\ge\varepsilon\) の滑らかな境界付き多様体、両法線座標の正値性、境界の式 \(uv=\varepsilon\) |
| `Diffeomorphism` / `DiffeomorphismIdentity` / `DiffeomorphismComposition` | 角付き多様体の微分同相、その逆・恒等・合成 |

`GlobalPush` の座標式は \(x+tq b_q(x)e_\nu\) であり、\(0\le t<1\) で移動量を \(q\) 以下に抑える。
bump の台を含む半径 \(2q\) の閉集合をチャート内の半径 \(4q\) の球に収め、移動後もチャート内に留まることを証明する。
コンパクトな台の像の外では恒等写像と一致する開近傍を用いて、連続性と滑らかさを証明する。
`CollarCoordinates` はこの同じ写像の境界での法線微分が正であることを証明し、`HalfSpaceInverse` を適用する。
`CollarLocal` は実際の局所的な単射性、開いた像、連続な逆写像を構成する。
`CollarStrip` はコンパクトな境界上の時間幅を一様化し、`CollarEmbedding` はその積から開いた像への大域同相を構成する。
前向き写像は `InwardNeighborhood` の滑らかな写像の制限である。
`CollarEmbedding.Of.inverseSmooth` は大域逆写像の各点で実際の滑らかな局所表示が存在することを証明する。
`CollarWidth` は時間近傍の内部に入る正の半開区間の幅を取り出す。
`CollarRelative` は指定された境界の開近傍内に大域的な滑らかな collar の像が収まるように時間を縮める。
`CollarComparison` は二つの構成に共通の時間近傍を取り、境界を固定する比較同相と、その両方向の実際の滑らかな局所表示を構成する。
指定された既存 collar の相対拡張、一般の貼り合わせと大域的な角の丸めはまだ構成していない。

`CompactStrip` の証明は、二つの点が同じ単射性近傍に入る場合と、像を Hausdorff 性で分離できる場合の開集合を合わせる。
この開集合を二つの時間と二つの底点の積へ引き戻し、底空間の二乗のコンパクト性と tube lemma から共通の時間近傍を得る。
大域 collar を入力として仮定する補題ではない。

`RoundedCorner` は局所的な双曲線による丸めであり、既存の積多様体へコンパクト台で接続する構成を含まない。
`TopologicalCollar` は位相的な同相とその法則で定め、滑らかな相対 collar 定理とは区別する。

[Examples.ref](src/Examples.ref) は半直線の double、丸めた象限、閉区間の局所 collar、および一次元の局所移動を具体化する。

```sh
cargo build -p cli --release --locked
target/release/cli libs/geometry/manifold_gluing --module manifold_gluing --full-check-local --memory-mib 12288 --cache-stats
python3 scripts/check_all.py --initial-memory-mib 12288 --memory-mib 12288 --cache-budget-mib 12288 --min-free-mib 512
```

検査結果と対象ソースの対応は [検査記録](../../../benchmarks/records/manifold-gluing/README.md) に記録する。
