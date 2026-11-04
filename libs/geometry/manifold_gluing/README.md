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
`BoundarySeam` は境界の微分同相に沿う実際の商空間を作る。両側の包含の単射性と交差の判定を公開し、両側がコンパクトであれば商のコンパクト性、Hausdorff 性と第二可算性を証明する。
その証明には、コンパクトな貼り合わせ部分に沿う商写像の閉性 (`ClosedPushout`)、コンパクト Hausdorff 空間からの閉全射による分離性と第二可算性 (`ClosedSurjection`)、可算基底の有限和の列挙 (`FiniteBasisUnions`) を用いる。
指定された既存 collar の相対拡張と大域的な角の丸めは引き続き実装中である。

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

`ChartTransport` は、開いた像への同相から実際のチャートを移し、その内部での滑らかな座標変換と被覆を証明する。
`SignedParameter` は正負の法線パラメータの連続な分解、正側・負側それぞれでの実際の滑らかな局所表示、半開区間からの連続な挿入と零時刻での一致を構成する。
`CollarBoundary` は、構成した collar 候補の像が境界にあることと時間が零であることが同値であると証明する。
これらは一般の継ぎ目の atlas の構成に用いる。

`SeamCollar` は二つの実際の大域 collar を共通の正の時間幅で、境界の微分同相に沿って接続する。
符号付き collar から実際の商空間への連続な単射を構成し、その像が開集合であることと像への全射性を証明する。
`SeamOpen` は境界で対応する開集合の和が商で開くことを証明し、`CompactEmbedding` はコンパクト空間から Hausdorff 空間への連続単射の像への同相を構成する。
`SeamCollar.Image.Compact` は左右の閉集合上で構成した逆写像を接続し、実際の開いた継ぎ目近傍への同相を構成する。
`Charts` はその開近傍を覆うチャートを構成し、その内部での滑らかな座標変換を証明する。
`InteriorInclusion` は G03 の内点多様体を角付き多様体として扱ったときの元の多様体への滑らかな包含である。
左右の内部と継ぎ目の座標を合わせ、商全体の滑らかな atlas を構成する。

`InteriorInclusion.InverseAt` は内点での包含の逆の滑らかな局所表示を構成する。
`InteriorEmbedding` と `InteriorPatches` は左右の内部の像が商で開くことを示し、その座標近傍を構成する。
`SeamCollar.Image.Compact.Cover` は左右の内部と継ぎ目の3種類の座標近傍が商空間全体を覆うことを証明する。
`Cover.manifold` は、左右の内部と継ぎ目の全9種類の重なりで実際の滑らかな座標変換を証明した、商空間上の多様体である。
`LeftTransition`・`RightTransition` と `LeftInverse`・`RightInverse` は内部と継ぎ目を結ぶ両方向の滑らかな局所表示を構成する。
`Sides` は内部の像が左右で交わらず、左内部との重なりでは法線パラメータが正、右内部との重なりでは負となることを証明する。
`ChartCross` は局所表示を座標移送に適用し、`LocalSmoothCompose`・`LocalSmoothPair`・`ProductLocalMap` は局所表示の合成と積を構成する。
`Cover.Interior.noBoundary` は貼り合わせた多様体に境界が残らないことを証明する。
`CompactGluing` は実際の pushout の位相上の滑らかな atlas と境界がないことを組にした構造を構成し、`Double` は境界の恒等写像に沿う double を公開する。
`TransportInclusion` は開近傍へ移したモデルから全体への滑らかな写像と、その逆の滑らかな局所表示を構成する。
`TransportOut` と `Cover.Mapping` は、左右の内部と符号付き継ぎ目での滑らかな写像を用いて、商全体の写像の滑らかさを証明する。
`Cover.Inclusions` は左右の元の境界付き多様体から商への実際の滑らかな包含を構成する。
`Cover.CollarMaps` は共通の collar 幅で collar 座標を保つ左右の滑らかな写像と滑らかな境界写像から、商の間の実際の滑らかな写像を構成する。
零時刻の collar の一致から商への降下条件を導き、左右の内部と符号付き継ぎ目での実際の表示を用いて全体の滑らかさを証明する。
`Cover.IdentityMap` は恒等写像をこの構成に適用し、得られた商全体の写像が実際に恒等写像であることを証明する。
`BoundarySigns` は外向き・内向きの法線の反転による符号、二つの法線の収縮順序の交換による符号と打ち消しを証明する。
`BoundaryForms` は実際の境界包含の微分で収縮した形式を引き戻し、境界の接ベクトル上で法線の反転と再尺度化の公式を公開する。
`SupportedRounding` は滑らかな bump から \(\psi(d)=\sqrt{d^2+b(d)}\) を構成する。
`Higher` は \(u+v-\psi(u-v)\geq0\) で定まる実際の滑らかな境界付き多様体であり、元の象限に含まれ、\(u\geq3\) または \(v\geq3\) では元の象限と一致する。
接方向を加えた任意次元の正規モデルを扱い、境界は \(u+v=\psi(u-v)\) である。
`QuadrantOpen` と `OpenManifold` は角付き多様体の任意の開部分集合に、制限されたチャートと実際の滑らかな atlas を構成する。
指定された部分 collar の相対拡張と、一般の積多様体への丸めモデルの大域的な接続は継続中である。

`SupportedRounding.Higher.Quarter` は丸めた領域から元の象限への実際の滑らかな包含写像を持つ。
`Quarter.Outside` は二つの法線座標のいずれかが 3 より大きい開部分について、元の象限と丸めた多様体の間の恒等微分同相を構成する。
`OpenManifold.Inclusion` と `OpenCorestriction` は開部分多様体の滑らかな包含・局所逆写像と、像が開部分に入る写像の制限を与える。
`ChartModel` は一つの大域チャートを持つ多様体とその標準象限の実際の微分同相を、`DimensionChange` は同じ次元の異なる自然数表示間の恒等写像を構成する。
`CompactTimes` は collar の有限な閉時間区間のコンパクト性を証明する。

`CollarRestriction` は任意の小さい開いた collar パラメータ領域とその像との実際の微分同相を構成する。
`CollarWindow.Core` は閉時間区間から得られるコンパクトな collar 領域を構成し、その領域に入ることと時間座標の上限を対応させる。
`ProductCollar` は二つのコンパクト collar の共通の正のスケールを選び、積の角の開近傍と、その内側のコンパクト領域を構成する。
`Rounded` は正規座標の丸め関数が負となる開集合を実際の積から除き、閉じたコンパクトな丸め領域を得る。
変更箇所は上記コンパクト領域の内側に含まれ、その外側は元の積と点ごとに一致する。
この丸め領域への滑らかな atlas の接続は継続中である。

`ProductCollar.Rounded.NearModel` は境界の積と丸めた正規モデルの積から元の積多様体への実際の滑らかな写像を構成する。
`Parameters` は非負の丸め条件を満たす collar パラメータ領域との同相を、`Image` は実際のコンパクトな丸め領域の開いた角近傍との同相を構成する。
`TimePlane` は二つの collar 時間から正規化された象限への実際の滑らかな写像を与える。
`RoundingWindow.Outside` は外側の象限から丸めモデルへの滑らかな写像と局所逆写像を、`OpenProductModel` は開いた積部分の滑らかな包含と局所逆写像を与える。
外側のチャートとの接続と、指定された部分 collar の相対拡張は継続中である。

`ProductCollar.Rounded.Global.Using.Cover` は実際のコンパクトな丸め領域に、内側と外側の全4種類の滑らかなチャート変換を持つ大域 atlas を構成する。
内側から外側への変換は実際の滑らかな collar 写像と開部分の局所逆写像から、外側から内側への変換は二つの collar の局所逆写像、正規化、外側の丸めモデルの逆写像から構成する。
`ProductCollar.With.Compact.exists` は二つのコンパクトな境界付き多様体とその境界チャート被覆だけから、collar・共通スケール・丸め領域・大域 atlas を構成する。
`Compact.Of` は得られた多様体、そのコンパクト性、コンパクトな変更領域の外側で元の積と一致すること、元の角の点が丸め領域から除かれることを公開する。
内側の局所モデルは通常の境界多様体の積と正則な sublevel の積である。
指定された既存の部分 collar の相対拡張は継続中である。
