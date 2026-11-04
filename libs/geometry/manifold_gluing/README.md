# collar と境界の貼り合わせの局所構成

G04 の実装途中の package である。
局所構成と位相的な比較・一様化は証明済みだが、コンパクトな境界付き多様体の大域 collar の存在、指定された collar の相対的延長、大域的な滑らかな貼り合わせと double、積多様体の角の大域的な丸め、collar を保つ写像の滑らかな貼り合わせは未実装である。
これらを仮定した存在定理や、計画全体の完了は公開していない。

| module | 証明した内容 |
| --- | --- |
| `Boundary[n].On[M]` | 接錐で定めた境界の閉性と、コンパクトな多様体の境界のコンパクト性 |
| `ChartMap[n].On[M].Of[c]` | チャートの逆座標写像の滑らかさと単射性 |
| `LocalCollar[n].On[M]` | 半空間チャートで被覆された境界の各点における局所 collar の存在 |
| `LocalCollar.On.In.Topology` | 局所 collar の像が開集合であることと、その像への実際の同相、零の時間座標と境界との同値 |
| `LocalPush[n].On[a,q]` | G01 の bump による法線方向への滑らかな局所移動、初期値、bump が零の場所での恒等性、半空間の保存と厳密な内向き移動 |
| `CompactStrip[T,B,X].On[...]` | コンパクトな底空間上で、初期単射性と零時刻付近の局所単射性から時間幅を一様化する定理 |
| `TopologicalCollar.On.Of.Relative` | 既存の collar とコンパクトな境界について、指定された開近傍に入るパラメータ近傍の存在 |
| `TopologicalCollar.On.Comparison` | 既存の二つの位相的 collar の像の間の、境界を固定する同相 |
| `Seam.Embedded` | 境界の両側の包含が単射な場合の商の同値類の分類、同じ側の単射性、両側の点の一致条件 |
| `Seam.Map` | 境界上の可換性から誘導される商空間の写像、その値と連続性 |
| `HalfSpaceDouble[n]` | 半空間の double と座標空間の同相、および商空間そのものの滑らかな多様体構造 |
| `Reflection.Orientation` | 法線反射の行列式が \(-1\) であることと、任意の最高次交代形式の符号反転 |
| `RoundedCorner[n].AtScale[epsilon]` | 自由な \(n\) 座標を伴う局所模型 \(u>0,uv\ge\varepsilon\) の滑らかな境界付き多様体、両法線座標の正値性、境界の式 \(uv=\varepsilon\) |
| `Diffeomorphism` / `DiffeomorphismIdentity` / `DiffeomorphismComposition` | 角付き多様体の微分同相、その逆・恒等・合成 |

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
