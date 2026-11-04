# collar と境界の貼り合わせ

コンパクトな境界付き多様体の滑らかな collar、境界の微分同相に沿う貼り合わせと double、積の角近傍に支持された丸めを、実際の写像・逆写像・チャートから構成する。
`boundary_manifolds` の角付き多様体と `smooth_partitions` の滑らかな bump を使う。
存在定理の入力に、大域 collar や貼り合わせ後の滑らかな構造を仮定しない。

## collar

| API | 証明した内容 |
| --- | --- |
| `CollarEmbedding.On.With.exists` | コンパクト性と実際の境界チャート被覆から、横断的な押し込みと一様な collar を構成する |
| `CollarEmbedding.From.Of` | 開いた像への同相、単射性、連続な逆写像、逆写像の各点での実際の滑らかな局所表示 |
| `CollarWidth` | 共通時間近傍に入る正の半開区間の幅 |
| `CollarRelative.On.With.In.exists` | 指定された境界全体の開近傍に collar の像が収まる相対版 |
| `CollarComparison` | 二つの構成された collar の共通時間近傍上の滑らかな比較と、境界を固定する法則 |
| `CollarRestriction` | 任意の小さい開いたパラメータ領域とその像との実際の微分同相 |
| `CollarWindow.Core` | 閉時間区間から得られるコンパクトな collar 領域と、その時間座標による判定 |

相対版は collar の像を指定近傍内に収める定理である。
既存の部分 collar と一致するように延長する、より強い定理は公開していない。
`GlobalPush` はコンパクトな台を持つ座標内の押し込みを恒等写像と滑らかに接続し、有限個を合成する。
その初期法線速度の正値性から実際の半空間局所逆写像を構成し、コンパクトな境界上で時間幅を一様化する。

## 境界の貼り合わせと double

`BoundarySeam` は境界の実際の微分同相から商空間を構成し、コンパクト性・Hausdorff 性・第二可算性を証明する。
`SeamCollar` は符号付き collar を、商空間の開いた継ぎ目への同相として構成する。
左右の内部と継ぎ目の全9種類のチャートの重なりで滑らかな遷移を構成する。
`CompactGluing.Between.With.Along.Compact.exists` は実際の商の滑らかな atlas と、境界が残らないことを公開する。
結果には構成した collar のデータ、atlas と構成の一致、左右全体と符号付き継ぎ目の実際の滑らかな包含、および各写像の点ごとの値の法則を保持する。
`Double.Compact.left` と `right` からも、公開結果に対応する滑らかな包含を直接取り出せる。
`Double.On.With.Compact.exists` は境界の恒等微分同相による double を構成する。
`SeamCollar.Image.Compact.Cover.Inclusions` は左右全体の包含と符号付き継ぎ目の包含を、実際の滑らかな写像として構成する。
同じ `Cover` の `CollarMaps` は collar を保つ二つの滑らかな写像を商の滑らかな写像へ貼り合わせ、その恒等写像の例も持つ。

## 積の丸め

`SupportedRounding` は滑らかな bump から \(\psi(d)=\sqrt{d^2+b(d)}\) を構成する。
`Higher` の正則な sublevel \(u+v-\psi(u-v)\geq0\) は元の象限に含まれ、\(u\geq3\) または \(v\geq3\) では元の象限と一致する。
`Quarter.Outside` は外側の開部分の実際の恒等微分同相を構成する。
`ProductCollar` は共通の正のスケール \(q\) を選び、\(3q<4q<\varepsilon\leq1\) の積 collar を構成する。
`Rounded` は正規化された丸め関数が負となる開集合を実際の積から除く。
得られる領域は閉じていてコンパクトであり、変更は内側のコンパクト領域に収まり、元の角の点を除く。
`NearModel.Image` はその開いた角近傍と、境界の積と丸めた正規モデルの積との実際の同相を構成する。
`Rounded.Global.Using.Cover` は内側と外側の全4種類の滑らかなチャート変換を構成する。
`ProductCollar.Between.With.Compact.exists` は入力のコンパクト性と境界チャート被覆から、collar・スケール・丸め領域・大域 atlas まで構成する。
`Compact.Of` はその多様体、コンパクト性、コンパクト領域の外側での一致、元の角を除く法則を公開する。
現状の結果は角付き多様体型であり、丸めた結果の正規化された `Boundary.Cover` と高次の角がない保証を追加している。

## 向きと補助定理

`Reflection.Orientation` は法線反射の行列式と任意の最高次交代形式の符号反転を証明する。
`BoundarySigns` は外向き法線の反転、二つの法線の収縮順序の交換、境界の打ち消しの符号を証明する。
`BoundaryForms` は実際の境界包含の微分による引き戻しにこれらの符号を適用する。
貼り合わせと double の実際の包含に対する向きの整合性を追加している。
`DiffeomorphismCones` は実際の滑らかな逆写像から境界と接方向の保存を導く。
`OpenManifoldCones` は開部分の包含について、境界の一致と、その微分による接方向・厳密な法線方向の判定を証明する。
`OpenSmoothExtension` は開集合上の滑らかな写像と閉集合の外の写像が重なりで一致するとき、その実際の滑らかな接続を構成する。

検査対象、checker、固定ソースとキャッシュの対応、終了コードと資源使用量は [検査記録](../../../benchmarks/records/manifold-gluing/README.md) にある。
