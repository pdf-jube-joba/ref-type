# 多様体と De Rham コホモロジーの利用例

公開されたライブラリを別パッケージから具体化し、解析・外代数・多様体・コホモロジーの接続を検査する。

| module | 利用する構成と法則 |
| --- | --- |
| `Calculus` / `OpenCalculus` / `MeanValue` | 極限、開集合上の微分、平均値定理、滑らかな合成 |
| `Alternating` / `LocalForms.On.CoefficientExpression` | 任意次数の交代形式、有限係数表示、外微分の係数公式 |
| `Geometry` | 標準アトラス、開部分多様体、一点・空多様体、飽和、標準・空多様体の滑らかな恒等写像 |
| `PlaneForms` | \(x\,dy\)、\(d(x\,dy)=dx\wedge dy\)、\(d^2=0\)、完全形式の類の零性 |
| `Shear.Forms` | \(F(u,v)=(u,v+u^2)\) のヤコビアン、\(F^*dy=dv+2u\,du\)、外微分との可換性 |
| `ShearCharts` | 非恒等のチャート変換、接ベクトルの代表変更、大域形式の異なる座標表示 |
| `ShearCharts.SmallForms` / `SmallSmooth` | 小さいアトラスからの一意な拡張、形式・コホモロジーの同型、滑らかさの判定 |
| `ShearCharts.Representations` | 同じ最大アトラスを生成する二つの表示の形式・コホモロジーの標準同型 |
| `Point` | 一点の \(H^0\cong\mathbb R\) と正次数の零性 |
| `Contravariance` | 形式とコホモロジーにおける反変な合成則 |
| `Pointwise` / `Cohomology` | 点や次数に依存する商の台集合、外延性、商の API |

```sh
target/debug/cli tests/projects/manifolds-de-rham --module manifolds_de_rham_tests --full-check-local --diagnostics compact
```
