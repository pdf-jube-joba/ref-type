# 多様体上の微分形式

`Forms[n].On[M].Form(k)` は最大アトラスの各チャートに局所形式を割り当て、重なりで引き戻しが一致する族である。

| module | 内容 |
| --- | --- |
| `At` / `Wedge` / `ExteriorDerivative` / `Square` / `Leibniz` | 大域形式の線形構造、外積と外微分の法則 |
| `Pointwise` / `DegreeZero` | 接空間上の交代形式の族 / 滑らかな関数との対応 |
| `Regrade` | 次数の等式に沿う移送とチャート表示 |
| `Pullback.Between.Of` | 滑らかな写像による引き戻し、線形性・積・外微分の保存 |
| `PullbackIdentity` / `PullbackComposition` / `PullbackDiffeomorphism` | 恒等・反変合成則、同型 |
| `Restriction` / `Gluing` | 開部分多様体への制限、互換な局所形式の一意な貼り合わせ |
| `AtlasForms` / `Presentation` | 小さいアトラスからの拡張、表示間の標準同型 |
| `Forms.On.DeRham` | 閉形式・完全形式の商、次数付きの積、誘導写像 |
| `DeRham.DegreeZero` | 微分が零の関数との同型 |

[座標計算](../coordinate_calculus/README.md) に、引き戻し・貼り合わせ・コホモロジーの利用例がある。
