# 体係数の Künneth 同型

有界有限自由体係数余鎖複体について、分裂によらない標準外積同型を構成する。

| module | 内容 |
| --- | --- |
| `FieldFinite.Over.Of` | サイクル・境界・コホモロジーの射影性、分裂と収縮 |
| `TensorCochain.Over.Total` | 有限対角直和、微分 \(d_h+(-1)^p d_v\) と二乗零 |
| `TensorMapping` / `HomotopyLeft.With` | 写像とホモトピーの total への持ち上げ |
| `CycleProduct` / `Exterior.map` | サイクルの積、境界による消滅、コホモロジー上の外積 |
| `CycleProductNaturality.With.Exterior` / `IndexedExterior` | 両因子の自然性と次数移送 |
| `Swap` / `TensorSymmetry.At.Component` | 符号 \((-1)^{pq}\) の交換と代表元公式 |
| `Kunneth.Field.Of.Canonical` | 成分の外積をまとめる同型、代表元公式と一意性 |
| `Canonical.SplittingChange` / `Mapping.With.At` | 分裂変更、標準同型の両向きの自然性 |
| `Kunneth.Field.Of.Symmetry` / `Unit` | 交換符号と左右の単位則 |
| `Kunneth.Field.Assertions` | 複体・写像・次数を全称量化した定理 |

`With.At.ExteriorComparison.backwardExterior` は分裂から得た同型の逆と標準外積の一致を示す。
単位複体は零次に一座標、他の次数に零座標を持つ。
