# 特異鎖の細分と小鎖

[特異鎖の基礎](../cohomology/README.md) を使い、重心細分、小鎖と開被覆の比較を構成する。
直接依存は [ref.toml](ref.toml)、公開 module は [root.ref](src/root.ref) にある。
開被覆に対する鎖ホモトピー同値は、[切除](../excision/README.md) と有限モデルとの比較に使う。

| module | 構成と証明 |
| --- | --- |
| `SimplexChains` / `Subdivision` / `Face` | 単体内のアフィン鎖への評価、等重みの重心細分と鎖ホモトピー、面への制限との整合性。 |
| `Subdivision` / `Natural` / `Coefficients` | 特異鎖上の重心細分と恒等写像との鎖ホモトピー、連続写像との可換性、任意係数のコホモロジーでの恒等作用。 |
| `Subdivision.Iterated` / `Homotopy` | 任意回数の細分の鎖写像と、恒等写像との鎖ホモトピー。 |
| `Small` / `FromSubset` / `With` | 被覆要素に含まれる単体上の小鎖複体、全体への単射、被覆要素からの持ち上げ、余鎖の制限。 |
| `Small.Subdivision` | 小鎖を保つ細分と鎖ホモトピー、全特異鎖への包含との整合性。 |
| `Small.Pullback.Over` / `Square` | 被覆の引き戻しによる小鎖写像と、通常の特異鎖写像との可換性。 |
| `OpenCover.On.Subspace` | 部分空間への開被覆の引き戻しと、小鎖の包含の次数ごとの分裂。 |
| `OpenCover.On.Subspace.Degree.Lift` | 像が部分空間に入る小単体の持ち上げと、包含後の元の単体との一致。 |
| `OpenCover.On.Subspace.Relative` / `With` | 通常の相対理論への比較写像、長完全列との整合性、整数ホモロジーと任意係数コホモロジーの同型。 |
| `SubdivisionCells` / `Comparison` | 細分セルの符号付き鎖、アフィン頂点列への評価と重心細分との一致。 |
| `SubdivisionCells.Words` / `Length` / `Evaluation.Comparison` | 反復細分のセル列の鎖、長さごとの部分加群と細分に可換な評価。 |
| `Small.Cover.On.Eventually` | 引き戻した開被覆の Lebesgue 数と距離評価から、十分な反復細分で各セルが小単体になること。 |
| `Small.Cover.On.WordChains.Support` | 各特異単体の十分な反復細分が小鎖複体の像に入ること。 |
| `Small.Persistence` / `Small.Cover.Chains` | 小鎖に入った後の反復細分の保存と、任意の特異鎖についての十分な細分回数の存在。 |
| `Small.HomotopyPersistence` / `OpenCover.On.Selection` | 反復ホモトピーによる小鎖の保存と、各鎖に対する最小の細分回数の選択。 |
| `OpenCover.On` | 小鎖複体の包含の具体的な鎖ホモトピー逆、面との整合性を持つ再帰構成、小鎖上の厳密な左逆。 |
| `OpenCover.On.With.At` | 任意の整数加群を係数とする、小鎖への余鎖の制限によるコホモロジー同型。 |
| `OpenCover.On.With.Homotopies` | 余鎖の制限と延長の両合成を恒等写像へ結ぶ余鎖ホモトピー。 |

`SimplexChains` は標準単体内のアフィン鎖、`Subdivision` は特異鎖上の細分と恒等写像との鎖ホモトピーを扱う。
`Small` は被覆要素内の単体からなる複体、`OpenCover.On` はその包含の鎖ホモトピー逆を与える。
`OpenCover.On.Subspace.Relative` は部分空間についての比較と任意係数への適用を持つ。

```sh
cargo run -p cli -- libs/topology/singular/subdivision
```
