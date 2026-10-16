# 特異鎖と特異コホモロジー

標準単体からの連続写像上の自由整数加群を特異鎖とし、整数加群への Hom から特異余鎖とコホモロジーを構成する。
直接依存は [ref.toml](ref.toml)、公開 module は [root.ref](src/root.ref) にある。

| module | 構成と証明 |
| --- | --- |
| `Simplices` / `At` / `Faces` / `Identities` | 全特異単体、定数単体、面写像とその合成公式。 |
| `Chains` / `Boundary` / `SquareZero` | 全特異単体上の自由整数加群、交代境界、その二乗の零性、非負次数と整数次数の複体。 |
| `Chains.Augmentation` | 零次の増大写像、境界での消滅、空間の点から得る右逆。 |
| `Chains.Reduced.NegativeOne` | 非空空間での被約ホモロジーの負一次の消滅と、空空間での整数との同型。 |
| `Chains.Reduced` | 次数 \(-1\) に整数を置く増大鎖複体と、係数付き Hom による被約余鎖。 |
| `Cochains.With` / `Cohomology` | 任意の整数加群を係数とする余鎖複体、閉余鎖・類・コホモロジーの加群。 |
| `Cochains.With.At` | 全特異単体への任意の値の割り当てと余鎖との加群同型。 |
| `Cochains.Abelian` | 可換群から標準の整数加群を作り、係数付きコホモロジーへ渡す。 |
| `Maps` / `Differential` / `Composition` | 後合成から得る鎖写像、境界との可換性と合成則、整数次数への零拡張。 |
| `Identity` / `Identity.Coefficients` | 恒等連続写像が鎖・余鎖・コホモロジーの恒等写像を誘導すること。 |
| `Maps.Coefficients` | 空間に関して反変、係数に関して共変な余鎖写像・コホモロジー写像と、生成元での評価公式。 |
| `Maps.Composition.Coefficients` | 連続写像の合成が誘導するコホモロジー写像の合成則。 |
| `Homotopy` / `Coefficients` | cylinder のアフィン prism 鎖から構成する鎖ホモトピーと、任意係数でのホモトピー不変性。 |
| `Equivalence.With` | 位相空間のホモトピー同値から得るコホモロジーの加群同型。 |
| `Relative` / `Injection` | 部分空間からの単射な鎖写像、その像による商、相対鎖の短完全列。 |
| `Relative.Homology` / `LongExact` | 相対ホモロジー、接続写像、その前後の合成の零性と長完全列の完全性。 |
| `Relative.Split` / `Relative.With.PairSequence` | 次数ごとの包含の分裂と余鎖の短完全列、相対コホモロジー長完全列。 |
| `Relative.With.Vanishing` | 相対余鎖と部分空間の鎖上で零になる全体の余鎖との加群同型。 |
| `Relative.With` | 商鎖複体から係数加群への Hom と相対コホモロジー。 |
| `Coefficients.Sequence.On` / `Bockstein` | 係数短完全列が誘導する余鎖の短完全列、Bockstein 接続写像と完全性。 |
| `OrderedTuples` / `ConeBoundary` / `SquareZero` | 頂点列上の自由鎖、交代境界と複体、頂点を先頭に加える cone の境界公式。 |
| `OrderedTuples.Prism` | 二つの頂点写像の間の prism、境界公式、前合成・後合成に関する自然性。 |
| `OrderedTuples.Subdivision` / `Homotopy` / `Natural` | 各頂点列に指定した中心を使う細分、境界との可換性、恒等写像との鎖ホモトピー、中心を保つ写像に関する自然性。 |
| `CylinderChains` | 頂点列を cylinder 内のアフィン特異鎖へ送る鎖写像、普遍的 prism、面への制限との整合性。 |
| `SimplexChains` / `Subdivision` / `Face` | 単体内のアフィン鎖への評価、等重みの重心細分と鎖ホモトピー、面への制限との整合性。 |
| `Subdivision` / `Natural` / `Coefficients` | 特異鎖上の重心細分と恒等写像との鎖ホモトピー、連続写像との可換性、任意係数のコホモロジーでの恒等作用。 |
| `SimplicialChains.On` | 面の恒等式を満たす任意の次数付き集合からの自由鎖複体と、その関手性。 |
| `Small` / `FromSubset` / `With` | 被覆要素に含まれる単体上の小鎖複体、全体への単射、被覆要素からの持ち上げ、余鎖の制限。 |
| `Small.Subdivision` | 小鎖を保つ細分と鎖ホモトピー、全特異鎖への包含との整合性。 |
| `SubdivisionCells` / `Comparison` | 細分セルの符号付き鎖、アフィン頂点列への評価と重心細分との一致。 |
| `SubdivisionCells.Words` / `Length` / `Evaluation.Comparison` | 反復細分のセル列の鎖、長さごとの部分加群と細分に可換な評価。 |
| `Small.Cover.On.Eventually` | 引き戻した開被覆の Lebesgue 数と距離評価から、十分な反復細分で各セルが小単体になること。 |
| `Small.Cover.On.WordChains.Support` | 各特異単体の十分な反復細分が小鎖複体の像に入ること。 |
| `Zero.With.Functions` | 任意の空間の零次コホモロジーと、道成分全体から係数群への全関数の加群との同型。 |
| `Zero.Homology` | 零次整数ホモロジーと、道成分の集合上の自由整数加群との同型。 |
| `Calculations.With.Singleton` | 一点空間の零次の係数加群との同型と、全正次数での消滅。 |
| `Calculations.With.Contractible` | 具体的な収縮から得る零次の係数加群との同型と、全正次数での消滅。 |
| `Calculations.With` | 空空間の全非負次数における通常コホモロジーの消滅と零加群との同型。 |

`Chains.boundary n` は \(C_{n+1}\to C_n\) である。
境界の符号は、`module_theory.Module.Over.Alternating.sum` の先頭を正にする交代和を使い、\(i\) 番目の面に \((-1)^i\) を付ける。
通常の整数次数の鎖複体は負次数に零加群を置く。
増大鎖複体は `Chains.Reduced.complex` で、\(C_0\to C_{-1}=\mathbb Z\) に増大写像を置き、\(-2\) 以下は零加群にする。

係数には `module_theory.Module.Over` の整数加群の `Bundle` を渡す。
余鎖は特異単体全体への全関数に対応し、有限支持の条件は鎖の側にある。
`Cochains.With.At.productIsomorphism` はこの対応を加群同型として公開する。
`Relative.LongExact` の接続写像は、相対サイクルの持ち上げの境界を部分空間の鎖として読む符号である。

[利用例](../cohomology_models/README.md) は、代表余鎖の評価、両微分の二乗の零性、増大、係数付き誘導写像、相対接続写像と空空間の計算を別パッケージで検査する。
[実装計画](../../../_plans/math/singular-cohomology.md) は、ホモトピー不変性・切除・有限モデルとの比較・積・具体的な空間の計算までを含む。

```sh
cargo build -p cli
target/debug/cli libs/topology/singular_cohomology --module singular_cohomology --diagnostics compact
target/debug/cli libs/topology/cohomology_models --module cohomology_models --diagnostics compact
```

workspace 共通の `libs/refcache/` を利用する。
整数次数の複体の別名の再公開については [G15](../../../_plans/gaps.md#g15) に、単独で検査できる再現例と直接 import する回避例がある。
