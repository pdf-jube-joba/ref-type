# 特異鎖と特異コホモロジー

標準単体からの連続写像上の自由整数加群を特異鎖とし、整数加群への Hom から特異余鎖とコホモロジーを構成する。
直接依存は [ref.toml](ref.toml)、公開 module は [root.ref](src/root.ref) にある。
重心細分、小鎖と開被覆の比較は [singular_subdivision](../subdivision/README.md) にある。

| module | 構成と証明 |
| --- | --- |
| `Simplices` / `At` / `Faces` / `Identities` | 全特異単体、定数単体、面写像とその合成公式。 |
| `Chains` / `Boundary` / `SquareZero` | 全特異単体上の自由整数加群、交代境界、その二乗の零性、非負次数と整数次数の複体。 |
| `Chains.Augmentation` | 零次の増大写像、境界での消滅、空間の点から得る右逆。 |
| `Chains.Reduced.NegativeOne` | 非空空間での被約ホモロジーの負一次の消滅と、空空間での整数との同型。 |
| `Chains.Reduced` | 次数 \(-1\) に整数を置く増大鎖複体と、係数付き Hom による被約余鎖。 |
| `Cochains.With` / `Cohomology` | 任意の整数加群を係数とする余鎖複体、閉余鎖・類・コホモロジーの加群。 |
| `Cochains.With.At` | 全特異単体への任意の値の割り当てと余鎖との加群同型。 |
| `Cochains.OverRing.With` / `Relative.OverRing.With` | 可換環上の係数加群、点ごとのスカラー倍、余境界の線形性、通常・相対コホモロジーの環上の加群構造。 |
| `Cochains.Abelian` | 可換群から標準の整数加群を作り、係数付きコホモロジーへ渡す。 |
| `Maps` / `Differential` / `Composition` | 後合成から得る鎖写像、境界との可換性と合成則、整数次数への零拡張。 |
| `Identity` / `Identity.Coefficients` | 恒等連続写像が鎖・余鎖・コホモロジーの恒等写像を誘導すること。 |
| `Maps.Coefficients` | 空間に関して反変、係数に関して共変な余鎖写像・コホモロジー写像と、生成元での評価公式。 |
| `Maps.Coefficients.Integer.At` | 空間と係数の写像について、整数次数と非負次数のコホモロジー比較が満たす自然性。 |
| `Maps.Composition.Coefficients` | 連続写像の合成が誘導するコホモロジー写像の合成則。 |
| `Homotopy` / `Coefficients` | cylinder のアフィン prism 鎖から構成する鎖ホモトピーと、任意係数でのホモトピー不変性。 |
| `Homotopy.Homology.At` | 整数次数の特異ホモロジーにおけるホモトピー不変性。 |
| `Equivalence.With` | 位相空間のホモトピー同値から得るコホモロジーの加群同型。 |
| `Relative` / `Injection` | 部分空間からの単射な鎖写像、その像による商、相対鎖の短完全列。 |
| `Relative.Homology` / `LongExact` | 相対ホモロジー、接続写像、その前後の合成の零性と長完全列の完全性。 |
| `Relative.Split` / `Relative.With.PairSequence` | 次数ごとの包含の分裂と余鎖の短完全列、相対コホモロジー長完全列。 |
| `Relative.With.Vanishing` | 相対余鎖と部分空間の鎖上で零になる全体の余鎖との加群同型。 |
| `Relative.With` | 商鎖複体から係数加群への Hom と相対コホモロジー。 |
| `Relative.Support` | 部分空間に値を持つ特異単体の持ち上げと、連続写像の全鎖が部分空間の鎖の像に入ること。 |
| `Relative.Equivalence.Over.On` | 対の二つの連続写像と逆合成のホモトピーから得る、相対ホモロジー・任意係数コホモロジーの同型。 |
| `Relative.Identity` / `Maps.Over.Composition` | 相対鎖の恒等則・合成則と、ホモロジー・任意係数コホモロジーでの関手性。 |
| `Relative.Maps.Over.Homotopy.On` | 部分空間を保つホモトピーの prism が誘導する相対鎖ホモトピーと、ホモロジー・任意係数コホモロジーの誘導写像の一致。 |
| `Relative.Maps.Over.On` / `Integer.With` / `Naturality` | 対の連続写像による相対鎖・余鎖の写像と、包含・商・接続写像の自然性。 |
| `Coefficients.Sequence.On` / `Bockstein` | 係数短完全列が誘導する余鎖の短完全列、Bockstein 接続写像と完全性。 |
| `OrderedTuples` / `ConeBoundary` / `SquareZero` | 頂点列上の自由鎖、交代境界と複体、頂点を先頭に加える cone の境界公式。 |
| `OrderedTuples.Prism` | 二つの頂点写像の間の prism、境界公式、前合成・後合成に関する自然性。 |
| `OrderedTuples.Subdivision` / `Homotopy` / `Natural` | 各頂点列に指定した中心を使う細分、境界との可換性、恒等写像との鎖ホモトピー、中心を保つ写像に関する自然性。 |
| `CylinderChains` | 頂点列を cylinder 内のアフィン特異鎖へ送る鎖写像、普遍的 prism、面への制限との整合性。 |
| `SimplicialChains.On` | 面の恒等式を満たす任意の次数付き集合からの自由鎖複体と、その関手性。 |
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

[利用例](../../examples/cohomology/README.md) は、代表余鎖の評価、両微分の二乗の零性、増大、係数付き誘導写像、相対接続写像と空空間の計算を別パッケージで検査する。
[特異理論の一覧](../README.md) と[具体的な空間の計算](../../examples/finite_models/README.md) に、切除・有限モデルとの比較・積とその利用例をまとめている。

```sh
cargo build -p cli
target/debug/cli libs/topology/singular/cohomology --module singular_cohomology --diagnostics compact
target/debug/cli libs/topology/examples/cohomology --module cohomology_models --diagnostics compact
```

workspace 共通の `libs/refcache/` を利用する。
複体を別名で再公開した場合も、module の具体化は捕捉した型引数を保持する。
単独の検査例は [G15](../../../../_plans/gaps.md#g15) にある。

`OverRing.With.integerCoefficients` は係数加群の加法群に標準の整数作用を入れる。
環上の余鎖・コホモロジーの台集合は、その整数係数加群を使った通常の理論と共有する。

相対鎖と余鎖の誘導写像は `Relative.Maps.Over.On.Integer` とその `With` に置く。
長完全列との可換性、比較定理は、それぞれの `Naturality` に分ける。
