# コンパクト台付き K 理論

入口は `compact_support_k.Support`。
局所コンパクト Hausdorff 空間の一点コンパクト化を実際に構成し、K09 の整数次数群を適用する。

| API | 内容 |
| --- | --- |
| `OnePoint` | 一点を追加する集合、開集合の条件、包含の連続性 |
| `OnePoint.Compactness` / `Separation` | コンパクト性と Hausdorff 性 |
| `OnePoint.Outside` | 元の空間と無限遠点の補空間との同相 |
| `On.At` | \(K_c^j(X)=\widetilde K^j(X^+)\) と2周期同型 |
| `Proper.With` / `On.Pullback.At` | proper map の無限遠点への延長、引き戻し、加法性と零元 |
| `ProperIdentity` / `ProperComposition` | proper 性と延長の恒等・合成則 |
| `Homeomorphic` | 同相による proper 性と局所コンパクト性の移送 |
| `On.Symbols` | コンパクト化上の三つ組の群と被約零次数群の比較、両側逆と加法性 |
| `On.Symbols.Supported.With` | コンパクトな台、台の拡大、台の外の実際の束同型 |
| `On.Symbols.Complexes` | 全ての零次数類の二項束複体による表示 |
| `On.Symbols.EqualityCriterion` | 直和・合成・全体の同型・ホモトピーの関係から生成される同値関係と等式との同値 |
| `On.Symbols.Stabilize` | 対角三つ組との直和による安定化 |
| `OpenPart.Collapse` / `On.Open.At` | 開部分空間の外を無限遠点へ送る連続写像と零延長 |
| `ClosedPair` | コンパクト閉対の商と補空間の一点コンパクト化との同相 |
| `ClosedPair.At` / `Triples` | 相対群と補空間のコンパクト台付き群との比較 |
| `ClosedPair.Excision.At` | 閉部分空間に含まれる開集合の切除と両側逆 |
| `On.Product.At` / `Coordinates` | 整数次数の外積、双加法性、出力空間と通常の積空間との明示的な同相 |
| `Disk.At` | 円板・球面束の相対群と開円板束のコンパクト台付き群との比較 |
| `On.Neighborhood` | コンパクト集合を含む開集合とコンパクトな包絡の存在 |

`OnePoint.Open` は、元の空間への引き戻しが開であり、無限遠点を含むならその引き戻しの補集合がコンパクトであることを表す。
コンパクト性の証明は、無限遠点を覆う一枚を取り、そのコンパクトな補集合に対する有限部分被覆を加える。
Hausdorff 性は、有限点同士には元の分離性を、有限点と無限遠点にはコンパクト近傍を用いる。

`On.Symbols` の束は一点コンパクト化上の束で、三つ組の同型は最初は無限遠点上で与える。
B09 の同型延長によって近傍上の同型を得て、その近傍の補集合をコンパクトな台とする。
`Supported.With.Outside` は、任意のより大きいコンパクト台の補空間へ同型を引き戻す。
`Complexes.TwoTerm` はこの三つ組と、順・逆の束写像の全体への延長と有限埋め込みを持つ。
`Supported.Complex.With.differential` は全体で定義された微分であり、`inverseAtInfinity` と `forwardEquation` が同じ微分の台の外での可逆性を与える。

`On.Open.At` の定義域は元の空間の開部分集合の部分空間位相による群である。
`Coordinates` がコンパクト化内の開部分空間表示との同相を与え、その延長と collapse を合成する。
`RepresentedAt` はこの座標変更前の表示である。
外積も、積コンパクト化の二軸の補空間と通常の \(X\times Y\) を `On.Product.Coordinates.homeomorphism` で比較する。

`Disk` には射影表示を渡す。
一般の束には `relative_k_theory.Relative.BundleDisk.existence` で表示 `r` を選び、`r.presentation` を渡せる。
元の束の単位円板との同相と球面条件は `BundleDisk.With[r].OriginalUnit` が与える。

最小利用例は [Examples.ref](src/Support/Examples.ref) にある。
有限一点空間の各整数次数群と、ランク0・1の自明円板束を実体化する。

```ref
\import std.Data[].Nat[] \as N;
\import compact_support_k.Support[].Examples[].TrivialDisk[n := N.Nat^::zero] \as Zero;
\definition zeroDisk: \Set := Zero.Interior;
```

## 元の空間上の一般の束三つ組

`On.BundleModel.From` は、底空間の位相が指定の位相と一致する任意の局所自明複素束を受け取る。
`On.BundleTriples[F, G, firstModel, secondModel].Supported[K, compactK].With[alpha]` は、元の空間上の二つの束と、コンパクト集合 \(K\) の外での束同型を入力とする。
個々の束を一点コンパクト化へ延長するデータは要求しない。

`With.In[n]` は、\(K\subset U\subset L\) を満たす開集合 \(U\) とコンパクト集合 \(L\) を選び、束を \(L\) へ制限して対 \((L,L\setminus U)\) の相対三つ組を作る。
`On.Localization.collapse` による引き戻しで、この相対類を \(X^+\) 上へ零延長する。
`With.Choices.equation` は二つの近傍の開部分の共通部分とコンパクト部分の和集合を使って選択独立性を示す。
有限射影表示および負の束の補助束の選択独立性は `relative_k_theory.Relative.Pair.BundleTriples` が保証する。

`With.value` は近傍に依存しないコンパクト台付き K 類、`With.symbol` は既存の小さいシンボル群の元である。
`With.comparison` はこの個々の類の一致を示し、`finiteRepresentation` はコンパクト化上の三つ組による代表を与える。
`On.Symbols.Supported.With.Raw.equation` は、従来のシンボルを元の空間上の三つ組へ制限してこの構成に入力すると元の類が回収されることを示す。
`On.Symbols.RawRepresentatives.existence` は全ての類にそのような元の空間上の代表が存在することを示す。
コンパクト化上の代表の等式は `On.Symbols.EqualityCriterion` で判定できる。

`On.BundleTriples.To.Supported.With.equation` は、台の和の外で可換な束同型による表示変更を許す。
`With.Enlarge.comparison` は拡大後の台の外への同型の制限を構成し、`equation` と `symbolEquation` は元の類とシンボルに一致することを示す。
`On.Pullback.BundleTriples.Supported.With.naturality` は、この一般の三つ組の構成と proper 引き戻しが可換であることを示す。

`Examples.Raw` は、有限一点空間上の自明束を入力し、空の近傍と空間全体を近傍に選んだ値の一致を実体化する。

## 元の空間上の三つ組の関係表示

`On.Triples.Group` の生成元は元の空間上の台付き三つ組である。
`Relation` は大域同型、可換な束同型、直和、同型の合成、台の外での連続な同型のホモトピーからなる。
`Equivalent` はこれらの関係と可換群の演算から生成する同値関係であり、K 類の等しさを定義に使わない。
`Triples.Input` は任意の局所自明束を座標模型へ移し、選択によらない群の元を与える。
`InputSum`、`InputComposition`、`Input.Homotopy` は元の束の側の幾何学的関係を保存する。
`DirectSumInput.With.Stabilization` は大域同型となる対角三つ組を足す安定化を与える。

`Group.ToK` はコンパクト近傍への制限と零延長による加法写像である。
逆比較では、コンパクトな局所模型の負の束に補助束を足し、境界上の枠を使って商空間へ降下させる。
`Triples.Normalize` は、この降下束の引き戻しと元の束を、局所の安定同型と台の外の同型の貼り合わせで比較する。
`Group.Comparison` と `Group.EqualityCriterion` の最終検査は進行中である。

## 一般の有限複体

`On.FiniteComplexes.Complex` は任意の有限長の束と連続な微分の列を受け取る。
基盤の `bundle_operations.Operations.Over.Models.Chains.Data` は長さに上限を置かず、`fold` が偶奇和と二つの微分を構成する。
各束は局所自明性を保持した座標模型であり、階数は点ごとに変わってよい。
`Models.From.existence` が任意の局所自明束と座標模型との大域同型を与える。

`FiniteComplexes.Of.Supported` は、コンパクト集合の外での完全性を入力とする。
`In[w]` はコンパクトな境界上で連続な縮約を構成し、正規化した偶奇和の同型から相対三つ組と零延長した K 類を作る。
`In.Choices` は縮約の選択独立性、`Choices` はコンパクト近傍の選択独立性を証明する。
`Enlarge.With.equation` は台を拡大しても同じ類になることを示す。
`Global.equation` は全体で完全な有限複体の類が零であることを示す。

`FiniteComplexes.Sum.With` には、実際の偶奇和の束同型と微分との可換性を渡す。
`Supported.equation` が直和の K 類の加法性を、`Supported.Stabilization.equation` が全体で完全な複体を加える安定化を与える。
`FiniteComplexes.Homotopy.With.Supported.In.With` の入力は、共通のコンパクト近傍の境界上の連続な微分の族である。
族は各時刻で完全であり、端点の微分は二つの有限複体の偶奇和の微分に一致する。
端点の偶奇和の束は、指定した大域同型で同一視する。
`equation` はコンパクトな円柱上の縮約から端点の正規化同型のホモトピーを作り、二つの K 類の一致を証明する。

`Of.Supported.Representatives` は有限複体の類の元の空間上の三つ組による形式表示と、生成された幾何学的関係による等式判定を接続する。
この接続の最終検査は進行中である。
三つの非零の項を持つ零微分複体の最小利用例は `Examples.ThreeTerm` にある。

通常検査はリポジトリルートで実行する。

```sh
source /workspace/ref-type-env.sh && cargo build -p cli --release --locked
python3 scripts/check_all.py --initial-memory-mib 10240 --memory-mib 10240
```
