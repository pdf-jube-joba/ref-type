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

## 未完了の比較

一点コンパクト化上へ個々の束が延長されることを要求せず、元の空間上の任意の束とコンパクト集合の外での同型を出発点とする三つ組の群との比較は、まだ実装していない。
上記の三つ組群との比較だけでは、この追加の比較の完了とはしない。
必要なコンパクト近傍の存在は `On.Neighborhood` にある。
その近傍への束の制限、相対三つ組の構成、零延長、近傍の選択独立性を接続する作業が残る。
このため K10 全体は実装途中である。

通常検査はリポジトリルートで実行する。

```sh
source /workspace/ref-type-env.sh && cargo build -p cli --release --locked
python3 scripts/check_all.py --initial-memory-mib 10240 --memory-mib 10240
```
