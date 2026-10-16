# 特異理論の切除と開被覆

切除の条件 \(\overline Z\subseteq\operatorname{int}_X A\) から、\(\operatorname{int}_X A\) と \(X\setminus\overline Z\) の開被覆を構成する。

| module | 内容 |
| --- | --- |
| `Excision.Over.Pair` / `On` | 切除する部分集合と閉包の条件、二要素の開被覆、各要素の包含関係。 |
| `On.Chains.Degree` | 除去前後の小相対鎖と、部分空間の像に入らない単体上の自由加群との同型。 |
| `Degree.Range` / `Complement` | 除去後への小単体の持ち上げ、補集合の生成元の全単射と自由加群の同型。 |
| `Chains.Preservation` / `Mapping` | 部分空間の鎖の像の保存と、除去後の対から元の対への小相対鎖写像。 |
| `Degree.Comparison` / `Chains.Isomorphism` | 小相対鎖の切除写像の鎖同型、ホモロジーと任意係数コホモロジーの同型。 |
| `Chains.Naturality` / `Homology` / `Cohomology` | 小相対鎖から通常の相対鎖への比較の自然性と、元の切除写像が誘導する群同型。 |
| `MayerVietoris.Over.On.Chains` | 二つの開集合の鎖の直和、符号付き包含、和による小鎖への全射と短完全列。 |
| `Chains.With` | 任意係数で双対化した余鎖の短完全列と長完全列。 |
| `Chains.Homology` / `Cohomology` | 小鎖との比較と直和の比較を経た、通常の特異理論の Mayer–Vietoris 列。 |

Mayer–Vietoris の交わりは、左の部分空間を右の集合で再び制限した部分空間として構成する。
ホモロジーの包含は \((i_*,-j_*)\)、次の写像は両包含の和である。
余鎖の制限は両開集合への制限、次の写像は交わり上の制限の差である。
各次数の `exactAtSum`、`exactAtWhole`、`exactAtIntersection` は、写像と像・核の一致を含む `module_theory.ExactPair.Sequence` を返す。
