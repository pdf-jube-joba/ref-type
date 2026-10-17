# 特異コホモロジーの具体例

有限鎖複体の計算と、実際の位相空間から定まる特異コホモロジーへの比較をまとめる。
係数 \(A\) は整数上の加群の束として渡す。
コチェインの値、商への射影、係数変換を明示し、生成元の積や連結準同型を同じ代表元で追跡する。

| 対象 | 名前空間 | 内容 |
| --- | --- | --- |
| 有限グラフ | Graph.On.With | 全域森に沿った原始関数と、成分・弦による有限コチェインの座標 |
| グラフの実現 | Graph.On.Geometry | 各辺の三分割を真の有限単体複体として実現し、アフィン特異単体へ写す |
| グラフの群 | Graph.On.Geometry.Coefficients.Singular | 成分数 \(c\)、弦の数 \(k=e-v+c\) に対する \(H^0\cong A^c\)、\(H^1\cong A^k\)、高次の消滅 |
| 円の有限モデル | Circle | 次数 \(0,1\) にそれぞれ階数 \(1\) を持つ零微分の整数鎖複体 |
| 円の比較 | Circle.Geometry.FiniteComparison | ユークリッド単位円の特異鎖複体との比較 |
| 円の普遍係数列 | Circle.Geometry.UniversalCoefficient | 証明済みの有限比較から、任意の整数加群係数に対する実際の特異理論の短完全列を得る |
| 円のループ | Circle.Geometry.Loop.Primitive | 上半円を二乗して得られる閉じた特異辺と、その原始的なホモロジー類 |
| 円の評価 | Circle.Geometry.Evaluation | 閉じたコチェインをこのループで評価する同型 \(H^1(S^1;A)\cong A\) |
| トーラスの群 | Torus.Geometry.Comparison | 実際の積 \(S^1\times S^1\) を円の有限モデルのテンソル積と比較する |
| トーラスの基底 | Torus.Geometry.Ring.Basis / UnitBasis | 次数 \(1\) の二つの射影類の基底、および次数 \(0\) の単位生成元 |
| トーラスの積と反転 | Torus.Geometry.Ring | 二つの射影から得る次数 \(1\) の類、そのカップ積、因子交換の作用 |
| 実射影平面の空間 | ProjectivePlane.Geometry | 実際の \(S^2/(x\sim -x)\)、半球による商、円板の貼り付けの相互比較 |
| 実射影平面の有限モデル | ProjectivePlane.With | 二頂点・三辺・二三角形のコチェイン複体 |
| 整数係数 | ProjectivePlane.Integral | \(H^1=0\)、\(H^2\cong\mathbb Z/2\) の有限計算 |
| 二元体係数 | ProjectivePlane.ModTwo | 次数 \(1\) の類 \(u\) と \(u^2\ne0\) の有限計算 |
| 実射影平面の群 | ProjectivePlane.Geometry.Cohomology | 任意の整数加群係数で、次数 \(1\) は倍写像の核、次数 \(2\) はその余核、高次は零 |
| 実際の整数・二元体係数 | ProjectivePlane.Geometry.Integral / ModTwo | 商空間自身の特異コホモロジー、生成元、その非零性 |
| 三角形への制限 | ProjectivePlane.Geometry.Restriction | 実際の二つの特異三角形への制限、円のループによる次数 \(1\) の検出、カップ積との整合性 |
| 実射影平面の Bockstein | ProjectivePlane.Geometry.Bockstein | 実際の \(u\) を整数次数 \(2\) の非零生成元へ送る連結準同型 |
| 有限モデルの Bockstein | ProjectivePlane.Bockstein.Finite | \(0\to\mathbb Z\xrightarrow{2}\mathbb Z\to\mathbb F_2\to0\) による実際のコチェイン連結準同型の値 |

## 代表元と符号

Surface は頂点、辺、三角形と三つの面写像から半単体的鎖複体を作る。
コボーダリーは、辺では終点の値から始点の値を引き、三角形では後辺から対角辺を引いて前辺を加える。
Surface.On.Simplicial.Coefficients は、自由鎖上の線形写像とこれらの点ごとのコチェインを比較する。

実射影平面の辺を \(a,b,d\)、三角形を \(P,Q\) と書くと、
\[
\partial P=a-d+b,\qquad \partial Q=a-b+d.
\]
二元体係数のコチェイン \(u=(1,0,1)\) に対し、Alexander–Whitney の式は \(u^2=(0,1)\) を与える。
同じ値を整数に持ち上げるとコボーダリーは \((0,2)\) となり、Bockstein の値は整数次数 \(2\) の生成元 \((0,1)\) の類になる。

トーラスでは二つの射影から得る類を \(a,b\) とし、向きを \(a\smile b\) で指定する。
Ring の平方消滅と次数付き可換性は
\[
a^2=b^2=0,\qquad b\smile a=-a\smile b
\]
を与える。
因子交換は \(a,b\) を交換するため、次数 \(2\) のこの類に符号 \(-1\) で作用する。

## 比較の入口

Graph.On.Geometry.Indexing は頂点の整数ラベル、その単射性、各分割辺の順序、端点対の単射性を与える。
singular_simplicial の実現との比較は、このデータから作った単体複体に適用する。

ProjectivePlane.Geometry.Attachment.Comparison.Pair は、実際の貼り付け円板の内部と基底の補集合との同相、および基底を固定する穿孔円板の放射変形を与える。
その相対ホモロジー・相対コホモロジーの比較は、特徴写像自身が誘導する写像である。

Two.Quotient は整数の巡回商と二元体との同型を与える。
Two.Quotient.Sequence は上記の係数短完全列を構成し、Surface.On.Simplicial.Sequence はそれを自由コチェインの短完全列へ移す。

ProjectivePlane.Geometry.CoefficientSequence は、特異コチェインから有限コチェインへの制限と係数の短完全列から得られる連結準同型が可換であることを示す。
この自然性により、有限モデルでの Bockstein の値を実際の商空間の生成元と同定する。
