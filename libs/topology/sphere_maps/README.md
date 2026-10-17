# 球面の写像

既存のユークリッド球面上に連続写像を構成し、特異コホモロジー上の作用を計算する。

`Circle.Coordinates` は二次元ユークリッド球面と単位複素数の同相を与える。
`Circle.Powers.map` は任意の整数 \(k\) の円周写像で、負の整数では複素共役を用いる。
`Circle.Powers.Actions.integer` は任意の整数加群係数で一次コホモロジーの作用が \(k\) 倍になることを示し、`Degree.integer` は整数係数の向き付き生成元から次数 \(k\) を得る。
`Actions.Signed.integer` と `Actions.Reduced.integer` は整数次数の通常および被約コホモロジーでも同じ作用を与え、`Actions.DegreeZero` は零次の作用を扱う。

`Circle.Powers.square` は座標で \((x,y)\mapsto(x^2-y^2,2xy)\) となる連続写像である。
`Circle.Roots` は平方根の存在を、`Circle.Powers.Antipodal.Fibers` は平方写像のファイバーが反対点対であることを示す。
`Circle.Quotient.homeomorphism` は実際の平方写像から \(S^1/(x\sim -x)\cong S^1\) を構成する。

`Reflection` は最初の座標の反転と残りの座標の反転を構成する。
`Hemispheres` は二つの半球の入れ替えに伴う Mayer–Vietoris の符号を、実際の特異鎖写像と短完全列の自然性から計算する。
`Hemispheres.Homology.Whole.head` は最初の座標の反転が最高次ホモロジー上で符号を反転することを示す。
`Antipodal.degree` は正次元の球面 \(S^{n+1}\) 上の反対点写像の次数が \((-1)^{n+2}\) であることを示す。
`IntegerPowers.power` はこの式で用いる整数の自然数冪である。

`ZeroAntipodal.With` は零次コホモロジーの二つの点での評価を入れ替える作用と、その差の符号反転を任意係数で計算する。

`ZeroAntipodal.With.Reduced.law` は被約零次コホモロジー上で反対点写像が \(-1\) 倍になることを、定数コチェインが増大写像の余境界であることから示す。
