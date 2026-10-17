# 有限モデルと係数の比較

有限自由整数鎖複体と特異鎖複体の鎖ホモトピー同値から、任意の係数加群に対する普遍係数の短完全列を得る。
有限モデルは `homological_algebra.Finite.Bounded.Complex` であり、各次数の有限性、境界の二乗零、有界性を保持する。

| API | 内容 |
| --- | --- |
| `Integer.Middle.exact` | 中央の加群同型による短完全列の移送。 |
| `Integer.CoefficientTensor.On.map` | 整数次数付き鎖写像を係数とのテンソル積へ送る。 |
| `Integer.CoefficientTensor.Homotopy.With.homotopy` | テンソル積へ移した鎖ホモトピー。 |
| `Integer.CoefficientEquivalence.With.equivalence` | 任意係数とのテンソル積が保持する鎖ホモトピー同値。 |
| `Integer.HomZero.At.isomorphism` | 微分が零の非負次数複体について、任意係数のコホモロジーと各項の Hom 加群を同定。 |
| `Integer.HomTransport.With.isomorphism` | 台の加群同型から、任意係数への Hom 加群の同型を前合成で構成。 |
| `Integer.ProjectiveCone.On.equivalenceExists` | 下に有界な射影的複体の擬同型から、同じ前向き写像を持つ鎖ホモトピー同値を構成。 |
| `Integer.Attachment.On.Kernel` / `Cokernel` | 接続写像が 2 倍となる完全列から、任意係数の 2 倍写像の核と余核を取り出す。 |
| `Integer.Units.classification` | 積が 1 となる整数は、それぞれ 1 または −1 であることを示す。 |
| `Integer.Orientation.Normalize.existence` | 最上次の反転作用を持つ自己同相を使い、二つの向き付き生成元を結ぶ同相写像の存在を示す。 |
| `Integer.Finite.Compared.At` | 有限モデルから特異理論への普遍係数比較。 |

`Finite` の `model` は有限自由整数複体を指定する。
`Compared` の `comparison` は、その複体から対象空間の特異鎖複体への鎖ホモトピー同値を指定する。
この比較を Hom とテンソル積へ移して、それぞれの誘導同型と有限モデルの普遍係数列を合成する。

`universalCoefficient` の中央項は対象空間の特異コホモロジーであり、端は有限モデルのホモロジーに対する Ext¹ と Hom である。
`homologyUniversalCoefficient` の中央項は係数付き特異ホモロジーであり、端は有限モデルのホモロジーのテンソル積と Tor₁ である。
`homologyIsomorphism` は両モデルの整数ホモロジーを同定する。
`cohomologyIsomorphism` と `coefficientHomologyIsomorphism` は任意係数の比較同型を公開する。
`splitting` は有限整数行列の分裂から得られるが、自然な写像として扱うのは短完全列とその端の写像である。

`Integer.Finite.Groups.CohomologyCompared` と `HomologyCompared` は、証明された群同型から直接、同じ短完全列を移す。
骨格の長完全列から比較同型を構成する場合にも、この入口を使える。

`ProjectiveCone` は整数次数の二つの複体を受け取り、非負次数の各項の射影性と負次数の消滅を保つ。
擬同型の写像錐を非負次数へ制限すると、零加群の射影的分解になる。
分解の比較ホモトピーからこの錐の収縮を得て、その行列成分を逆写像と両側のホモトピーにする。
前向き写像は与えた実際の鎖写像と一致し、逆写像の選択は存在命題の内部で行う。

`HomZero` は非負次数の複体と係数加群を受け取り、微分の消滅証明からコホモロジーの座標を取り出す。
`At.onClass` により、同型の前向き写像は閉余鎖の類を元の余鎖へ送る。

`Integer.Product.Compared.At.kunneth` は有限自由整数モデルのテンソル積の比較から積空間の整数 Künneth 短完全列を返す。
`Field.Product.Compared.At.kunneth` は体上の有界有限モデルの余鎖比較から、コホモロジーのテンソル和と積空間のコホモロジーとの同型を返す。
両者は有限モデルの条件と係数の条件を引数の型に保持する。

積の各因子について比較がある場合には、次の入口で実際の空間の群を端点にできる。

| API | 入力と結果 |
| --- | --- |
| `Integer.Product.Factors.nativeEquivalence` | 各有限整数模型の非負次数部分から各因子の特異鎖への鎖ホモトピー同値を受け取り、テンソル積の全複体から積空間の特異鎖への同値を構成する。 |
| `Integer.Product.Compared.Factors.At.kunneth` | 各因子の整数次数付き比較を使い、両端を実際の因子の整数ホモロジーのテンソル和と Tor₁ の和へ移す。 |
| `Integer.Product.Compared.Factors.At.Component.Resolution.resolution` | 実際の第一因子のホモロジーに対する射影的分解。有限模型の分解の増大写像を比較同型で移して構成する。 |
| `Integer.Product.Compared.Factors.At.Splitting.isomorphism` | 実際の端点の直和から積空間のホモロジーへの選択された分裂同型。 |
| `Field.IntegralModel` | 有界有限自由整数模型 (P) から、任意の体 (K) に対する \(\operatorname{Hom}_{\mathbb Z}(P,K)\) の有限座標余鎖模型を構成する。 |
| `Field.IntegralProduct.Factors.At.kunneth` | 各整数模型の非負部分と実際の因子との鎖比較から、実際の \(H^*(X;K)\)、\(H^*(Y;K)\) のテンソル和と \(H^*(X\times Y;K)\) の同型を構成する。 |

`Field.IntegralProduct` の積全体の比較は、因子の比較をテンソル積へ移し、Eilenberg–Zilber 同値の逆と合成して得る。
整数鎖に対する体係数の Hom と体上のテンソル積の接続には `singular_tensor_dual.Over.Mixed.On` を用いる。
`IntegralModel` の微分は整数境界との前合成を座標同型で共役したものであり、二乗零と有界性は元の模型から証明する。
