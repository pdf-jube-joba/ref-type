# 有限モデルと係数の比較

有限自由整数鎖複体と特異鎖複体の鎖ホモトピー同値から、任意の係数加群に対する普遍係数の短完全列を得る。
有限モデルは `homological_algebra.Finite.Bounded.Complex` であり、各次数の有限性、境界の二乗零、有界性を保持する。

| API | 内容 |
| --- | --- |
| `Integer.Middle.exact` | 中央の加群同型による短完全列の移送。 |
| `Integer.CoefficientTensor.On.map` | 整数次数付き鎖写像を係数とのテンソル積へ送る。 |
| `Integer.CoefficientTensor.Homotopy.With.homotopy` | テンソル積へ移した鎖ホモトピー。 |
| `Integer.CoefficientEquivalence.With.equivalence` | 任意係数とのテンソル積が保持する鎖ホモトピー同値。 |
| `Integer.ProjectiveCone.On.equivalenceExists` | 下に有界な射影的複体の擬同型から、同じ前向き写像を持つ鎖ホモトピー同値を構成。 |
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

`Integer.Product.Compared.At.kunneth` は有限自由整数モデルのテンソル積の比較から積空間の整数 Künneth 短完全列を返す。
`Field.Product.Compared.At.kunneth` は体上の有界有限モデルの余鎖比較から、コホモロジーのテンソル和と積空間のコホモロジーとの同型を返す。
両者は有限モデルの条件と係数の条件を引数の型に保持する。
