# Čech 比較の鎖代数

`Algebra[R, ring].ProjectiveQuasi[C, D, f].equivalenceExists` は、非負次数の鎖写像 \(f:C\to D\) の前向き写像を保った鎖ホモトピー同値の存在を与える。
仮定は両複体の各項の射影性、各次数の全射性、および核内のサイクルが核内で境界になることである。
次数ごとの切断から核を射影加群の直和因子とし、零加群の射影分解の比較ホモトピーで核を収縮する。
`Algebra.Concentrated[C]` は \(q=0\) の行に \(C\) を置く二重複体と、元の複体との零行の同型を与える。

`PartialCone.On[X]` は、頂点を既に含むかどうかの判定と、含まない単体への頂点の付加を扱う。
`Cone` は面との関係を含むデータであり、`With[cone].homotopy` は自由整数鎖への延長である。
`Positive.cycle` と `Zero.cycle` は、正次数のサイクルと零次の増大写像の核を実際に埋める。
`Coproduct.On[Index, objects]` は半単体的対象の族の直和を構成し、各成分の増大鎖収縮から直和の収縮と増大写像の切断を作る。

`CarrierModel.On[C, D]` は \(\operatorname{Hom}(C_n,D_z)\) の部分加群族を模型にする。
標的の微分との後合成、始域の境界との前合成について閉じていれば、二つの作用素の二乗零と可換性が従う。
`With[S, closed].Diagonal[delta, carried].cells` は、その部分加群に支えを持つ実際の鎖写像から閉対角を与える。
有限単体複体への適用では、星被覆の Čech 二重複体の行を最小頂点の付加で、列を共通部分の可縮性で解消し、担体を保つホモトピーで二つの増大写像をアフィン比較と同定する。
具体的な被覆・担体と比較の組み立ては `singular_simplicial.Complex.On.Cech` にある。

`Algebra.Restriction` は整数次数の複体・写像を非負次数へ制限する。
負次数の項が零なら、ホモトピーと同値も制限できる。
`RestrictionZeroExtension` は零拡張を制限した複体と元の複体の同型を与える。
`TensorEquivalence` は二つの非負次数の鎖ホモトピー同値から、テンソル全複体の同値を作る。

パッケージ全体と比較橋の検査例は次のとおりである。

```sh
cargo run -p cli -- libs/topology/singular_cech --cache-dir libs/refcache
cargo run -p cli -- libs/topology/singular_cech --module singular_cech.Algebra.ProjectiveQuasi.Contracted.Equivalence --module-only --cache-dir libs/refcache
```
