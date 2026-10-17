# 特異鎖の比較に用いる代数

特異鎖の商、直和、係数加群への Hom とそのホモロジーを比較する。
相対鎖の次数ごとの射影性と、対の可換正方形・切除の自然性もまとめる。

- `Algebra.NeighborhoodMapping` は、実際の近傍変形収縮と切除を組み合わせた相対群の比較について自然性を示す。
- `Algebra.RelativeRepresentative` と `CellLiftStep` は、射影的な相対群の基本類を持ち上げ、境界が指定の鎖と一致するように代表を補正する。
- `Algebra.SumTo`、`SumSequence`、`SumCochains` は、直和の鎖と Hom の積を比較する。
- `Algebra.PointRelative.Positive` は、正次数で一点を相対化した射影の誘導写像が同型になることを示す。
- `Algebra.IntegerCoordinates` は、生成元を保つ写像と整数座標の整合性を与える。
  `PointClass` は実際の定数特異単体の零次ホモロジー類と、その連続写像に関する自然性を公開する。
- `Algebra.Refinement.ext` と `forgetEquality` は、部分型の等式と元の台集合の等式を相互に移す。
