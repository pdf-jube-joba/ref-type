# G04 の実装状態

基点は `ed1af945bfdfdc1849bf1919317e3ce422b1ac1f`、ブランチは `math/g04-collars-gluing`、保存用 Draft は [PR #73](https://github.com/pdf-jube-joba/ref-type/pull/73) である。
G04 全体は未完了である。
定理の範囲は [manifold_gluing の README](../libs/geometry/manifold_gluing/README.md)、検査結果と数学ソースの対応は [検査記録](../benchmarks/records/manifold-gluing/README.md) にある。

## 大域 collar に向けた構成

`LocalPush.On` は半空間を保つ座標式 \(x+tq b_q(x)e_\nu\) を構成する。
`Bounds` は \(0\le t\le1\) で移動量が \(q\) 以下であり、半径 \(2q\) の bump の台を半径 \(4q\) のチャート内の球に収めると移動後もチャート内に留まることを証明する。
`GlobalPush.On.In` はこの式を台の外で恒等にし、多様体全体の滑らかな写像へ延長する。
内点を内点に保ち、像が境界にある場合は元の点を固定する。

`PushHomotopy` は同じ時間を使う有限合成と開被覆による大域化を構成する。
`BoundaryInclusion` は G03 の境界多様体から元の多様体への滑らかな包含を構成する。
`InwardNeighborhood` はコンパクトな境界について、時間零で包含に一致し、正の時刻には内点に入る滑らかな写像 \(\partial M\times[0,1)\to M\) の存在を証明する。
この写像の単射性、開いた像、その像への滑らかな逆写像はまだ構成していない。

`LocalPush.On.Derivative` は時間零での微分の明示式を与える。
`InitialJet` は任意の滑らかな初期恒等ホモトピーの空間方向の微分が恒等であることを、半空間上の微分の一意性から証明する。
`ProductDifferential`、`PairDifferential`、`SmoothChainRule` は積の接ベクトルの分解、対の微分、連鎖律を与える。
`HomotopyVelocity` は座標に依存しない初期速度を接ベクトルとして構成し、内向き性を証明する。
`HomotopyCompositionVelocity` は合成の初期速度が二つの速度の和になることを証明する。
`ConeAddition` は内向き速度の和と、厳密な内向き性の保存を証明する。
`TransverseHomotopy` は局所的な横断性をコンパクトな境界全体へ大域化し、`GlobalPush.existsTransverse` は実際の bump による局所族を適用してその存在を証明する。

次の段階は、`InwardNeighborhood` の境界への制限の初期微分が同型であること、半空間を保つ局所逆写像、局所 collar の証明である。
`CompactStrip.On.existsUniform` はコンパクトな境界上の単射性を一様化する補題として利用できる。
局所逆写像の定義域の被覆にも tube lemma を適用し、像が開で逆写像が滑らかになる共通の幅を選ぶ必要がある。

既存の `differential_equations.Euclidean.Smooth.Regularity` は一つの解の時間変数についての滑らかさである。
初期値を含めた滑らかな flow の存在はこの構成の入力ではない。

## その他の残件

- 指定された collar に一致する相対的な大域延長と、二つの滑らかな collar の選択比較。
  `TopologicalCollar` の相対補題は、既存の位相的 collar の像を指定された開近傍に収める時間近傍の存在である。
- 境界の任意の微分同相に沿う商についての、符号付き collar チャートの滑らかなアトラス、Hausdorff 性、第二可算性、および一般の double。
  `Seam.Embedded` は同値類の分類、`Seam.Map` は互換な写像の位相的な降下、`HalfSpaceDouble` は半空間の局所模型を構成する。
- 積多様体に対する、角の近傍に局在した丸めと元の積との比較。
  `RoundedCorner` は自由な座標を伴う \(u>0,uv\ge\varepsilon\) の局所模型である。
- 大域的な向きと境界向きの規約、および向き付き貼り合わせの符号。
  `Reflection.Orientation` は法線反射の行列式 \(-1\) と最高次交代形式の符号反転を証明する。
- collar を保つ滑らかな写像を、貼り合わせた滑らかな多様体の写像へ降下させる定理。

最初の全体検査の数学ソースは `8b314683331496400104d0de8cb29f7c0a500f90` であり、11,767 対象すべてが accepted である。
大域押し込みの数学ソース `827da4f87550e523586407535211346eb2126e24` の全ローカル検査では 177 module を新規検査し、通常の全体検査では 11,884 対象すべてが accepted である。
対応する検査記録は [global](../benchmarks/records/manifold-gluing/global/README.md) にある。
