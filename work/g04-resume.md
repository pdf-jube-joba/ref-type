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

`BoundaryDifferential` は境界包含の微分の単射性と、その像が接境界全体であることを証明する。
`HalfSpaceJet` は境界超平面を固定する滑らかな座標写像の微分とその逆を構成する。
`HalfSpaceSigns` は法線偏微分の連続性と平均値の定理から符号を保つ近傍を構成し、`HalfSpaceInverse` は半空間を保つ実際の局所微分同相を構成する。
次の段階は、`InwardNeighborhood` の境界への制限について座標表示が境界超平面を固定することと、初期の法線微分が正であることを証明し、この局所逆写像を適用することである。
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

半空間の局所逆写像までの数学ソース `2aa597e8667be0efee4a8ac2d2521eecde79ab1f` の全ローカル検査では 203 module を新規検査し、通常の全体検査では 11,910 対象すべてが accepted である。
対応する検査記録は [halfspace](../benchmarks/records/manifold-gluing/halfspace/README.md) にある。

## Common collar neighborhood checkpoint

Added TransverseVelocity, CollarCoordinates, CollarLocal, CollarStrip, CollarEmbedding. The very same compactly constructed inward candidate has positive normal derivative at every boundary point; actual half-space local inverses give injectivity, open images and continuous inverses. CompactStrip and a second tube lemma yield a common open parameter neighborhood. CollarEmbedding constructs the actual open image, unique inverse, inverse continuity, and TopologicalCollar.Data on that parameter neighborhood. Its forward map is the restriction of the original smooth map. Scratch package full result accepted in /tmp/g04-step-37.json; integration and fixed-source verification follow. This is not completion of G04: smooth inverse, relative extension/comparison, general gluing/doubles and supported global corner rounding remain.

Fixed-source validation of 507afad2b0b64f8c0217cfc52aa6b68ea45178bf completed: normal release build exit0 (98.517 s), focused 1421 targets/240 newly checked/1181 reused, reuse1421, regressions1081/581/628 all reused. Normal repository verification11947/11947 accepted, all reused, exit0 (354.205 s), save failures/corrupt reads/worker recovery0. SHA256 checker8b62b74b30fdef253447ba04042e1492b4dd87cb9972a0fde399abb69829bcd7. Source snapshots match before/after and all10678 global files match Git blobs; source SHA53ec4dcd52df402746dd54bbc1b47d76dcdf19d6a2690317710c7d6d9ec9739e. Evidence benchmarks/records/manifold-gluing/embedding/.

## Smooth inverse and neighborhood-relative collar checkpoint

Scratch /tmp/g04-step-49.json accepted. Added actual ambient inverse witnesses for each CollarLocal.OpenPatch; LocalSmoothTransfer restricts a supplied smooth local witness along an open equality neighborhood. CollarEmbedding.InverseAt transfers these witnesses to the unique global inverse (no global inverse smoothness hypothesis). CollarWidth extracts positive epsilon <=1 inside the common parameter neighborhood. CollarRelative constructs a global collar with image inside any prescribed open neighborhood of the whole boundary. This does not yet extend a specified collar on a subset. LocalSmoothPostcompose composes a supplied local smooth witness with an actual smooth map. Choice comparison, extension of a prescribed partial collar, general gluing/doubles and supported global rounding remain. Integration/fixed-source checks follow.

CollarComparison (scratch /tmp/g04-step-50.json accepted) restricts any two constructed collars to a common open time neighborhood, constructs the comparison homeomorphism fixing boundary, and proves local smoothness of both directions by composing each actual inverse witness with the other actual smooth collar map. This is a smooth comparison of the two open images; it is not an ambient isotopy or extension of an arbitrary prescribed partial collar.

Fixed-source normal validation completed at cd58c28cc8f45cecb3b71a63c5d1aef62561adfd: normal release build exit0 (83.774s); focused1457 targets,275 newly checked,1182 reused; all-reuse1457; regressions1081/581/628 all reused. Repository11982 targets accepted,0 new11982 reused,exit0 (342.804s),peakRSS1410700KiB,virtual2117840KiB; save/corrupt/worker recovery0. Checker SHA unchanged8b62b74b30fdef253447ba04042e1492b4dd87cb9972a0fde399abb69829bcd7. Global snapshot SHA01604a674b4e9e5c982bc0b4831fd5105b5c28199742dc80fd3bc0b31c0c1701; before/after equal and all files match recorded commit Git blobs. Evidence benchmarks/records/manifold-gluing/smooth/.

## Boundary pushout topology checkpoint

Scratch /tmp/g04-glue-13.json accepted. BoundarySeam takes the actual smooth boundary diffeomorphism, forms its pushout, proves both side injections and cross classification, and proves compactness, Hausdorff and second countability when the sides are compact. ClosedPushout proves the quotient map closed from compact seam and Hausdorff sides. ClosedSurjection derives T1, Hausdorff and second countability from an actual continuous closed surjection out of a compact Hausdorff source; the target conclusions are not assumptions. FiniteBasisUnions explicitly enumerates finite unions of an enumerated basis via finite tuples, and CoproductCountability provides the source basis. Smooth atlas for the actual pushout is still pending.

Fixed-source normal validation completed at aae620b4f93eefb6fa748407b329fee4d039744e: normal release build exit0 (97.430s), focused1494 targets/309 new1185 reused, all-reuse1494, regression1081/581/628 all reused; repository12016 accepted,0 new12016 reused,exit0 (376.136s),save/corrupt/recovery0,peakRSS1413000KiB,virtual2117832KiB. Checker SHA8b62b74b30fdef253447ba04042e1492b4dd87cb9972a0fde399abb69829bcd7 unchanged. Global before/after source snapshots equal, Git blobs all matched, SHA0519f626a16429ff55787347eacbcbe67e3f4419bd48b60ae6f0272e0ee05819. Evidence benchmarks/records/manifold-gluing/seamtopology/.

## Seam chart preparation

ChartTransport scratch /tmp/g04-glue-17.json accepted: actual charts transported via a homeomorphism to an open range, inherited smooth coordinate changes and cover of the open range. SignedParameter, ParameterLaws, CollarBoundary scratch /tmp/g04-signed-6.json accepted: signed interval model, continuous positive/negative parts, local smoothness on the appropriate strict side, reconstruction formula, small-time insertions and their continuity, zero agreement, and collar boundary iff time zero. Integrating these preparations does not complete the pushout atlas. Next: actual signed collar map into BoundarySeam, prove it is a homeomorphism onto its open image, then combine interior and seam charts and prove cross transitions.

## Actual signed seam collar, continuous bijection onto open image

Scratch /tmp/g04-assembly-7.json accepted. SeamCollar constructs common epsilon from the two actual collars and builds the signed seam map using closed pasting. It proves continuity, injectivity (including cross-side equality forcing both times zero) and an explicitly open image, with actual surjectivity onto it. Along.exists constructs every input from compact M,N and a supplied actual boundary diffeomorphism. SeamOpen proves matched open sets give an open pushout union. CompactEmbedding constructs the image homeomorphism for a continuous compact-to-Hausdorff injection, for the inverse-continuity step. The seam map inverse continuity and smooth global atlas are still pending. Next build inverse on closed left/right parts of the seam image using CompactEmbedding, actual collar inverses and SignedParameter.SmallTimes insertions, then closed-paste.

Fixed-source normal validation completed at 8c0f1331326b82512699a83497a21f5dcdf4f6a6: build exit0 (93.674s); focused1541 targets354new1187reused; reuse1541; regressions1081/581/628 all reused; repository12061 accepted,0new12061reused,exit0 (407.793s),save/corrupt/worker recovery0,peakRSS1417268KiB,virtual2117840KiB. Checker SHA unchanged8b62b74b30fdef253447ba04042e1492b4dd87cb9972a0fde399abb69829bcd7; before/after snapshots equal, all files matched sourcecommit Git blobs; global SHA5f2509294fd91145c1756ccbf479d613ef017c06c35d2d6736c403113bfef5cb. Evidence benchmarks/records/manifold-gluing/signedseam/.

## Seam homeomorphism and seam chart patch

Scratch /tmp/g04-assembly-11.json accepted. SeamCollar.Image.Compact uses actual compact side embeddings to obtain closed left/right parts of the seam image. It constructs each branch inverse from actual global collar inverses and SignedParameter.SmallTimes insertions, proves both branches continuous, identifies them on the intersection by seam-map injectivity, and closed-pastes the global continuous inverse. The actual signed collar is therefore homeomorphic to the explicitly open pushout neighborhood. Compact.Charts transports Source.manifold charts to that neighborhood and proves covers and within-patch smooth transition extensions. Scratch /tmp/g04-interior-1.json accepted: actual smooth InteriorInclusion from G03's ordinary interior converted to corners, via coordinate identity extensions. Remaining next step: build interior image chart patches and cross transitions to the seam charts, then the whole pushout manifold; relative extension of a prescribed collar, supported global rounding and global orientation/map gluing still pending.

Fixed-source normal validation completed at 824f80da77720c1cbd68ebc5fada4359cd730ddc: normal release build exit0 (83.701s); focused1563 targets363new1200reused; reuse1563; regressions1081/581/628 all reused; repository12070 accepted,0new12070reused,exit0 (368.683s),save/corrupt/recovery0,peakRSS1419188KiB,virtual2117836KiB. Checker SHA unchanged 8b62b74b30fdef253447ba04042e1492b4dd87cb9972a0fde399abb69829bcd7. Before/after snapshots equal and every file matched the recorded commit Git blob. Global snapshot SHA 484b21ca030af0aaf7cb808f43519965bc3a56d08f58ddefda2da36df0ee7879. Evidence benchmarks/records/manifold-gluing/seamhomeo/.

## Full topological chart cover

Scratch assembly12 and interior5 accepted; integrated focused /tmp/g04-integrated-cover.json accepted. InteriorInclusion.InverseAt constructs the local smooth inverse of the intrinsic interior inclusion. InteriorEmbedding transports charts of the converted intrinsic interior through an actual image homeomorphism. InteriorPatches proves each interior image open using SeamOpen. SeamCollar.Image.Compact.Cover classifies both side points by intrinsic boundary membership, places all boundary points in the signed seam (including right boundary using the boundary diffeomorphism inverse), and proves the three chart families cover every pushout point by quotient induction. The cross transitions between distinct chart families and hence the global atlas are still pending; no completed global manifold is claimed. No fatal blocker.

Fixed-source normal validation at 9942f3428bdd362676e00399ba55c5f5229035a0: build exit0 (92.904s); focused1577/377new1200reused; reuse1577; regressions1081/581/628 all reused. Repository12084 accepted,0new12084reused,exit0 (364.853s),save/corrupt/recovery0,peakRSS1419196KiB,virtual2117836KiB. Checker unchanged 8b62b74b30fdef253447ba04042e1492b4dd87cb9972a0fde399abb69829bcd7. All snapshots before/after equal and Git blob matched; global SHA c7209150b1b21b69d13a44f68f1700af8117898f4ca4fa32db1e62c8972d77d5. Evidence benchmarks/records/manifold-gluing/cover/.

## Actual smooth atlas of the compact boundary pushout

Scratch assembly32 accepted; integrated /tmp/g04-integrated-atlas.json accepted. LocalSmoothCompose, SmoothWitness, LocalSmoothPair, ProductLocalMap and SignedInsertion construct actual local smooth witnesses. SmallLeft/SmallRight reconstruct the small collar inverse. LeftTransition/RightTransition and LeftInverse/RightInverse construct the four actual interior/seam transition maps with local smooth witnesses and equality on explicitly open neighborhoods. Sides proves both strict time signs and that opposite interiors cannot meet. ChartCross transfers these actual witnesses to transported chart changes (including rebasing source coordinate membership proofs). Cover proves compatibility of all nine ordered pairs of chart families and constructs Cover.manifold with the actual pushout carrier/topology and its actual Hausdorff/second-countability proofs. No assumed global atlas or new axiom. Next: boundarylessness theorem, public compact gluing/double API; prescribed partial collar extension, supported global rounding, orientation/map gluing remain. No fatal blocker. Scratch assembly13 failed because the dependency source changed during integration, then rerun on fixed sources; other scratch errors were repaired before accepted32.

Fixed-source normal validation at 51b0e049041156016853b0602ef05babb33f79c9: build exit0 (99.449s); focused1631/431new1200reused; reuse1631; regressions1081/581/628 all reused. Repository12138 accepted,0new12138reused,exit0 (371.4s),save/corrupt/recovery0,peakRSS1421252KiB,virtual2117832KiB. Checker unchanged 8b62b74b30fdef253447ba04042e1492b4dd87cb9972a0fde399abb69829bcd7. All before/after snapshots equal and Git blobs matched; global SHA 25f16ead97b823154b7eef9fd5a7d4758866fea287dc4509788a7f4135fbfb8b. Evidence benchmarks/records/manifold-gluing/atlas/.

## Boundaryless gluing, double and local mapping criterion

Scratch assembly41 accepted; integration /tmp/g04-integrated-double.json accepted. BoundaryTransport derives intrinsic boundary membership in a model from boundary membership in its transported chart, using actual charts of both atlases. OpenRegion has no intrinsic boundary. Cover.Interior proves the signed product has no boundary from converted boundary and signed open interval, transports this and the two ordinary interior models, and proves noBoundary at every glued point. CompactGluing constructs actual atlas plus noBoundary on the actual pushout carrier/topology from compactness and actual boundary diffeomorphism. Double specializes the actual construction to the identity boundary diffeomorphism. TransportInclusion constructs the actual smooth model inclusion and local inverse witnesses. TransportOut and Cover.Mapping derive global smoothness from actual smooth maps on the two interior models and signed seam agreeing with the continuous global function. Prescribed partial collar extension, supported global rounding, orientation and collar-preserving map gluing still pending. Next SideInclusions and actual collar-preserving map gluing.

Fixed-source normal validation at 1ae75af8b11eccfd8cd08b09b4123084c88d0ac2: build exit0 (99.634s); focused1670/468new1202reused; reuse1670; regressions1081/581/628 all reused. Repository12175 accepted,0new12175reused,exit0 (369.814s),save/corrupt/recovery0,peakRSS1423364KiB,virtual2117836KiB. Checker unchanged 8b62b74b30fdef253447ba04042e1492b4dd87cb9972a0fde399abb69829bcd7. All before/after snapshots equal and Git blobs matched; global SHA 27d44212b6798f81ad8eba8e44800368674e1628135919baf19735b89bd92fde. Evidence benchmarks/records/manifold-gluing/double/.
