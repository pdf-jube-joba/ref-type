# G04 の実装状態

基点は `ed1af945bfdfdc1849bf1919317e3ce422b1ac1f`、ブランチは `math/g04-collars-gluing`、保存用 Draft は [PR #73](https://github.com/pdf-jube-joba/ref-type/pull/73) である。
G04 全体は未完了である。
定理の範囲は [manifold_gluing の README](../libs/geometry/manifold_gluing/README.md) にある。

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

半空間の局所逆写像までの数学ソース `2aa597e8667be0efee4a8ac2d2521eecde79ab1f` の全ローカル検査では 203 module を新規検査し、通常の全体検査では 11,910 対象すべてが accepted である。

## Common collar neighborhood checkpoint

Added TransverseVelocity, CollarCoordinates, CollarLocal, CollarStrip, CollarEmbedding. The very same compactly constructed inward candidate has positive normal derivative at every boundary point; actual half-space local inverses give injectivity, open images and continuous inverses. CompactStrip and a second tube lemma yield a common open parameter neighborhood. CollarEmbedding constructs the actual open image, unique inverse, inverse continuity, and TopologicalCollar.Data on that parameter neighborhood. Its forward map is the restriction of the original smooth map. Scratch package full result accepted in /tmp/g04-step-37.json; integration and fixed-source verification follow. This is not completion of G04: smooth inverse, relative extension/comparison, general gluing/doubles and supported global corner rounding remain.

## Smooth inverse and neighborhood-relative collar checkpoint

Scratch /tmp/g04-step-49.json accepted. Added actual ambient inverse witnesses for each CollarLocal.OpenPatch; LocalSmoothTransfer restricts a supplied smooth local witness along an open equality neighborhood. CollarEmbedding.InverseAt transfers these witnesses to the unique global inverse (no global inverse smoothness hypothesis). CollarWidth extracts positive epsilon <=1 inside the common parameter neighborhood. CollarRelative constructs a global collar with image inside any prescribed open neighborhood of the whole boundary. This does not yet extend a specified collar on a subset. LocalSmoothPostcompose composes a supplied local smooth witness with an actual smooth map. Choice comparison, extension of a prescribed partial collar, general gluing/doubles and supported global rounding remain. Integration/fixed-source checks follow.

CollarComparison (scratch /tmp/g04-step-50.json accepted) restricts any two constructed collars to a common open time neighborhood, constructs the comparison homeomorphism fixing boundary, and proves local smoothness of both directions by composing each actual inverse witness with the other actual smooth collar map. This is a smooth comparison of the two open images; it is not an ambient isotopy or extension of an arbitrary prescribed partial collar.

## Boundary pushout topology checkpoint

Scratch /tmp/g04-glue-13.json accepted. BoundarySeam takes the actual smooth boundary diffeomorphism, forms its pushout, proves both side injections and cross classification, and proves compactness, Hausdorff and second countability when the sides are compact. ClosedPushout proves the quotient map closed from compact seam and Hausdorff sides. ClosedSurjection derives T1, Hausdorff and second countability from an actual continuous closed surjection out of a compact Hausdorff source; the target conclusions are not assumptions. FiniteBasisUnions explicitly enumerates finite unions of an enumerated basis via finite tuples, and CoproductCountability provides the source basis. Smooth atlas for the actual pushout is still pending.

## Seam chart preparation

ChartTransport scratch /tmp/g04-glue-17.json accepted: actual charts transported via a homeomorphism to an open range, inherited smooth coordinate changes and cover of the open range. SignedParameter, ParameterLaws, CollarBoundary scratch /tmp/g04-signed-6.json accepted: signed interval model, continuous positive/negative parts, local smoothness on the appropriate strict side, reconstruction formula, small-time insertions and their continuity, zero agreement, and collar boundary iff time zero. Integrating these preparations does not complete the pushout atlas. Next: actual signed collar map into BoundarySeam, prove it is a homeomorphism onto its open image, then combine interior and seam charts and prove cross transitions.

## Actual signed seam collar, continuous bijection onto open image

Scratch /tmp/g04-assembly-7.json accepted. SeamCollar constructs common epsilon from the two actual collars and builds the signed seam map using closed pasting. It proves continuity, injectivity (including cross-side equality forcing both times zero) and an explicitly open image, with actual surjectivity onto it. Along.exists constructs every input from compact M,N and a supplied actual boundary diffeomorphism. SeamOpen proves matched open sets give an open pushout union. CompactEmbedding constructs the image homeomorphism for a continuous compact-to-Hausdorff injection, for the inverse-continuity step. The seam map inverse continuity and smooth global atlas are still pending. Next build inverse on closed left/right parts of the seam image using CompactEmbedding, actual collar inverses and SignedParameter.SmallTimes insertions, then closed-paste.

## Seam homeomorphism and seam chart patch

Scratch /tmp/g04-assembly-11.json accepted. SeamCollar.Image.Compact uses actual compact side embeddings to obtain closed left/right parts of the seam image. It constructs each branch inverse from actual global collar inverses and SignedParameter.SmallTimes insertions, proves both branches continuous, identifies them on the intersection by seam-map injectivity, and closed-pastes the global continuous inverse. The actual signed collar is therefore homeomorphic to the explicitly open pushout neighborhood. Compact.Charts transports Source.manifold charts to that neighborhood and proves covers and within-patch smooth transition extensions. Scratch /tmp/g04-interior-1.json accepted: actual smooth InteriorInclusion from G03's ordinary interior converted to corners, via coordinate identity extensions. Remaining next step: build interior image chart patches and cross transitions to the seam charts, then the whole pushout manifold; relative extension of a prescribed collar, supported global rounding and global orientation/map gluing still pending.

## Full topological chart cover

Scratch assembly12 and interior5 accepted; integrated focused /tmp/g04-integrated-cover.json accepted. InteriorInclusion.InverseAt constructs the local smooth inverse of the intrinsic interior inclusion. InteriorEmbedding transports charts of the converted intrinsic interior through an actual image homeomorphism. InteriorPatches proves each interior image open using SeamOpen. SeamCollar.Image.Compact.Cover classifies both side points by intrinsic boundary membership, places all boundary points in the signed seam (including right boundary using the boundary diffeomorphism inverse), and proves the three chart families cover every pushout point by quotient induction. The cross transitions between distinct chart families and hence the global atlas are still pending; no completed global manifold is claimed. No fatal blocker.

## Actual smooth atlas of the compact boundary pushout

Scratch assembly32 accepted; integrated /tmp/g04-integrated-atlas.json accepted. LocalSmoothCompose, SmoothWitness, LocalSmoothPair, ProductLocalMap and SignedInsertion construct actual local smooth witnesses. SmallLeft/SmallRight reconstruct the small collar inverse. LeftTransition/RightTransition and LeftInverse/RightInverse construct the four actual interior/seam transition maps with local smooth witnesses and equality on explicitly open neighborhoods. Sides proves both strict time signs and that opposite interiors cannot meet. ChartCross transfers these actual witnesses to transported chart changes (including rebasing source coordinate membership proofs). Cover proves compatibility of all nine ordered pairs of chart families and constructs Cover.manifold with the actual pushout carrier/topology and its actual Hausdorff/second-countability proofs. No assumed global atlas or new axiom. Next: boundarylessness theorem, public compact gluing/double API; prescribed partial collar extension, supported global rounding, orientation/map gluing remain. No fatal blocker. Scratch assembly13 failed because the dependency source changed during integration, then rerun on fixed sources; other scratch errors were repaired before accepted32.

## Boundaryless gluing, double and local mapping criterion

Scratch assembly41 accepted; integration /tmp/g04-integrated-double.json accepted. BoundaryTransport derives intrinsic boundary membership in a model from boundary membership in its transported chart, using actual charts of both atlases. OpenRegion has no intrinsic boundary. Cover.Interior proves the signed product has no boundary from converted boundary and signed open interval, transports this and the two ordinary interior models, and proves noBoundary at every glued point. CompactGluing constructs actual atlas plus noBoundary on the actual pushout carrier/topology from compactness and actual boundary diffeomorphism. Double specializes the actual construction to the identity boundary diffeomorphism. TransportInclusion constructs the actual smooth model inclusion and local inverse witnesses. TransportOut and Cover.Mapping derive global smoothness from actual smooth maps on the two interior models and signed seam agreeing with the continuous global function. Prescribed partial collar extension, supported global rounding, orientation and collar-preserving map gluing still pending. Next SideInclusions and actual collar-preserving map gluing.

## Smooth side inclusions and collar-preserving map gluing

Scratch assembly47 accepted; integrated /tmp/g04-integrated-maps.json accepted. LeftLift/RightLift construct actual local signed collar lifts of all side points in the small collar image, including boundary. Cover.Inclusions proves actual smooth side inclusions by these lifts near boundary and intrinsic interior inverse witnesses elsewhere. Cover.CollarMaps uses a common positive collar width for source and target constructed gluing structures, actual smooth side maps and an actual smooth boundary map preserving both collar formulas. Its Of derives the quotient descent laws at time zero, constructs the continuous quotient map, builds the signed product smooth map and the two interior smooth maps, and applies the proved Cover.Mapping criterion. Cover.IdentityMap instantiates with all three actual identities and proves the descended smooth map is the identity at every quotient point. No new axiom and no assumed smooth descended map. Remaining: relative extension of specified partial collar, supported global product rounding, global orientation consistency/sign API. No fatal blocker. Next supported universal rounding and boundary contraction sign proofs, then global transport and prescribed collar extension.

## Supported normal rounding model and intrinsic boundary signs

Scratch /tmp/g04-round-12.json accepted; integration /tmp/g04-integrated-roundmodel.json accepted. New /tmp/g04-round package depends on actual library. SupportedRounding.Unit constructs smooth sqrt(d^2+bump(d)) with positive radicand, lower bound abs(d), upper bound abs(d)+1, and equality abs(d) outside bump support. Higher constructs the actual regular sublevel manifold in arbitrary dimension using diagonal derivative exactly two, proves containment in the original quadrant, equality with the quadrant outside u<3,v<3, and intrinsic boundary iff sum=profile. This is the supported NORMAL MODEL, not yet transported to an arbitrary compact product. BoundarySigns proves normal contraction reversal, arbitrary rescaling, anti-commutation and cancellation/repeated-normal vanishing. BoundaryForms pulls contraction through the actual boundary-inclusion differential and proves intrinsic boundary tangent form sign/rescale formulas. QuadrantOpen constructs exact ambient representatives of open quadrant subsets; OpenManifold constructs a genuine corner manifold on any open subset with restricted charts and all actual compatibility extensions. Next /tmp/g04-open-inclusion.py (prepared, not run) adds actual smooth inclusion and local inverse witnesses for OpenManifold; then transport rounding model through product collars. Prescribed partial collar extension remains. No fatal blocker.

## Smooth outside agreement and open model operations

Scratch round25 accepted. SupportedRounding.Higher.Quarter is an actual smooth inclusion of the rounded manifold into the original quadrant, proved through actual Sublevel adapted charts. Quarter.Far constructs the actual smooth inverse on the open region u>3 or v>3; Quarter.Outside bundles these as an actual identity diffeomorphism of the open parts, with inverse laws. OpenManifold now has its actual smooth inclusion and local inverse; OpenCorestriction restricts any actual smooth map whose image lies in the open subset. ChartModel proves the actual diffeomorphism from a globally charted model to its canonical quadrant. DimensionChange proves smooth identity maps across equal natural dimension expressions without changing carrier or topology. CompactTimes proves compactness of [0,a] inside the parameter manifold. General compact product transport and extension of a prescribed partial collar remain; no fatal blocker.

## Compact support of global product rounding

Scratch round39 accepted. CollarRestriction now constructs an actual diffeomorphism from any open parameter region inside the uniform collar to its actual open image, deriving the inverse smoothness from the actual collar inverse, without an assumed inverse smoothness premise. CollarWindow.Core proves compactness of finite closed-time collar images and classifies their parameter time bounds. OpenProduct constructs the product homeomorphism to the open rectangle of the two actual images. ProductCollar chooses common positive scale q with 3q<4q<epsilon<=1, actual open product collar and compact inner product core. Rounded normalizes the actual time coordinates, removes the open locus where the actual rounding defining function is negative, proves that the removed locus lies in that compact core, and constructs the actual closed compact subset of MxN unchanged outside the core. NormalPlane proves its raw 2-coordinate reconstruction and continuity; PositiveScale proves cancellation and inequalities. The smooth atlas on this actual compact rounded subset and extension of a prescribed partial collar remain. No fatal blocker.

## Actual near model of compact product rounding

Scratch round52 accepted. RoundingWindow constructs actual smooth scaled normal maps from the bounded rounded normal model to Time. ProductCollar.Rounded.NearModel constructs the actual smooth physical map from boundary product times the rounded normal window into MxN. Parameters proves it homeomorphic to the actual nonnegative-constraint collar parameter subset, deriving both inverse laws and both continuities. ParameterRegion proves nonnegative defining value iff membership in the global rounded subset on the actual near collar. Image constructs the actual homeomorphism to the open near region of the actual compact rounded subset. TimePlane constructs the actual smooth normalization from Time x Time into the standard quadrant, with exact formula. RoundingWindow.Outside constructs the actual smooth outside inverse into the rounded window, with local smooth inverse witnesses. MapProduct constructs actual product smooth maps. OpenProductModel constructs an actual smooth inclusion of the open product and local inverse witnesses. Still pending: assemble cross transitions and the global smooth atlas on this rounded subset, extend prescribed partial collars. No fatal blocker.

## Global smooth atlas on compact product rounding

Scratch round62 accepted. Coordinates derives actual smooth base and normalized quarter-coordinate maps on the full small parameter product. Outside constructs the actual local smooth inverse of the near model at every parameter outside the inner core, with exact underlying point equality. Global uses natural-number dimension equality to reinterpret the near atlas on the original product dimension while preserving carrier/topology and actual smooth identity maps. NearTransition and FarTransition construct both actual local smooth cross maps and explicit open agreement neighborhoods. Cover transports and combines the near and far families, proves all four chart-family transition cases, and constructs the actual global corner-manifold atlas on the compact rounded subset. Unit.strictlyPositive and Higher.ZeroNormal prove every original corner is removed; Corner also proves all original product corners lie in the compact core. Global.exists derives the atlas, and ProductCollar.With.Compact.exists constructs all input collars, widths, scale, region and atlas from compact boundary manifolds and their actual boundary covers. Compact.Of publishes the actual manifold, compactness, unchanged outside core and removesCorners. This uses the existing corner-manifold type, with near local model ordinary boundary product times regular sublevel; a separately normalized fixed-normal Boundary.Cover on the final rounded atlas has not been published. Extension of a prescribed partial collar remains, no fatal blocker.

## Review scope clarification and reusable cone/local extension proofs

Parent review clarified original G04 relative requirement may already be satisfied by CollarRelative's theorem producing a global collar inside any given open neighborhood of the whole boundary. Exact extension of an already prescribed partial collar is a stronger separate result; do not list that stronger result as completed. Parent explicitly requests final rounded Boundary.Cover and no higher corner guarantee, actual gluing/double orientation consistency, and public extraction of actual side smooth inclusions from CompactGluing.Result. README intro is stale and will be rewritten. Scratch relative8 accepted: SmoothMapExt, DifferentialOfIdentity, DifferentialCones, TangentTransportCones, SmoothLeftInverseCones, DiffeomorphismCones, OpenManifoldCones, HalfProduct, CollarCylinder, OpenSmoothExtension, MapProductDifferential, OpenProductLeft. These are actual proofs, no prescribed partial extension asserted. OpenManifoldCones proves boundary equivalence and reflection of tangent vectors under the actual inclusion derivative. DiffeomorphismCones proves boundary preservation and strict derivative preservation from an actual smooth left inverse. CollarCylinder provides canonical half-chart boundary cover for ordinary B x Time and boundary iff time zero. OpenSmoothExtension glues an actual smooth map on an open set to another actual global map outside a closed subset when they agree on the overlap. It is derived from open pasting, actual local inverse witnesses and equality transfer. Further work should prioritize review completion, not require the stronger partial extension as original plan completion condition.

## Public gluing construction and side maps

Scratch public3 accepted. CompactGluing.Compact.Result now retains actual collar Construction, atlasConstructed equality, actual smooth left/right/seam maps into the very returned atlas, and exact pointwise values for all three maps. Construction(c) publishes the actual signed seam manifold and function. Build(c) derives every new field from the already verified Cover.Inclusions and the same constructed atlas. Double.Compact exposes actual smooth left and right maps from the returned Result. README replaced chronological stale claims with current stable APIs and explicit review items: final Boundary.Cover/no higher corners and actual gluing/double orientation consistency. Stronger prescribed partial-collar extension is separate from original neighborhood-relative requirement.

## Boundary atlas and no higher corners of the actual compact rounding

Scratch boundary20 and integrated full-check-local accepted. RoundedBoundary constructs a normalized fixed-normal Boundary.Cover on the same actual compact rounded subset and topology. It derives local half-space models from free boundary base charts times the regular sublevel window near the corner; outside the compact core it excludes simultaneous boundary points and crops the interior factor to derive a half chart. TransportHalfModel transports the derived half models through the actual near and far homeomorphisms into the actual global atlas. DimensionChangeHalf transports the full half-cover evidence with dimension equality. NormalizeHalfAtlas restricts and swaps each actual local half-model normal coordinate, proves the new chart transitions via actual smooth extensions, retains old compatible charts, constructs the fixed-normal Boundary.Cover, and proves a chart with at most one active constraint at every point. Compact.Of exposes manifold, boundaryCover, noHigherCorners, compact, unchanged, removesCorners. The stronger prescribed partial-collar extension remains separate from the original neighborhood-relative theorem.

## Actual gluing and double orientation consistency

Scratch orientation6 accepted. TransportDifferential proves the actual differential of a map with the actual open-homeomorphism values has the identity matrix in the actual source and transported target charts; frame identifies this actual differential with coordinate isomorphisms. GluingForms fixes the very public CompactGluing.Result, proves its actual seam map equals actual left/right inclusion composed with actual collar maps on the appropriate signed half, and builds the actual seam differential frames at every boundary point in every boundary chart. orientationSign/orientationCoherence prove top form sign reversal for the right inward normal frame. frameCoordinates/recoverForm prove coordinate isomorphism and recovery of every ambient top form, rather than allowing a degenerate zero pullback. horizontal and normalOpposite prove shared tangential directions and opposite inward normals. outwardOpposite/boundaryCancellation prove opposite induced outward boundary forms and their cancellation. DoubleForms specializes these statements to the actual Double.Result. These are universal signs on the constructed smooth gluing; no orientation consistency conclusion is assumed. Original G04 requirements are complete in the clarified scope.
