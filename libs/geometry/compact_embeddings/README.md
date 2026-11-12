# コンパクト多様体の埋め込み

有限個のチャートとコンパクト台付き cutoff から、コンパクトな滑らかな多様体の有限次元 Euclid 空間への埋め込みを構成する。

埋め込みは `manifolds.Immersion.Embedding` の実際の写像であり、接写像の単射性、点の単射性、像への同相を与える開集合の持ち上げを持つ。

## 閉多様体

`Compact[n].On[M].exists compact` は `Result` の存在を証明する。

`Result.dimension` は構成した有限次元、`Result.embedding` はその Euclid 空間への滑らかな埋め込みである。

空多様体も含み、空の場合は零次元を使う。

零次元の非空多様体も同じ cutoff の構成で扱う。

チャート領域の開被覆に対し `smooth_partitions` の局所 bump を選び、コンパクト性から有限個の plateau が全体を覆うようにする。

チャートを \(\phi_i\)、cutoff を \(b_i\) とすると、各ブロックは
\[
x\longmapsto \bigl(b_i(x),b_i(x)\phi_i(x)\bigr)
\]
である。

積の座標はチャートの外で零延長する。

台がチャート領域に含まれることから、この零延長は滑らかになる。

各点の近傍では少なくとも一つの \(b_i\) が一なので、そのブロックがチャート座標を回収する。

これにより写像と接写像の単射性を示す。

コンパクトな閉集合の像が Hausdorff 空間で閉じることから、像への同相を得る。

| API | 内容 |
| --- | --- |
| `WeightedChart[n].On[M].At[c,b,within].map` | 零延長した重み付きチャートブロック |
| `At.injectiveAtOne` | cutoff が一の点と同じ像を持つ点の一致 |
| `At.Plateau[U,open,oneOn].At[x,inside].immersion` | plateau 上の実際の微分の単射性 |
| `WeightedChart.On.Vector[m].Of[f,regular].map` | 滑らかなスカラー座標から Euclid 空間への写像を構成 |
| `Finite[n,d].On[M].Of[f,U].build` | 有限ブロックの組み立てと被覆領域上の分離・微分の単射性 |
| `CompactCriterion.Between.Of.embedding` | コンパクトな定義域から Hausdorff 多様体への単射 immersion の埋め込み判定 |
| `Compact.On.exists` | 有限チャート・cutoff の選択を含む存在定理 |

構成に使う有限個のチャートや cutoff の選択は結果の入力条件にしない。

`Naturality.On.Comparison` は異なる選択から得た任意の二つの結果を、安定化した滑らかな埋め込みの族で結ぶ。

## 安定化した埋め込みの族

`Stabilization[n,a,b].On[M].Between[f,g]` は、任意の滑らかな埋め込み \(f:M\to\mathbb R^a\)、\(g:M\to\mathbb R^b\) に対し、
\[
H_t(x)=((1-t)f(x),t g(x))\in\mathbb R^{a+b}
\]
を構成する。

`embedding[t]` は各実数 \(t\) で実際の `manifolds.Immersion.Embedding` を返す。

\(t\ne0\) なら右射影を \(t^{-1}\) 倍して \(g\) を回収し、\(t=0\) なら左射影から \(f\) を回収する。

この滑らかな回収写像から微分の単射性、写像の単射性、開集合の持ち上げを証明するので、元の多様体にコンパクト性を要求しない。

`leftEndpoint` と `rightEndpoint` は両端が \((f,0)\) と \((0,g)\) であることを示す。

`Linear.InChart[c].map` は \(\mathbb R\times c.image\) 上の実際の滑らかな座標写像であり、`formula` が \(H\) との一致を与える。

`Parameters[k].On[U,s].Local[c]` は任意の開パラメータ領域と滑らかなスカラー関数 \(s\) に対し同じ構成を行う。

`Reparametrization[j].From[V,r].natural` は滑らかなパラメータ写像による引き戻しとの一致を証明する。

`Relative.embeddingAt[t]` は `smooth_partitions.Exponential.Step.value` を時計に使い、\(t\le0\) では \((f,0)\)、\(t\ge1\) では \((0,g)\) と一致する。

`Relative.InChart[c].map` は端をまたぐ実際の滑らかさを証明する。

一般のパラメータ版の `fixedLeft` と `fixedRight` も、時計が零または一の任意のパラメータ領域で端の固定を保証する。

`Naturality[p].From[P].Of[h]` は任意の滑らかな埋め込み \(h:P\to M\) による前合成を扱い、線形時計と相対時計の両方で一致を証明する。

`Example` は実直線の恒等埋め込みから二つの座標軸を結ぶ族と固定された端を具体化する。

## 自然性と例

`Naturality[n].On[M].From[p].On[P].Along[d].Of[result].transport` は微分同相による埋め込みの引き戻しを構成する。

`dimension`、`formula`、`recover` が次元の保存、前合成の式、逆微分同相による回収を与える。

`Naturality.On.Comparison[left,right]` は任意の二つの存在定理の結果を比較し、安定化した埋め込み、両端の式、パラメータ区間の外側で端を固定する滑らかな族を公開する。

`Examples.Point.exists` は零次元 Euclid 空間の一点に存在定理を適用する。

`Examples.Empty[n].exists` は任意の次元の空多様体を扱う。

`Examples.Point.At[a].embedding` は一点を実数座標 \(a\) に埋め込み、`Point.path` と `Point.relative` が零と一への埋め込みを安定化後に結ぶ。

## 境界付き多様体と厳密な collar 整合性

`NeatExistence[n].On[M].With[cover].Compact[compact].exists` は、次元が \(1+n\) のコンパクトな境界付き多様体に対して `Result` を構成する。
`cover` は既存の境界チャート被覆である。
結果は有限次元 `dimension`、構成した collar と正の幅、および実際の `boundary_manifolds.Neat.Embedding` を持つ。
標的 `HalfSpace[k].manifold` は Euclid 空間と非負半直線の積で、`HalfSpace.coordinates` とその逆が通常の有限次元半空間との座標同一視を与える。

まず滑らかな double を構成し、元の多様体の片側包含が immersion であることを collar と内部の座標で証明する。
double のコンパクト性と境界の空性から上の閉多様体定理を適用し、Euclid 埋め込み \(e\) を得る。
collar 時間から構成した大域的な高さ \(h\) は境界上でちょうど零、内部で正であり、境界の内向き法線微分は正方向へ全射になる。

さらに collar 内の時間を滑らかに潰す写像 \(r\) を構成する。
十分狭い collar では \(r(c(b,t))=b\)、collar のコンパクトな台の外では \(r\) は恒等写像である。
最終的な埋め込みは \(x\mapsto(e(r(x)),h(x))\) である。
\(r\) と \(h\) の組が点を分離し、その微分の組も単射になることを証明する。
したがって `Result.compatible` は、ある正の幅の collar 上で厳密な積の式 \(F(c(b,t))=(F_{\partial}(b),t)\) を保証する。

| API | 内容 |
| --- | --- |
| `DoubleEmbedding.On.With.Compact.exists` | double の構成と片側包含の微分の単射性 |
| `Bridge.Interior` | 境界のない境界付き多様体と通常の多様体の比較 |
| `Neat.Height.With.From.Of.Compact` | 大域的な非負高さと正確な零集合 |
| `Neat.Height.With.From.Of.Compact.Collapse` | collar の潰し写像と点の同時分離 |
| `HeightNormal.On.With.From` | 境界の保存、法線全射、接空間の反映 |
| `CollapseDifferential.On.With.From.joint` | 潰し写像と高さの微分の同時単射性 |
| `NeatExistence.On.With.Compact.exists` | collar と厳密に整合する neat embedding の存在 |

`Examples.Interval.Compactness.compact` は具体的な閉区間のコンパクト性を証明する。
`Examples.Interval.Neat.exists` は存在定理をその区間に適用し、`Of[result]` は両端だけが標的境界に写ること、両端の像が異なること、厳密な collar 整合性を公開する。

## 検査

固定ソースと通常キャッシュを用いた package・依存回帰・全体検査の記録は [benchmarks/records/compact-embeddings](../../../benchmarks/records/compact-embeddings/README.md) にある。
