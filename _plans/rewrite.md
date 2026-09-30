# 新しい宣言への書き換え候補

`libs/std`、`libs/real`、`libs/topology`、`libs/tests` の `.ref` ファイルとパッケージ構成をざっと確認した候補一覧。
対応宣言の構文名は `\correspondence`。
優先度は、既存の定義をそのまままとめられる箇所を「高」、依存する構成も整理する箇所を「中」、表現や公開 API の設計を伴う箇所を「要検討」とした。
候補の成立はソースからの見通しであり、書き換え後の型検査は実施時に行う。

## libs/std

| 優先度 | 場所・対象 | 宣言 | 整理できる内容 |
| --- | --- | --- | --- |
| 高 | [Data/Bijection.ref](../libs/std/src/Data/Bijection.ref)：`RawBijection`、`BijectionLaws`、`BijectionSet`、`Bijection` | `\structure` | `forward`、`backward` と左右の逆写像の法則を一つの宣言にまとめる。`raw`、`laws` は生成される member に置き換えられる。 |
| 高 | [Data/Bool.ref](../libs/std/src/Data/Bool.ref)：`neg`、`and`、`or`、`xor`、`implies`、`eqb` | `\correspondence` | 各 Program 演算、`*Prec`、`*MatchesPrec` の三点をまとめる。既存の各引数についての一致証明から、関数全体の coherence を作れる。 |
| 高 | [Arithmetic/Int.ref](../libs/std/src/Arithmetic/Int.ref)：`DiffState`、`diffStep`、`diffTerminates`、`diff` | `\machine` | 自然数二つを同時に減らす状態遷移と停止性を `DiffLoop` にまとめる。`negOfNat`、`neg`、`add`、`mul` 内の直接の `\run` も同じ実行 member に統一できる。 |
| 高 | [Arithmetic/Int.ref](../libs/std/src/Arithmetic/Int.ref)：`diff` と整数演算の `*Prec`、`*MatchesPrec` | `\correspondence` | `diff`、`positive`、`negative`、`ofNat`、`negOfNat`、`neg`、`add`、`sub`、`mul`、`succ`、`pred`、`natAbs`、`abs`、比較、選択、偶奇、累乗を実装・仕様・一致証明の組にする。 |
| 高 | [Alg/Monoid.ref](../libs/std/src/Alg/Monoid.ref)：`RawMonoid`、`MonoidLaws`、`Monoid` | `\structure` | 単位元と二項演算、左右の単位律と結合律をまとめ、`MonoidSet`、`raw`、`laws` と法則を取り出す定義を整理する。 |
| 中 | [Alg/Alg.ref](../libs/std/src/Alg/Alg.ref)：`Group`、`Semiring` | `\structure` | `RawGroup`／`GroupLaws`、`RawSemiring`／`SemiringLaws` と refinement をまとめる。モノイドへの変換と構成済みの法則を利用する部分も合わせて更新する。 |
| 中 | [Alg/Monoid.ref](../libs/std/src/Alg/Monoid.ref)、[Alg/Alg.ref](../libs/std/src/Alg/Alg.ref)、[Alg/Ring.ref](../libs/std/src/Alg/Ring.ref)：可換モノイド・可換群・可換環 | `\structure` | 基礎構造と追加の可換律を束ねる。現在は基礎構造と Raw 型を共有しているため、共有を保つ表現と基礎構造を field に持つ表現を比較して決める。 |
| 中 | [Alg/Ring.ref](../libs/std/src/Alg/Ring.ref)：`Ring`、`RingModule`、`RingAlgebra` | `\structure` | データ、law record、部分集合、法則を取り出す関数をまとめる。`RingModule` と `RingAlgebra` はスカラー環に依存するので、環の書き換え後に進める。 |
| 中 | [Alg/Field.ref](../libs/std/src/Alg/Field.ref)：`RawField`、`FieldLaws`、`Field` | `\structure` | 環の演算に逆数を加えたデータと、可換環・非自明性・逆数の法則をまとめる。可換環への変換も更新する。 |
| 中 | [Data/Pair.ref](../libs/std/src/Data/Pair.ref)、[Program.ref](../libs/std/src/Data/Pair/Program.ref)、[Mapping.ref](../libs/std/src/Data/Pair/Program/Mapping.ref)、[Functions.ref](../libs/std/src/Data/Pair/Program/Functions.ref) | `\correspondence` | `make`、`first`、`second`、`swap`、`map`、`mapFirst`、`mapSecond`、`curry`、`uncurry`、`assoc`、`unassoc` の Program 演算と Set 演算を接続する。任意の `\Set` を扱う汎用 API と、`\VType` を引数にする対応宣言の役割を整理する。 |

### 依存箇所と設計上の論点

Int の `natIsZero`、`natEqb`、`natLeb`、`natLtb`、`natEven`、`natOdd` にも Program 演算・仕様・一致証明の組がある。
Nat と Int が共有する Bool の instance を確認し、既存の Nat の対応宣言を利用する箇所と、Bool の表現変換を含む対応宣言を分ける。
`zero`、`one`、`minusOne` にも一致証明があるので、定数を公開する形も演算の API と合わせて検討する。

[Int.Math](../libs/std/src/Arithmetic/Int/Math.ref) と [Specification](../libs/std/src/Arithmetic/Int/Math/Specification.ref) の `*MatchesMath` は、`toMath` を介して `Int^` と群完成 `Grothendieck` の演算を結ぶ証明である。
`\correspondence` の coherence は Program の反映と同じ型の Set 仕様の等式なので、この接続には引き続き型間の写像とその演算保存の証明が必要になる。
[Int.Order](../libs/std/src/Arithmetic/Int/Order.ref) と [Specification.Laws](../libs/std/src/Arithmetic/Int/Math/Specification/Laws.ref) も、新しい仕様と coherence の参照へ合わせて更新する。

代数構造の構成例は [IntAlgebra](../libs/std/src/Arithmetic/IntAlgebra.ref)、[Int.Math.Ring](../libs/std/src/Arithmetic/Int/Math/Ring.ref) にある。
生成される Raw 型と Law 型への移行では、これらの構成と構造間の変換を一緒に確認する。
独立した二つの structure の Raw 型の共有は、明示的なデータ変換を含めて設計する。

[Nat.ref](../libs/std/src/Nat.ref) は `Iteration`、七つの machine、演算の correspondence が導入済みであり、今回の候補の参考になる。
[Fixpoint.ref](../libs/std/src/Fixpoint.ref) は現状 `Stack` の宣言だけなので、machine の具体的な移行対象は今のところ Int の差分ループに集中する。

## libs/topology

| 優先度 | 場所・対象 | 宣言 | 整理できる内容 |
| --- | --- | --- | --- |
| 高 | [Topology.ref](../libs/topology/src/Topology.ref)：`RawTopology`、`TopologyLaws`、`TopologySet`、`Topology` | `\structure` | `openSets` と空集合・全体・和・有限交叉の法則をまとめる。`raw`、`laws` と各位相の構成を生成 member に合わせる。 |
| 要検討 | [Presentations.ref](../libs/topology/src/Topology/Presentations.ref)：`ClosedSetSystem`、`ClosureOperator`、`InteriorOperator`、`NeighborhoodSystem` | `\structure` | 集合族、閉包作用素、内部作用素、近傍の割り当てと、それぞれの law record をまとめる。現状の Raw は集合族や関数なので、それらを field に持つ record へ移す場合は所属判定と関数適用を更新する。 |
| 要検討 | [Presentations.ref](../libs/topology/src/Topology/Presentations.ref)：`PresentationsCorrespond` | `\structure` | 位相と四つの表示をデータとして持ち、表示の対応を law とする bundle にできる。現在の record は与えられた表示の対応命題なので、表示一式を値として受け渡す用途がある場合に有効。 |
| 要検討 | [Continuity.ref](../libs/topology/src/Continuity.ref)：`Continuous`、`composeContinuous`、`restrictContinuous` | `\structure` | 写像と連続性を持つ `ContinuousMap` を追加すると、合成や制限の結果を連続写像として返せる。現在の写像と命題を別々に渡す API に対する設計変更になる。 |

Topology の移行に伴う参照先は [Subspace](../libs/topology/src/Topology/Subspace.ref)、[Subspace.Maps](../libs/topology/src/Topology/Subspace/Maps.ref)、[SingletonSpace](../libs/topology/src/Topology/SingletonSpace.ref)、[Product](../libs/topology/src/Product.ref)、[Product.Universal](../libs/topology/src/Product/Universal.ref)。
`PresentationsCorrespond` は集合論的な表示間の同値を表し、Program と反映の対応とは意味が異なる。

## libs/real

| 優先度 | 場所・対象 | 宣言 | 整理できる内容 |
| --- | --- | --- | --- |
| 高 | [AxiomaticReals.ref](../libs/real/src/AxiomaticReals.ref)：`RawRealStructure`、`IsAxiomaticRealStructure`、`AxiomaticRealStructure` | `\structure` | 演算と順序関係をデータに、`FieldLaws`、`LinearOrderLaws`、`OrderedFieldLaws`、`Completeness` を law の field にまとめる。現在の入れ子の連言から法則を取り出す部分を named field にできる。 |
| 要検討 | [CauchyReal.ref](../libs/real/src/CauchyReal.ref)：`Sequence`、`IsCauchy`、`CauchySet`、`CauchySeq` | `\structure` | 列をデータ、Cauchy 性を law としてまとめる。列の関数型を record で包むため、`at`、`cauchyProperty`、列の構成と同値関係の証明へ変更が広がる。 |
| 要検討 | [DedekindReal.ref](../libs/real/src/DedekindReal.ref)：`IsCut`、`CutSet`、`Real` | `\structure` | 下方集合をデータに、inhabited・proper・lower・rounded・located・分数の同値関係の保存を law の field に持たせる。切断の性質を深い連言から取り出す部分を整理できる。 |

AxiomaticReals の参照先は [AxiomaticReals.Laws](../libs/real/src/AxiomaticReals/Laws.ref)、[DedekindReal の Field](../libs/real/src/DedekindReal/Operations/Closed/Field.ref)、[CauchyReal.Completeness](../libs/real/src/CauchyReal/Completeness.ref)、[DedekindReal.Completeness](../libs/real/src/DedekindReal/Completeness.ref)。
CauchySeq の変更は `Sequences`、`Order`、`Quotient` 以下の演算・閉性証明・完備性へ、Dedekind の変更は `Order`、`Operations` 以下の切断保存・演算法則・完備性へ反映する。
特に Dedekind の `Real` は現在 `\Pow Rat` の部分型なので、record を介した所属と外延性の証明の書き方を先に決める必要がある。
実数の演算や閉性証明は Set 上の構成であり、上の候補はデータと性質の bundle として評価する。

## libs/tests と周辺の確認

[libs/tests/src/root.ref](../libs/tests/src/root.ref) は空の module `A` だけで、現時点では具体的な書き換え候補がない。
実際の利用例は [tests/projects/library/src/root.ref](../tests/projects/library/src/root.ref) にあり、モノイド・半環の構成と `PairExamples` の一致証明を新しい宣言に合わせて更新できる。
Pair の一致証明は Bool と Nat を使った instance の例なので、対応宣言では一般の Program 型と引数についての coherence を用意する。
[libs/README.md](../libs/README.md) の Bool・Int の公開 API と代数構造の説明も、移行した範囲に合わせて更新する。

その他のファイルでは、`Logic` の law record は構造の law として再利用できる。
`List`、`Option`、`Sum` は Set 上のデータと演算、`Ordering` は Program データと判定命題、`Fraction` は分母の正値性を表現に織り込んだデータ record である。
`Fin`、`FiniteSubset`、各 `Quotient` は自然数・集合・同値類の部分型として使われているので、structure 化の評価には現在の carrier と等式の使い方も含める。

## 進める順序

1. Bool の correspondence と Bijection の structure で、小さい移行をそれぞれ確認する。
2. Int の DiffLoop と演算の correspondence を移し、数学的性質を `::[set]`、実行との接続を `::[coherence]` へ揃える。
3. Monoid から Group・Semiring・Ring・Field へ順に進み、可換版と構造間の変換、RingModule・RingAlgebra を整理する。
4. Topology と AxiomaticRealStructure を移し、それぞれの構成と法則を取り出す箇所を更新する。
5. Pair の汎用 Set API との接続、位相の各表示、Cauchy 列、Dedekind 切断は、表現変更の範囲を確認して個別に進める。

利用箇所は生成される member を直接参照する形に揃える。
各段階で対象パッケージを `--parse-only` で確認し、型検査と依存するパッケージ・利用例の検査を行う。
