# 現在の体系に合わせたライブラリの整理案20件

集合の存在は `\exists`、複数の証人とその条件は法則付きの `\structure`、性質の束は `\Prop` の structure で表す。
各項目は現行の定義を起点にし、導入・消去の証明と利用側までを一つの改修範囲とする。
以下のコードは変更後の定義の案であり、名前を追加する箇所では対応する宣言や import も整える。

## 1. 商の `IsClass` を代表元の存在として書く

対象: [std/Set/Quotient.ref](../libs/std/src/Set/Quotient.ref) の `IsClass` と、[integration/Real/Lebesgue/Def.ref](../libs/integration/src/Real/Lebesgue/Def.ref) の同名の定義。
現在は `\forall (P: \Prop) -> (\forall (x: A) -> C = ClassOf x -> P) -> P` という Church encoding になっている。

```text
\definition IsClass(C: \Pow A): \Prop :=
  \exists { x: A \where C = ClassOf x };
```

「この集合を代表する元が存在する」という条件がそのまま定義になる。
`classIsClass` は `IsClass (ClassOf x)` を結論にして `\exact` で証明し、`induction` と像の閉性証明は `\takefrom` で代表元を取り出す。
Lebesgue 側の `class`、`classProperty`、`induction` と、有理数・整数・Cauchy 実数で `classProperty` を関数適用している箇所も更新する。

## 2. 商の `UnaryImage`・`BinaryImage` を証人の存在として書く

対象: [std/Set/Quotient.ref](../libs/std/src/Set/Quotient.ref) の `UnaryImage`、`BinaryImage`。
どちらも所属条件の中に Church encoding があり、代表元と条件を継続へ順に渡している。
代表元と、その代表元であること、演算結果との関係を法則付きの証人にまとめる。

```text
\structure BinaryWitness[f: A -> A -> A, C, D: \Pow A, z: A]: \Set {
  left: A,
  right: A,
  leftClass: C = ClassOf left,
  rightClass: D = ClassOf right,
  related: Equivalent (f left right) z,
}
\definition BinaryImage(f: A -> A -> A)(C, D: \Pow A): \Pow A :=
  { z: A \where \exists BinaryWitness[f, C, D, z] };
```

単項の場合も同様に一つの代表元を持つ証人を定義する。
`unaryImageClass`、`binaryImageClass`、それぞれの `Closed` の証明を、証人の導入・消去と名前付きの射影で書く。

## 3. 自然数の `Divides` を商の存在として書く

対象: [std/Data/Nat/Division/Prop.ref](../libs/std/src/Data/Nat/Division/Prop.ref) の `Divides`。
現在は因数 `q` と等式を受け取る継続を定義に持つ。

```text
\definition Divides(d, a: Nat^): \Prop :=
  \exists { q: Nat^ \where a = \(d "*" q\) };
```

整除性の内容が直接読め、`dividesAdd`、`dividesMul`、`dividesSub` は因数を取り出して計算する通常の存在証明になる。
`dividesIntro` と、Gcd・Parity を含む利用側の消去も合わせて更新する。

## 4. 切断の `SumMember` を二つの下界の存在として書く

対象: [real/DedekindReal/Cuts/Def.ref](../libs/real/src/DedekindReal/Cuts/Def.ref) の `SumMember` と `SumWitness`。
`SumWitness` は既に条件を名前付きで表しているが、証人 `a, b` の存在だけが Church encoding になっている。

```text
\definition SumMember(x, y: Real)(q: Rat): \Prop :=
  \exists { a: Rat \where
    \exists { b: Rat \where SumWitness[x, y, q, a, b] } };
```

`Cuts/Prop.ref` の `sumIntro`、`sumElim` と和の切断条件の証明を、通常の存在量化の導入・消去へ移す。
証人と条件を一度に利用する箇所では、2番と同じ法則付きの証人を使う形にも整理できる。

## 5. 切断の `ProductBelow` を有理区間の証人にまとめる

対象: [real/DedekindReal/Cuts/Def.ref](../libs/real/src/DedekindReal/Cuts/Def.ref) の `ProductBelow`、`productBelowIntro`。
現在は四つの有理数と八つの条件を継続へ渡しており、各条件の役割を引数の順番で判別する必要がある。
`ProductWitness[x, y, q]: \Set` に `leftLower`、`leftUpper`、`rightLower`、`rightUpper` を置き、切断への所属・非所属と四隅の積に対する下界条件を法則として持たせる。

```text
\definition ProductBelow(x, y: Real)(q: Rat): \Prop :=
  \exists ProductWitness[x, y, q];
```

`productBelowIntro` の結論もこの名前に統一し、`Cuts/Prop.ref` の `productBelowElim` と積の各証明を名前付きの端点・法則で書く。
下端・上端の両方を使う現行の積の定義が、証人の構造に現れる。

## 6. 切断の `ReciprocalBelow` を逆数の証人にまとめる

対象: [real/DedekindReal/Cuts/Def.ref](../libs/real/src/DedekindReal/Cuts/Def.ref) の `ReciprocalBelow`。
現在の Church encoding が隠しているのは、区間の端点 `a, b` と `b` の逆数候補 `r` である。
`ReciprocalWitness[x, q]: \Set` にそれらを置き、下端の所属、上端の非所属、端点の積の正値性、`FractionEq (mulRat b r) oneRat`、`lt q r` を法則にする。
`ReciprocalBelow x q` をその証人型の `\exists` とし、`Cuts/Prop.ref` の `reciprocalBelowElim` と逆数の切断条件の証明を更新する。
`InvLower` の零の場合と非零の場合という場合分けは、この証人とは別の条件として表現する。

## 7. 有理数の `DivisionMember` を分子・分母の代表元の存在として書く

対象: [std/Arithmetic/Rat/Fractions/Quotient.ref](../libs/std/src/Arithmetic/Rat/Fractions/Quotient.ref) の `DivisionMember`、`divisionMemberIntro`。
既存の `DivisionWitness` が必要な法則を持っているので、代表元を存在量化すればよい。

```text
\definition DivisionMember(x: Rat)(y: NonZeroRat)(z: Fraction): \Prop :=
  \exists { a: Fraction \where
    \exists { b: Fraction \where DivisionWitness[x, y, z, a, b] } };
```

[Division/Prop.ref](../libs/std/src/Arithmetic/Rat/Fractions/Quotient/Division/Prop.ref) の `divClassOfRepresentatives` などで `member` に結論の命題を渡している部分を `\takefrom` に置き換える。
商の除法に属するという条件を、実際に使う代表元と方程式で直接記述できる。

## 8. Dedekind 切断族の `UnionMember` を所属する切断の存在として書く

対象: [real/DedekindReal/Completeness.ref](../libs/real/src/DedekindReal/Completeness.ref) の `UnionMember`、`unionIntro`。

```text
\definition UnionMember(S: \Pow Real)(q: Rat): \Prop :=
  \exists { x: Real \where Logic.And[Member S x, mem x q] };
```

現在の二段の含意による Church encoding を、和集合への所属の通常の定義にする。
`unionProper`、`unionLower`、`unionRounded`、`unionRespects`、`supremumLeast` の消去を更新する。
[topology/Topology.ref](../libs/topology/src/Topology.ref) の `UnionMember` は既に同じ存在量化の形なので、ライブラリ間でも表現が揃う。

## 9. `nonnegativeMulElim` の結論を正の下界の存在にする

対象: [real/DedekindReal/Arithmetic/Prop.ref](../libs/real/src/DedekindReal/Arithmetic/Prop.ref) の `nonnegativeMulElim`。
この定理は非負の積の下界から正の有理下界 `a, b` を得ているが、結論が `\forall (P: \Prop) -> (...) -> P` になっている。
正値性、各切断への所属、`lt q (mulRat a b)` を持つ `PositiveProductWitness[x, y, q]: \Set` を定義し、定理の結論を `\exists PositiveProductWitness[x, y, q]` にする。
定理名も存在する証人を表す名前に整え、利用側では証人を取り出して各法則を参照する。
5番が積の所属条件そのものを整理するのに対し、これは追加の非負性の仮定から得られる、より強い証人を定理の結論として明示する変更になる。

## 10. `RelationLe` で標準の `PairToRel` を使う

対象: [real/AxiomaticReals.ref](../libs/real/src/AxiomaticReals.ref) の `RelationLe`。
現在は対を作って関係の集合に所属させる定義を直接書いているが、同じ変換が [std/Logic/Rel.ref](../libs/std/src/Logic/Rel.ref) の `PairToRel` にある。

```text
\definition RelationLe(relation: Rel.RelPair Carrier)(x, y: Carrier): \Prop :=
  Rel.PairToRel Carrier relation x y;
```

`leRelation` の型や、その型を繰り返す法則の添字にも `Rel.RelPair Carrier` を使う。
集合として保存した関係を述語として使う、という体系上の変換を標準の定義に集約できる。

## 11. 同値関係の法則を `Rel.Equivalence` に統一する

対象: [std/Set/Quotient.ref](../libs/std/src/Set/Quotient.ref) と [integration/Real/Lebesgue/Def.ref](../libs/integration/src/Real/Lebesgue/Def.ref) の `EquivalenceLaws`。
どちらも [std/Logic/Rel.ref](../libs/std/src/Logic/Rel.ref) の `Equivalence` と同じ反射律・対称律・推移律を別の record として宣言している。
特に `Rel.QuotientOf.quotient` は `refl/sym/trans` を `reflexive/symmetric/transitive` に詰め直しているだけである。
共通の法則型を使い、必要なローカル名は `\definition EquivalenceLaws: \Prop := Rel.Equivalence[A, Equivalent];` で与える。
`Rel.ref` 側にも商への参照があるため、共通の関係・法則の宣言を `Logic.Rel.Def` などの下位モジュールに切り出して依存方向を整理する。
整数・有理数・Cauchy 実数・Lebesgue の法則の構成と射影を一括で揃える。

## 12. `Bijection` を法則付き structure として直接宣言する

対象: [std/Data/Bijection.ref](../libs/std/src/Data/Bijection.ref) の `BijectionData`、`BijectionLaws`、`Bijection`。
現在は往復の関数、逆写像の法則、それらの refinement を手で分けている。

```text
\structure Bijection: \Set {
  forward: A -> B,
  backward: B -> A,
  leftInverse: \forall (a: A) -> backward (forward a) = a,
  rightInverse: \forall (b: B) -> forward (backward b) = b,
}
```

現行の法則付き structure の展開で同じデータと制約を表せる。
`LeftInverse`・`RightInverse` を独立した述語として使う場合は、二つの関数を引数に取る定義として整理する。
[category/SetValued.ref](../libs/category/src/SetValued.ref) の米田の全単射を含め、既存の構成と射影を検査する。

## 13. 微分可能な関数の束を法則付き structure に揃える

対象: [calculus/Real/Derivative/Def.ref](../libs/calculus/src/Real/Derivative/Def.ref)、[Multivariable/Differential/Def.ref](../libs/calculus/src/Real/Multivariable/Differential/Def.ref)、[Multivariable/Partial/Def.ref](../libs/calculus/src/Real/Multivariable/Partial/Def.ref) の関数の束。
`DifferentiableFunctionData` と `DifferentiableFunctionLaws`、および `PartiallyDifferentiableFunction` の同様の分割を、関数・微分・その法則を持つ一つの structure にする。

```text
\structure DifferentiableFunction: \Set {
  function: Real -> Real,
  derivative: Real -> Real,
  differentiable: HasDerivative function derivative,
}
```

一変数の `constantRaw`、`identityRaw`、`affineRaw` を経由する構成は、法則も記入した literal へ整理する。
多変数では微分の値が `Point -> LinearMap`、偏微分では勾配が `Point -> Point` になる点を保ち、それぞれ同じ宣言形式へ揃える。
[integration/Real/Riemann/Def.ref](../libs/integration/src/Real/Riemann/Def.ref) の `Function` は既にこの形で書かれている。

## 14. 積位相の開矩形を一つの存在証人で表す

対象: [topology/Product.ref](../libs/topology/src/Product.ref) の `RectangleRights`、`RectangleLefts`、`Basis`。
現在は二つの開集合の存在を表すため、中間の部分集合を二段に定義している。
`RectangleWitness[left, right, W]: \Set` に `leftSet: \Pow A`、`rightSet: \Pow B` と `OpenRectangle[left, right, W, leftSet, rightSet]` の法則を持たせる。

```text
\definition Basis(left: Left.Topology)(right: Right.Topology): \Pow (\Pow CarrierSet) :=
  { W: \Pow CarrierSet \where \exists RectangleWitness[left, right, W] };
```

[Product/Universal.ref](../libs/topology/src/Product/Universal.ref) の矩形の導入と消去も、左右の開集合を持つ一つの証人に合わせる。
「開矩形である」という一つの数学的条件が、一つの存在量化になる。

## 15. `GeneratedOpen` は位相そのものを全称量化する

対象: [topology/Topology.ref](../libs/topology/src/Topology.ref) の `GeneratedOpen`。
現在は `candidate: TopologyData` と `TopologyLaws[candidate]` を別々に受け取るが、量化しているのは既に定義された `Topology` の元である。

```text
\definition GeneratedOpen(basis: \Pow (\Pow Carrier))(S: \Pow Carrier): \Prop :=
  \forall (candidate: Topology) ->
    (\forall (U: \Pow Carrier) -> FamilyMember basis U -> IsOpenIn candidate U) ->
    IsOpenIn candidate S;
```

`generatedLaws`、`generatedBasisOpen`、`generatedLeast` を、位相の元から法則を参照する形へ移す。
生成される位相の定義が「指定した族を含むすべての位相で開である」と直接読める。

## 16. `IsCountableBasis` の条件にフィールド名を付ける

対象: [topology/Topology.ref](../libs/topology/src/Topology.ref) の `IsCountableBasis`。
現在は `Logic.And` の左が各基本開集合の開性、右が近傍の細分条件になっている。
`IsCountableBasis[topology, basis]: \Prop` を、`open` と `refines` を持つ structure として宣言する。
内側の「点を含み、指定された開集合に含まれる」という条件にも、必要なら `BasisNeighborhood[topology, basis, U, x, n]: \Prop` として `contains`、`within` の名前を付ける。
[Topology/Countability.ref](../libs/topology/src/Topology/Countability.ref) の可算部分被覆の証明や可算基底の構成を、役割の分かる射影へ更新する。

## 17. 開被覆と有限部分被覆の条件を名前付きの命題にする

対象: [topology/Topology.ref](../libs/topology/src/Topology.ref) の `IsOpenCover`、`IsCompactIn`。
`IsOpenCover` は被覆性と各集合の開性を `Logic.And` で持ち、`IsCompactIn` は有限族が元の族に含まれることと被覆性を、再び匿名の `Logic.And` で持つ。
前者を `covers`、`open` のフィールドを持つ `\Prop` の structure にし、後者を `FiniteSubcover[family, S, finite]: \Prop` として `included`、`covers` を持たせる。

```text
\definition IsCompactIn(topology: Topology)(S: \Pow Carrier): \Prop :=
  \forall (family: \Pow (\Pow Carrier)) -> IsOpenCover[topology, family, S] ->
    \exists { finite: FiniteFamilies.FiniteSubset \where FiniteSubcover[family, S, finite] };
```

[Topology/Normality.ref](../libs/topology/src/Topology/Normality.ref) と [Topology/Countability.ref](../libs/topology/src/Topology/Countability.ref) の被覆の導入・消去も合わせる。
コンパクト性の証人が持つ二つの役割を、その利用箇所でも明示できる。

## 18. 上限の条件を `upper`・`least` の法則にまとめる

対象: [real/DedekindReal/Completeness.ref](../libs/real/src/DedekindReal/Completeness.ref) の `LeastUpperBound` と、[real/AxiomaticReals.ref](../libs/real/src/AxiomaticReals.ref) の `IsLeastUpperBound`、`Complete`。
現在は上界であることと最小性を `Logic.And` で表し、`Complete` には同じ条件をさらに直接書いている。
それぞれの順序に対して `upper` と `least` を持つ `\Prop` の structure を定義し、完備性の存在量化もその型を参照する。
`supremumLaw`、上限の一意性、Cauchy 実数から公理的実数への完備性証明を名前付きの射影に揃える。
これにより「左の証明」「右の証明」の読み替えがなくなり、`Complete` と `Completeness` の上限条件も同じ定義を共有できる。

## 19. 既存の部分集合型をそのまま存在量化する

対象: [linear_algebra/Field/Space/Finite.ref](../libs/linear_algebra/src/Field/Space/Finite.ref) の `FiniteDimensional` と、[topology/MetricSpace.ref](../libs/topology/src/MetricSpace.ref) の `IsOpen`。
前者は直前に定義した `Basis` の refinement をもう一度展開し、後者は既存の `NeighborhoodRadius` への所属で再び集合を内包している。

```text
\definition FiniteDimensional: \Prop := \exists Basis;

\definition IsOpen(metric: Metric)(U: \Pow Carrier): \Prop :=
  \forall (x: Carrier) -> T.Member U x ->
    \exists \Cast[R.Real] (NeighborhoodRadius metric U x);
```

同様に、`AxiomaticReals.Inhabited` と `DedekindReal.Completeness.Nonempty` は既存の集合に対する `\exists \Cast[...]` で表す。
存在命題が対象の型・集合を直接参照するため、条件を変更するときの定義の重複が減る。
利用側の `\takefrom` と `\exact` の型も同じ名前に揃える。

## 20. 線形写像の零保存を導出される既定の法則にする

対象: [linear_algebra/Field/Space/Linear.ref](../libs/linear_algebra/src/Field/Space/Linear.ref) の `MapLaws.preservesZero`。
現在は各線形写像の構成で零保存を独立に証明しているが、加法保存と加法群の法則から導ける。
`preservesAdd` を先に宣言し、その後に既定の証明を持つ `preservesZero` を置く。
証明は `f(0 + 0) = f(0) + f(0)` と `0 + 0 = 0` から `f(0) + f(0) = f(0)` を作り、[Space/Laws.ref](../libs/linear_algebra/src/Field/Space/Laws.ref) の `idempotentZero` を適用すればよい。
この導出を補題にする場合は、加法保存の仮定を補題の命題内で量化する。
`Linear/Operations.ref` の零写像・和・スカラー倍、`Composition.compose`、座標写像などは既定の証明を使う構成へ整理する。
既存の射影 `preservesZero` を数学的に導かれる法則として提供できる。

## 実装時の確認

1〜9番は存在証明を直接関数適用している利用側まで同時に更新し、各定義の導入・消去と代表元による計算の証明を検査する。
10〜20番は変更した型・射影・literal の参照を検索し、関連するライブラリと利用例まで揃える。
`libs/README.md` の型検査手順に従い、各ライブラリと `tests/projects/library`、`tests/projects/category` を `--no-cache` で検査する。

調査時には、1番の存在量化による `IsClass`、その導入と `\takefrom` による消去、2番の法則付き `BinaryWitness` と `BinaryImage` の最小例を、既存の `target/debug/cli` で検査した。
全20件を既存ライブラリへ適用した際の型検査は、各改修の実装時に行う。
