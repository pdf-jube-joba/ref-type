# 複素 K 理論の Thom 類

コンパクト Hausdorff 空間上の連続な複素ベクトル束を扱う。
入口は `Thom[].For[X, F, bundle, compact, hausdorff]` である。
`thom` は束の全空間上のコンパクト台付き群 \(K^0_c(E)\) の元で、`forward` はこの類と底空間の係数との積である。

## Koszul 複体

`Koszul` は全空間への引き戻し束の双対外代数 \(\Lambda^k\pi^*E^*\) と、tautological 切断による内部積を構成する。
`Contraction` と `Algebra` は各次数の内部積、二乗零、外積との符号付き Leibniz 則、Cartan の関係を扱う。
束写像の連続性には既存の `bundle_operations` の外代数、双対、テンソル積とその普遍性を使う。

零切断の外では、切断に値1を取る共変ベクトルとの外積が収縮を与える。
コンパクトな底空間上の階数の一様な上界により、この複体を有限な偶奇複体にまとめる。
`Finite`、`RelativeComplex` と `For.Using[data]` が、実際の有限複体を K10 のコンパクト台付き類へ送る。
`For.Choices`、`For.Bounds` と `For.ChoicesAny` は座標系と切断次数からの独立性を証明する。
`For.thom` は、これらの実際の複体が表す一意な類として定義する。

## 公開 API

| API | 内容 |
| --- | --- |
| `For.thom` / `For.forward` / `For.additive` | 標準の Koszul 類とその積による加法的な写像 |
| `For.Isomorphism.data` | Thom 写像と逆写像、および両側の逆写像則と加法性 |
| `For.ThomPullback.equation` / `forwardNaturality` | 底空間の連続写像に沿う引き戻しとの整合性 |
| `For.BundleIsomorphism.equation` / `forwardNaturality` | 実際の束同型が誘導する proper 引き戻しと Thom 類の比較 |
| `For.Proofs.equation` / `forwardAgreement` | コンパクト性・Hausdorff 性の証明の選択からの独立性 |
| `FiberMultiply.multiply` | 同じ底空間上の二つの束の全空間に対する積 |
| `KoszulProduct.equation` | 直和の Koszul 類が二つの類の積となること |
| `DirectSumIsomorphism.data` / `composition` | 直和に沿う Thom 同型と、底空間からの Thom 写像の合成則 |
| `FiberAssociativity.associativity` / `associationEquivalence` | 束の直和の結合子に沿う、三つの類の積の比較 |
| `TrivialThom` / `TrivializedThom` | 自明束・自明化を指定した束と、底空間と点上の束の外積表示 |
| `Complexification.Compact.Isomorphism.data` | 実束の複素化が持つ標準の複素 Thom 向きへの適用 |

`BundleIsomorphism` は終域のコンパクト性と Hausdorff 性も明示的に受け取る。
全空間の引き戻しには proper 性を証明し、一点コンパクト化上の実際の写像を用いる。

## Bott 類と同型の証明

`Isomorphism.Point[n]` は一点上の自明な複素 \(n\) 次元束と、その実際の Koszul 類を公開する。
階数0では、この類は \(S^0\) の単位類に一致する。
複素直線では、偶奇複体の境界写像を標準座標で計算し、円周上の clutching による Bott 類と比較する。
`Isomorphism.BottExternal[base, n]` は、この点上の Koszul 類との外積による同型を、任意のコンパクトな基点付き空間に対して与える。

直和の比較では、外代数の次数分解と符号付き内部積の式を、連続なテンソル積束と有限な偶奇和へ移す。
`MetricFoldClass` は計量による実際の収縮と、その K10 の局所表示を構成する。
計量・補束による安定化、商上への降下と Clifford 作用素の比較により、標準の Koszul 類と外積の一致を証明する。

一般の束の同型には、局所自明化とコンパクト性から得られる有限次元自明束への埋め込みと、その直交補束を使う。
補束との直和を自明化して Bott 同型へ移し、二度の安定化と直和の結合子を用いて Thom 写像の両側の逆写像を構成する。
`Cancellation` は、この最後の逆写像則に用いる写像の消去法である。
`For.Isomorphism` の公開する逆像は一意な逆像として選ぶので、埋め込みと補束の選択に依存しない。

実束への適用では `Complexification` が既存の連続な複素化束を用い、その複素束の Koszul 類と Thom 同型を返す。
