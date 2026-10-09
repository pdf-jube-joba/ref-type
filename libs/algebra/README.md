# 抽象代数

`std.Alg` の構造を入力として、準同型、商、群完成、多項式環を構成する。
直接依存は `std` で、公開 module は [root.ref](src/root.ref) にある。

## 構成と定理

| module | 公開する内容 |
| --- | --- |
| `Hom` | モノイド・群・半環・環の準同型とモノイド準同型の合成。 |
| `Quotient` | 同値関係による商、演算の降下、代表元によらない写像の一意な延長。 |
| `Quotient.Groups` / `Quotient.Rings` | 合同関係による可換群・可換環の商構造。 |
| `Group.Of.Subgroups` | 零元・和・逆元で閉じた部分集合上の可換群。 |
| `GroupCompletion.Of` | 一般の可換モノイドの群完成と、可換群への準同型の一意な延長。 |
| `GroupCompletion.Natural` | 自然数の加法モノイドの群完成と既存の整数との同型、加法の保存。 |
| `GroupCompletion.Semiring` | 半環の群完成の環構造、半環準同型の環準同型への一意な延長、積の可換性の保存。 |
| `Exact` | 核・像・完全性、完全性から合成が零になること、可換群準同型の核・像の群構造。 |
| `Module.Over` | 台集合と加群構造の束、準同型の可換加法群、部分加群・核・像・商。 |
| `Module.Over.FirstIsomorphism` | 核による商と像との同型。 |
| `Module.Over.Presentation` / `Free` | 形式和と関係による加群、生成元による準同型の一意な延長、自由加群の射影性。 |
| `Module.Over.Free.Coefficients` / `Finite` | 係数写像、有限生成元による展開、有限支持関数との同型。 |
| `Module.Over.FiniteCoordinates` | 有限座標加群、標準基底による展開、有限集合上の自由加群との同型、先頭座標と残りの座標の分解、零拡張と先頭が零の部分加群との同型。 |
| `Module.Commutative.Matrix` | 有限自由加群の準同型と行列の往復、積と合成、転置、恒等行列、逆行列と加群同型の対応。 |
| `IntegerMatrix` | 有限行列から自然数添字の表現への拡張と往復、整数行列の実行可能な積、行・列の基本変形、転置、恒等行列、領域内の非零成分の探索と型付き行列との対応。 |
| `Module.Commutative.Elementary` | 行交換、異なる行の整数倍の加算、符号反転の加群同型と逆行列の証明。 |
| `IntegerDiagonal` / `IntegerKernel` / `IntegerBasis` | 対角行列の核、Smith 標準形から得た元の行列の核の自由座標、実行可能な基底行列と逆座標行列、その成分と核の同型の対応、像の階数と自由基底。 |
| `Module.Over.KernelTransport` | 可換な基底変更に沿う核と余核の同型、商の類での写像の計算。 |
| `Smith` | 辞書式に停止する Smith 標準形の機械、非負の対角成分・整除列・階数の証明、実行可能な変換行列と逆行列、履歴からの可逆性と \(UAV=D\) の証明。 |
| `IntegerIdeals` / `IntegerSubmodules` | 整数部分加群の主イデアル表示、有限自由整数加群の部分加群の有限生成性、生成行列から得た自由基底と部分加群との同型。 |
| `Module.Over.Product` / `DirectSum` | 任意添字の積・直和、有限支持族との同型、成分の包含、直和からの準同型の普遍性と射影性、生成元と加群演算による `Generated.induction`。 |
| `Module.Over.FinitelySupported` | 任意加群族の積における有限支持部分加群。 |
| `Module.Over.Biproduct` | 二項直和と積、射影・包含、組と余組の普遍性。 |
| `Module.Over.ShortExact` / `ShortExactComparison` | 短完全列、分裂から得られる直和同型、可換図式の比較。 |
| `Module.Over.Pushout.On` | 二つの準同型の押し出しと、可換な写像からの一意な準同型。 |
| `Module.Over.ShortExact.Pushout.On` | 短完全列を左端の係数写像に沿って押し出した短完全列。 |
| `Module.Over.CanonicalFree` / `FreeResolution` | 元の集合上の自由加群からの全射、反復する核、射影的な各項と隣接する微分の完全性。 |
| `Module.Commutative.HomSpace` / `FreeHom` | 準同型の加群構造と \(\operatorname{Hom}_R(R^{(S)},A)\cong A^S\)。 |
| `Module.Commutative.Tensor.Adjunction` | テンソル積の双線形な普遍性と Hom–tensor の加群同型。 |
| `Module.Commutative.ProjectiveTensor`、`ProjectiveTensorShortExact` | 射影加群とのテンソル積による単射性・短完全列の保存。 |
| `Module.Commutative.TensorProjective` | 二つの射影加群のテンソル積の射影性。 |
| `FreeCommutativeRing.Over.Presentation` | 係数環と変数・関係から作る可換環の表示と普遍性。 |
| `Polynomial.Over` | 一変数多項式環、係数写像と変数の値で定まる評価準同型とその一意性。 |
| `LaurentPolynomial.Over` | Laurent 多項式環、可逆元への評価準同型とその一意性。 |

可換モノイドの群完成は、形式差の関係

\[
(a,b)\sim(c,d)\quad\Longleftrightarrow\quad\exists e,\quad a+d+e=c+b+e
\]

で定義する。
この関係の同値性、演算との整合性、群の法則、普遍性を証明している。
半環の積は加法に関する普遍性を二度使って延長する。

多項式環と Laurent 多項式環は、式の集合を最小の環合同関係で割って構成する。
`FreeCommutativeRing` の表示は追加の関係を持つ係数環上の可換環にも利用できる。
係数列による正規形、次数、体上の除法と互除法は次の実装単位となる。

## 型検査

リポジトリのルートで実行する。

```sh
target/debug/cli libs/algebra --no-cache --diagnostics compact
```

群完成の具体化には `GroupCompletion.Of[M := ..., monoid := ...]` を使う。
`Universal[K := ..., target := ...]` の `extension` と `unique` が、準同型の延長とその一意性を提供する。
型検査時に確認した言語上の制約と比較例は [gaps.md](../../_plans/gaps.md#g03) にある。

## 体上の有限次元部分空間

`FieldSubspaces.Over` は、体と有限座標空間の部分加群から線形な引き戻しの存在を証明する。
`Dimension.Of.Retraction` は部分空間への写像と包含との左逆の法則を持つ。
`existence` は次元による帰納法で引き戻しを構成し、`projective` は有限自由加群の直和因子として部分空間の射影性を示す。
