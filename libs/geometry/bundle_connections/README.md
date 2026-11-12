# 接続と共変微分

`bundle_connections` は [smooth_bundles](../smooth_bundles/README.md) の滑らかな束に接続を構成する。
基底は第二可算 Hausdorff な有限次元実多様体である。
局所枠の接続行列を実際の滑らかな一形式で表し、チャート変更に関するアフィン変換則を証明して貼り合わせる。

## 局所共変微分と接続行列

`Local[n,r].On[U].Connection` は滑らかな係数 \(A_{i,a,b}\) を持つ。
`Of[connection].partial` は \(\nabla_i s=\partial_i s+A_i s\) であり、加法性と滑らかな関数に関する Leibniz 則を満たす。
`Dual` は負の転置行列による双対接続と評価対の微分則、`Of.Tensor` はテンソル積の係数と積の微分則を与える。
`Flat` は零係数の場合に通常の微分へ戻ることと、定数切断が平行であることを証明する。

`Forms[n,r].On[U]` の `Form[k]` は局所枠で表した束値 \(k\) 形式である。
`Connection` は一形式の行列であり、`Covariant` は \(d_A\omega=d\omega+A\wedge\omega\) を構成する。
`Coordinates` と `Coefficients` は局所共変微分係数と一形式行列の間を往復し、両方の復元則を証明する。
`Pullback.Between` は滑らかな写像による形式・接続行列の引き戻しと共変外微分の自然性を与える。
`After` は合成、`Forms.On.Identity` は恒等写像との比較である。

## 大域接続と存在

`Real[n,r].On[M].Family[F,space].Of[I,bundle].Connection` は、B07 の束の各局所枠に接続行列を与え、重なりで変換則を満たす族である。
`existsConnection` は滑らかな従属分割からこの族を構成する。
各枠の平坦接続を別の枠へ移した項に分割の重みを掛け、閉じた台の外では零延長し、局所有限和を取る。
三重の重なりにおけるアフィン cocycle と重みの和が一であることから接続の変換則を導く。
空の添字型も別に処理する。

`SectionCoordinates` は、全空間への写像が滑らかな B07 の切断から局所係数の滑らかさを導き、逆向きにも切断を構成する。
`Operators.covariant` は実際の滑らかな切断に作用し、重なりで整合する束値一形式を返す。
切断の加法・滑らかな関数倍に対する微分則と、局所の `Local.Of.partial` との一致を証明する。

`Complex[n,r].On[M].Family[F,space].Of[I,bundle]` は、複素束の実化上で複素構造 \(J\) を保存する接続を構成する。
任意の実接続の行列 \(A\) を \((A-JAJ)/2\) へ射影し、\(J^2=-I\) と遷移行列の複素線形性から変換則を証明する。
`existsConnection` はこの構成による複素接続の存在である。
`Operators` は実際の切断 \(is\) を構成し、\(\nabla(is)=i\nabla s\) を証明する。

## 束値形式と束演算

`BundleForms[n,r].On[M].Family[F,space].Of[I,bundle].Alternating[k,enumeration].Tensor[enumeration]` は実際の滑らかな束 \(E\otimes\Lambda^kT^*M\) を構成する。
`Form` はその B07 の滑らかな切断であり、零切断と各ファイバーの純テンソルを持つ。
有限添字の列挙は [bundle_operations](../bundle_operations/README.md) の列挙型を使用する。
`TensorIndex` はその列挙上の和と二重和の一致を証明する。

`Real.On.Family.Of.InducedDual[connection].value` は B07 の双対束の接続である。
逆遷移行列の微分と負の転置行列から重なりの変換則を導く。
`PullbackGlobal` は滑らかな写像の始域のチャートと終域の束の枠を共通に細分し、実際の引き戻し束を構成する。
`Exterior` は外冪の交代座標で局所接続係数を構成し、零接続および零次外冪との比較を証明する。

`GlobalForms` は任意次数の局所束値形式に対して引き戻し・制限の自然性、滑らかな行列による枠変更の共変性、右からのスカラー形式との次数付き Leibniz 則を証明する。
`Real.On.Family.Of.ValuedForms[k]` は重なりで整合する局所形式の族であり、`TensorForms.Using.form` がそれを実際の束値形式の滑らかな切断へ送る。
`Operators.TensorForms.Using.derivative` は通常の切断の共変微分をこの切断型で返す。
`GlobalForms.OnManifold.Family.Of.At[k].apply` は次数を一つ上げる大域共変外微分であり、`Native.Using` は結果を実際の束の切断型へ送る。
`Operators.DegreeZero.comparison` は零次において通常の切断の共変微分と一致することを証明する。
`GlobalForms.OnManifold.Family.Of.Wedge.Leibniz` は大域スカラー形式との次数付き Leibniz 則である。
`GlobalForms.Complex.On.Family.Of.At` は複素束の実化上で束値形式を表し、複素構造の作用および複素スカラー倍と共変外微分の交換を証明する。
`PullbackGlobal.Between.Family.Of.Connection.Valued[k].apply` は実際の引き戻し束上の束値形式を返し、`Naturality.law` は大域的な共変外微分との交換を証明する。

`Real.On.Family.Of.InducedPaired.Using.Tensor.value` は B07 のテンソル積束上の誘導接続、`InducedExterior` は B07 の外冪束上の誘導接続を構成する。
テンソル積の係数は \(A\otimes I+I\otimes B\) であり、任意の有限列挙に関して接続の変換則を証明する。
外冪では外冪表現の積を証明し、行列の一次 jet に沿って微分することで誘導係数とその変換則を導く。
`ComplexPullbackGlobal` は複素束の実際の引き戻し束と、複素構造を保存する引き戻し接続を構成する。
`Complex.On.Family.Of.InducedDual.value` は実際の複素双対束上の接続である。
複素共役の実化行列を \(K\) とし、係数 \(-KA^{\mathsf T}K\) を構成する。
双対枠の評価式と実部の双線形対から遷移行列を同定し、変換則と複素線形性を証明する。

複素誘導接続の係数計算には `ComplexMatrices` を用いる。
複素一形式を実部・虚部の対で表し、複素構造と可換な実行列から複素係数を復元する。
`ComplexTensorGauge` は複素有限和のテンソル積恒等式と接続行列の変換則を証明する。
実化と複素テンソル積の階数を区別して扱う。
`Complex.On.Family.Of.Coefficients` は複素接続の局所複素行列を取り出し、`FromCoefficients` は複素行列の変換則から大域接続を構成する。
両方向の復元則と微分・積・引き戻しとの比較を証明する。
`Complex.On.Family.Of.InducedPaired.Using.Tensor.value` と `InducedExterior.value` は B07 の実際の複素テンソル積束・外冪束上の誘導接続である。
`ComplexEvaluation` は滑らかな複素多重線形形式を変化するベクトルに評価した関数の微分を証明し、`ComplexExteriorGauge` はこれを使って外冪表現の微分と枠変更の自然性を導く。

## 計量と Levi–Civita 接続

`Metric` と `ComplexMetric` は実対称計量と Hermitian 計量の局所表示を扱う。
正定値性から逆行列を構成し、その滑らかさを証明する。
`MetricCorrection` は任意の接続を計量適合接続へ補正し、適合性、枠変更・引き戻し・制限に関する自然性、適合する接続を固定することを証明する。
`Real.On.Family.Of.WithMetric` は B07 の実計量に対する大域的な適合接続の存在を与える。
`Complex.On.Family.Of.WithMetric` は Hermitian 計量の実部と複素構造を用い、同じ存在を与える。
虚部は \(\operatorname{Im}h(v,w)=-\operatorname{Re}h(v,iw)\) から復元する。

`LeviCivita[n].On[U].Riemannian[metric]` は Koszul の係数を逆計量で上げた接続を構成する。
捩率が零であることと計量適合性を直接証明し、`Unique.unique` は両条件を満たす接続の一意性を与える。
`CoordinateChange` は実際の座標変換の Jacobian と Hessian を使い、混合偏微分の交換から捩率の変換則を導く。
局所一意性によって接続行列のアフィン変換則を得る。
`OnManifold.With[metric].connection`、`laws`、`unique`、`value`、`exists` は B07 の接束計量に対する大域 Levi–Civita 接続、その性質、一意性、存在である。
`Restriction` と `Euclidean` は開集合への制限と標準 Euclid 計量の平坦接続との比較を与える。

## 例と検査

`Examples` は零次元基底上の実・複素零階数束、一次元の非零定数接続に対する \(\nabla 1=1\)、平坦接続の定数平行切断、標準 Euclid 計量の Levi–Civita 接続を扱う。

```sh
cargo build -p cli --release --locked
python3 scripts/check_all.py libs/geometry/bundle_connections
python3 scripts/check_all.py
```
