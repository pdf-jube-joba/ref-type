# Core calculus の構文的補題

この文書では [`system.md`](../system.md) の、一般の datatype 宣言を除いた
core を扱う。集合モデル、無矛盾性、subject reduction は仮定しない。
特に、合流性だけから subject reduction が従うとは主張しない。
合流性と head の区別は[合流性](confluence.md)、導出の基本補題と subject reduction は[typing](typing.md)、
モデルの構成は[集合モデル](model.md)、証明全体の到達点は[相対無矛盾性](proof.md)を参照する。

<a id="substitution"></a>

## 束縛と代入

項は alpha 同値で同一視する。変数の sort 注釈は名前の一部とし、
代入 \(t[x^s:=u]\) はその注釈を持つ変数だけを置換する。
lambda、product、subset は表示された変数を body で束縛する。
`prec` の \(x^s.P\) は \(P\) の中だけで \(x^s\) を束縛する。
従って motive への代入はこの局所変数を避ける。
Program の binder は Set の binder と別の名前空間に置く。

以下の式は、\(x\ne y\)、\(y\notin\mathrm{FV}(u)\) のもとで成り立つ。

\[
t[y:=v][x:=u]
=_\alpha t[x:=u][y:=v[x:=u]].
\tag{subst-comp}
\]

**証明。** \(t\) の構造帰納法。変数 \(x\)、変数 \(y\)、その他の変数、
sort の四場合では両辺を代入の定義で展開する。
束縛を持たない constructor では各引数への帰納法の仮定を使う。
束縛 constructor では、その局所変数を \(x,y,u,v\) の自由変数と
異なる名前へ alpha-renaming してから、annotation と body に帰納法を使う。
閉じた Program payload への Set 変数の代入は恒等である。□

同じ証明から、自由変数を capture しない renaming と代入の可換性を得る。
