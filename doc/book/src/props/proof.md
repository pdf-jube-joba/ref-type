# Core calculus の相対無矛盾性

対象は [system.md](../system.md) の、一般の datatype 宣言を除いた体系である。
Box を含む体系を \(\mathcal S_\Box\)、Box 関係の構文・規則を除いた体系を
\(\mathcal S_0\) と書く。判断は有限導出によって生成する。
well-termination の略記は、その二つの判断の導出へ展開して数える。

> **証明の到達点。**
> Box 消去、構文的代入、集合演算の構成、および下記の条件付き健全性を示す。
> raw conversion の意味保存 \(\mathrm{TC}\) は未証明である。
> したがって、現行体系の無条件の相対無矛盾性証明はまだ完成していない。
> subject reduction の一般形も、[typing の principal root の場合](typing.md#principal-root)と区別する。

## 証明すべき命題

\[
\bot:=\Pi P^{\sq^p}:*^p.P.
\]

\((*^p,\sq^p)\in\mathcal A\)、
\((\sq^p,*^p,*^p)\in\mathcal R\) より \(\emptyset\vdash_0\bot:*^p\)。
目標は、外部の集合論 \(\mathsf{ZFC}\) と [集合モデルの universe 仮定](model.md#universes)のもとで

\[
\neg(\emptyset\vDash_\Box\bot),\qquad
\neg\exists t.\ \emptyset\vdash_\Box t:\bot:*^p
\tag{Consistency}
\]

を示すことである。これは強正規化、Program の停止性、型検査の決定可能性とは別の命題である。

以下の証明は

\[
\text{Box 消去}\quad+\quad
\bigl(\mathrm{TC}\Longrightarrow\mathcal S_0\text{ の健全性}\bigr)
\quad+\quad\llbracket\bot\rrbracket=\varnothing
\]

までを与える。\(\mathrm{TC}\) を外部集合論の公理に紛れ込ませない。

## 証明の構成

導出の基本補題から Box 消去へ進み、Box-free core の集合モデルと条件付き健全性を使う。

- [構文的補題](metatheory.md)：束縛と raw 代入の合成。
- [合流性](confluence.md)：補助 reduction による共通簡約先と head の区別。
- [Typing](typing.md)：weakening、substitution、Regularity、および subject reduction の到達点。
- [Box 消去](box_elimination.md)：reflection と Box-free core への導出の移送。
- [集合モデル](model.md)：universe、集合演算、raw 項と context の解釈、未証明の条件 TC。
- [条件付き健全性](soundness.md)：TC を仮定した各規則の健全性と、TC の残る証明義務。

## 条件付きの無矛盾性

**定理。** [集合モデルの集合論的仮定](model.md#universes)と [TC](model.md#tc) のもとで Consistency が成り立つ。

**証明。**
\[
\llbracket\bot\rrbracket
=\operatorname{Prod}(\mathbb B,P\mapsto P)=0.
\]
実際、\(0\in\mathbb B\) に対応する fiber が空である。
もし \(\emptyset\vDash_0\bot\) なら [Soundness](soundness.md) により同じ値が 1 となって矛盾。
もし \(\emptyset\vdash_0t:\bot:*^p\) なら [Soundness](soundness.md) により
\(\llbracket t\rrbracket\in\varnothing\) となって矛盾。
Box 付きの導出は [Box 消去の Clear](box_elimination.md) により Box-free の導出へ移る。□

これは TC を証明したという主張ではなく、TC 以外のモデル側の接続を示す定理である。
現時点で得た結果は「この候補解釈に対する TC が成り立てば無矛盾」であり、
「現行体系の無矛盾性を証明した」ではない。

<a id="datatypes"></a>

## 一般の datatype を含める場合

ここまでの定理は、datatype の宣言・constructor も含めて除いた core の定理である。
Set case だけを除けば十分、とはしていない。
拡張には以下が必要になる。

1. declaration environment と strict positivity の形式的な定義。
2. reflection 後の signature の positivity と universe 内の最小不動点の構成。
3. Program case を含む reflection の全域的な定義と対応する Set case の規則。
4. case の代入・簡約 simulation と Box 消去の追加 case。
5. 追加規則についての健全性、および拡張した raw conversion の TC。

また、well-termination の定義に Set typing が含まれることと、
Program の operational な停止性を示すことは別である。
後者の定理はここでは主張しない。
