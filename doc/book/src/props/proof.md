# Core calculus の相対無矛盾性

対象は [system.md](../system.md) の、一般の datatype 宣言を除いた体系である。
Box を含む体系を \(\mathcal S_\Box\)、Box 関係の構文・規則を除いた体系を
\(\mathcal S_0\) と書く。判断は有限導出によって生成する。
well-termination の略記は、その二つの判断の導出へ展開して数える。

> **証明の到達点。**
> 現行の構文 family・rule label・多相 Program 型を含めて、Box 消去、構文的代入、
> context conversion、集合演算の構成、および条件付き健全性を示す。
> さらに、補助体系 \(\mathcal S_+\) では refinement を含む generation と一般の SR、
> 型付きの共通簡約先を示す。
> raw conversion の意味保存 \(\mathrm{TC}\) は未証明である。
> したがって、現行体系の無条件の相対無矛盾性証明はまだ完成していない。
> 元の \(\mathcal S_0\) の一般の SR と、\(\mathcal S_+\) の SR は区別する。

## 証明すべき命題

\[
\bot:=\Pi_{(\square^p,*^p,*^p)}X_{*^p}:*^p.X_{*^p}.
\]

\((*^p,\sq^p)\in\mathcal A\)、
\((\sq^p,*^p,*^p)\in\mathcal R\) より \(\emptyset\vdash_0\bot:*^p\)。
目標は、外部の集合論 \(\mathsf{ZFC}\) と [集合モデルの universe 仮定](model.md#universes)のもとで

\[
\neg(\emptyset\vDash_\Box\bot),\qquad
\neg\exists t.\ \emptyset\vdash_\Box t:\bot
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
- [Generation](generation.md)：補助体系で refinement を含む導出から導入時の型を回収する。
- [Subject reduction](subject_reduction.md)：補助体系での一般の保存と型付きの共通簡約先。
- [Box 消去](box_elimination.md)：reflection と Box-free core への導出の移送。
- [集合モデル](model.md)：universe、集合演算、raw 項と context の解釈、未証明の条件 TC。
- [条件付き健全性](soundness.md)：TC を仮定した各規則の健全性と、TC の残る証明義務。

## 総合したときに残る証明義務

| 結果 | 到達点 | 証明 |
| --- | --- | --- |
| raw 代入・導出の代入 | 証明済み | [構文的補題](metatheory.md)、[typing](typing.md) |
| context conversion | 証明済み。SR を使わない | [typing](typing.md) |
| 補助 reduction の合流性 | 証明済み。元の reduction の合流性とは別 | [confluence](confluence.md) |
| refinement を含む generation | \(\mathcal S_+\) で証明済み。型の一意性は使わない | [generation](generation.md) |
| 一般の SR と型付きの共通簡約先 | \(\mathcal S_+\) で証明済み | [subject reduction](subject_reduction.md) |
| Box 消去 | 型引数への btapp を含めて証明済み | [Box 消去](box_elimination.md) |
| 集合モデルの健全性 | TC を仮定した定理 | [健全性](soundness.md) |
| conversion を一切使わない Box-free 部分体系の無矛盾性 | 外部の集合論的仮定だけで証明済み | [部分体系の系](soundness.md#conversion-free) |
| 現行 core の無条件の相対無矛盾性 | 未証明。TC が残る | [TC の証明義務](soundness.md#tc-obligation) |
| datatype を含む体系への拡張 | 未証明 | [拡張に必要な事項](#datatypes) |

従って、これらの文書を合わせても、現時点では現行体系の無条件の相対無矛盾性は出ない。
補助体系を経由する経路では、subset を含む generation、一般の SR、
型付きの共通簡約先までは得られた。
残るのは[型付き一歩簡約の意味保存](subject_reduction.md#semantic-step)を、
健全性の証明との循環なしに示すことである。
これが得られれば \(\mathrm{TC}_+\)、元の TC、現行 core の無矛盾性が順に従う。
この経路では、元の \(\mathcal S_0\) の SR を追加の仮定にする必要はない。

[Stratified judgement](stratified_judgement.md) の検討は、この穴を埋めない。
その議論は全 product rule に \(\sigma_2=\sigma_3\) を仮定しているが、
現行の \((*^s_1,*^s_0,*^s_1)\in\mathcal R_s\) はその仮定を満たさない。
また、構文 family の保存だけでは、raw zigzag の中間項の typing や意味保存は保証されない。

## 条件付きの無矛盾性

**定理。** [集合モデルの集合論的仮定](model.md#universes)と [TC](model.md#tc) のもとで Consistency が成り立つ。

**証明。**
\[
\llbracket\bot\rrbracket
=\operatorname{Prod}(\mathbb B,P\mapsto P)=0.
\]
実際、\(0\in\mathbb B\) に対応する fiber が空である。
もし \(\emptyset\vDash_0\bot\) なら [Soundness](soundness.md) により同じ値が 1 となって矛盾。
もし \(\emptyset\vdash_0t:\bot\) なら [Soundness](soundness.md) により
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
