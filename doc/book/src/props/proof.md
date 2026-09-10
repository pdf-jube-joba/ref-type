# Core calculus の相対無矛盾性

対象は [system.md](../system.md) の、一般の datatype 宣言を除いた体系である。
Box を含む体系を \(\mathcal S_\Box\)、Box 関係の構文・規則を除いた体系を
\(\mathcal S_0\) と書く。判断は有限導出によって生成する。
well-termination の略記は、その二つの判断の導出へ展開して数える。

> **証明の到達点。**
> datatype を除く現行 core について、外部の集合論的仮定だけから相対無矛盾性を示す。
> 新しい型コードモデルと証明項の消去により、raw conversion を含む全導出を
> 意味的 conversion の補助体系へ移す。従来の候補解釈の未証明条件 TC は仮定しない。
> Box は既存の消去定理で扱う。一般の datatype への拡張は未証明である。

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

完成した core の証明は

\[
\mathcal S_\Box\ \longrightarrow\ \mathcal S_0\ \subseteq\ \mathcal S_+
\ \xrightarrow{\epsilon}\ \mathcal H
\quad+\quad\mathcal H\text{ の健全性}
\quad+\quad\langle\bot\rangle=0
\]

という構成である。\(\mathcal H\) の健全性と簡約保存を先に証明してから、
最後の導出移送で元の raw conversion を取り込む。
\(\mathrm{TC}\) を外部集合論の公理に紛れ込ませない。

## 証明の構成

導出の基本補題と Box 消去、補助 reduction の合流性を用意し、型コードモデルへ進む。

- [構文的補題](metatheory.md)：束縛と raw 代入の合成。
- [合流性](confluence.md)：補助 reduction による共通簡約先と head の区別。
- [Typing](typing.md)：weakening、substitution、Regularity、および subject reduction の到達点。
- [Generation](generation.md)：補助体系で refinement を含む導出から導入時の型を回収する。
- [Subject reduction](subject_reduction.md)：補助体系での一般の保存と型付きの共通簡約先。
- [Box 消去](box_elimination.md)：reflection と Box-free core への導出の移送。
- [型コードモデル](coded_model.md)：rank 再帰によるコード、decoding、証明消去、universe 閉性。
- [Conversion と無矛盾性](semantic_conversion.md)：補助体系の健全性・意味保存、元の導出の移送、最終定理。
- [従来の集合モデル](model.md)：再利用する集合演算と、別の候補解釈に対する条件 TC。
- [従来の条件付き健全性](soundness.md)：非コード化解釈についての条件付き定理。

## 結果と残る証明義務

| 結果 | 到達点 | 証明 |
| --- | --- | --- |
| raw 代入・導出の代入 | 証明済み | [構文的補題](metatheory.md)、[typing](typing.md) |
| context conversion | 証明済み。SR を使わない | [typing](typing.md) |
| 補助 reduction の合流性 | 証明済み。元の reduction の合流性とは別 | [confluence](confluence.md) |
| refinement を含む generation | \(\mathcal S_+\) で証明済み。型の一意性は使わない | [generation](generation.md) |
| 一般の SR と型付きの共通簡約先 | \(\mathcal S_+\) で証明済み | [subject reduction](subject_reduction.md) |
| Box 消去 | 型引数への btapp を含めて証明済み | [Box 消去](box_elimination.md) |
| 型コードモデルと元の導出の移送 | TC の仮定なしに証明済み | [型コード](coded_model.md)、[意味保存](semantic_conversion.md) |
| 従来の非コード化モデルの健全性 | その解釈の TC を仮定した定理 | [健全性](soundness.md) |
| conversion を一切使わない Box-free 部分体系の無矛盾性 | 外部の集合論的仮定だけで証明済み | [部分体系の系](soundness.md#conversion-free) |
| 現行 core の相対無矛盾性 | 外部の集合論的仮定だけから証明済み | [最終定理](semantic_conversion.md#相対無矛盾性) |
| datatype を含む体系への拡張 | 未証明 | [拡張に必要な事項](#datatypes) |

従来の解釈についての [Semantic-step-plus](subject_reduction.md#semantic-step) は未証明のままだが、
core の無矛盾性証明の前提ではなくなった。
新しいモデルでは、関数型のコードが domain と fiber の情報を保持し、
意味的 conversion を経た lambda の generation を直接示せる。
命題の product は真理値に潰れるため、proof を返す lambda/application は先に消去する。
これにより、\(\mathcal H\) の一歩保存をその健全性の後に独立に証明できる。
元の \(\mathcal S_0\) の一般の SR も、この証明の追加仮定ではない。

[Stratified judgement](stratified_judgement.md) の議論は、この証明では利用しない。
その議論は全 product rule に \(\sigma_2=\sigma_3\) を仮定しているが、
現行の \((*^s_1,*^s_0,*^s_1)\in\mathcal R_s\) はその仮定を満たさない。
また、構文 family の保存だけでは、raw zigzag の中間項の typing や意味保存は保証されない。

## Core の無矛盾性

**定理。** [集合論的仮定](model.md#universes)のもとで Consistency が成り立つ。

**証明。** [Coded-embedding と Core-consistency](semantic_conversion.md)を使う。
\(\bot\) の解釈は 0 であり、空 context は valid valuation を持つ。
仮に core の証明があれば H に移せるが、H の健全性はそれぞれ
\(0=1\)、\(0\in0\) を要求して矛盾する。
Box 付きの証明は Clear で先に消去する。□

これは文書上の数学的証明であり、証明支援系による機械検証までは行っていない。

## 従来の解釈に対する条件付き定理

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

これは従来の候補解釈に対する TC 以外の接続を記録した定理である。
上の型コードモデルによる無矛盾性は、この条件付き定理を経由しない。

<a id="datatypes"></a>

## 一般の datatype を含める場合

ここまでの定理は、datatype の宣言・constructor も含めて除いた core の定理である。
Set case だけを除けば十分、とはしていない。
拡張には以下が必要になる。

1. declaration environment と strict positivity の形式的な定義。
2. reflection 後の signature の positivity と universe 内の最小不動点の構成。
3. Program case を含む reflection の全域的な定義と対応する Set case の規則。
4. case の代入・簡約 simulation と Box 消去の追加 case。
5. 追加規則についてのコードモデルの健全性、消去後の合流性と H-step、導出の移送。

また、well-termination の定義に Set typing が含まれることと、
Program の operational な停止性を示すことは別である。
後者の定理はここでは主張しない。
