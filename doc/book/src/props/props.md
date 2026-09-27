# 体系の性質

## 証明の適用範囲

この章の既存の証明は、[分類付き補助体系](sorted-calculus.md)の構文・型判断を対象とする。
各 family と product rule の label を保持するため、証明消去を raw 構文上の写像として定義できる。
[system.md](../system.md) の共通項では、分類と product 関係を型判断から導出する。
この PTS に相対無矛盾性の結果を移すには、型付き共通項と conversion の導出を分類付き補助体系へ移送し、代入・reflection・証明消去との対応を示す必要がある。
この移送と一般の datatype への拡張は、残る証明義務である。

分類付き補助体系の datatype を除いた core については、型コードモデルと証明項の消去による相対無矛盾性の議論を保持する。
補助体系 \(\mathcal S_+\) の generation、subject reduction、型付き共通簡約先の主張も、この分類付き表現に対する結果である。
各結果と仮定は[証明全体の整理](proof.md)を参照する。

- [相対無矛盾性](proof.md)：目標、完成した core の証明、datatype への拡張。
- [構文的補題](metatheory.md)：束縛と raw 代入。
- [合流性](confluence.md)：補助 reduction の共通簡約先と head の区別。
- [Typing](typing.md)：導出の基本補題と subject reduction。
- [Generation](generation.md)：refinement を含む導出からの型の回収。
- [Subject reduction](subject_reduction.md)：補助体系の一般の保存と型付きの共通簡約先。
- [Box 消去](box_elimination.md)：reflection と導出の保存。
- [型コードモデル](coded_model.md)：型の構造を保持するコードと decoding、証明消去。
- [Conversion と無矛盾性](semantic_conversion.md)：意味保存と元の全導出の移送、最終定理。
- [集合モデル](model.md)：集合演算、raw 項・context の解釈、条件 TC。
- [条件付き健全性](soundness.md)：TC を仮定した健全性と残る証明義務。
- [Stratified judgement](stratified_judgement.md)：sorted PTS と判断の層化に関する検討メモ。

Typing・合流性・集合モデルの旧記法による検討は、各ページ末尾に保存している。
