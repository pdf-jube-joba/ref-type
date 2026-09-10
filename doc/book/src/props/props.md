# 体系の性質

[system.md](../system.md) の体系について、構文・導出・集合モデルの性質をまとめる。
現行 core に対する相対無矛盾性の議論は、一般の datatype 宣言を除いた範囲を対象とする。
型コードモデルと証明項の消去により、この core の相対無矛盾性を外部の集合論的仮定だけから示す。
従来の非コード化モデルの TC と元の体系の一般の subject reduction は、この証明の前提ではない。
補助体系 \(\mathcal S_+\) では、generation と一般の subject reduction、
型付きの共通簡約先まで証明できている。
現行規則への対応と各結果の到達点は[証明全体の整理](proof.md)を参照する。
conversion を一切使わない Box-free 部分体系については、[相対無矛盾性の証明](soundness.md#conversion-free)を与える。

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
