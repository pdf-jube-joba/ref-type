# 体系の性質

[system.md](../system.md) の体系について、構文・導出・集合モデルの性質をまとめる。
現行 core に対する相対無矛盾性の議論は、一般の datatype 宣言を除いた範囲を対象とする。
raw conversion の意味保存 TC と一般の subject reduction は未証明であり、無条件の相対無矛盾性証明はまだ完成していない。

- [相対無矛盾性](proof.md)：目標、証明の構成、条件付きの結論、datatype への拡張。
- [構文的補題](metatheory.md)：束縛と raw 代入。
- [合流性](confluence.md)：補助 reduction の共通簡約先と head の区別。
- [Typing](typing.md)：導出の基本補題と subject reduction。
- [Box 消去](box_elimination.md)：reflection と導出の保存。
- [集合モデル](model.md)：集合演算、raw 項・context の解釈、条件 TC。
- [条件付き健全性](soundness.md)：TC を仮定した健全性と残る証明義務。
- [Stratified judgement](stratified_judgement.md)：sorted PTS と判断の層化に関する検討メモ。

Typing・合流性・集合モデルの旧記法による検討は、各ページ末尾に保存している。
