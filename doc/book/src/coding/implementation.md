## 全体の設計
lean みたいに、 elaboration というか surface と desugar を分けたほうがいいらしい。
- syntax 側
  - surface exp: ほとんどプログラムと同じ
    - 変数の束縛や、moduleの参照と名前が存在するかを調べないで、そのまま parse する
  - middle: "名前"解決後
    - マクロの展開後
    - 関係する変数を束縛し、module とその名前解決を行う
    - module の平坦化も行う ... 子 module とかはなく、親から parameter を完全に引き継ぐ
  - core exp: kernel 側の言語（ほとんど式のみ）
    - goal を解くのも、式の中で制御できるようにする
- verifier
  - parse: string -> option surface
  - lowering: surface -> option middle
  - elaboration: middle -> option core
  - kernel-checker: core -> bool
