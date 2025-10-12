## 全体の設計
lean みたいに、 elaboration というか surface と desugar を分けたほうがいいらしい。

- syntax 側
  - surface exp: ほとんどプログラムと同じ
  - core exp: ほとんど理論と同じ
- verifier
  - parse: string -> result surface string
  - lowering: surface -> result core string
  - checker: core -> result () string
