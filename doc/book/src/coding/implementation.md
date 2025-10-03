とりあえずここで考えるだけ考えておく。
- global modules := list of module
- module := pair of
  - name: name
  - assumption: list of (var, exp)
  - declaration: list of either
    - inductive: pair of
      - parameter: list of (var, exp)
      - index: list of (var, exp)
      - sort: sort
      - constructors: pair of
        - arg: list of (var, exp)
        - index: list of exp
    - definition: pair of
      - name: name
      - type: exp
      - body: exp
    - theorem: pair of
      - name: name
      - type: exp
      - body: exp
    - import: pair of
      - module: module[by name]
      - arguments: list of (var, exp)
      - name: name
    - child-module: module

## 全体の設計
- front: パースから簡単な意味解析まで行ってしまう。
  - 例として、式の中の identifier が、 module になっているか、 variable ならどこを指しているか
  - AST もここで定義する。
- checker: 実際の checker の動作を定義する。
  - ただし、 IO とは作用しない。
- terminal:
  - IO を制御して適切に checker を呼び出す。

## front の動作
- パース自体は他の crate にお任せする。ただし、 name と variable は全部 identifier とかにしてしまう。
- 全体としての自由変数は存在できない前提とする。
  - AST では、式の中の variable がどこで束縛されているかを位置で示す形にする。
- 名前の被りがないかも調べること。

## checker の動作
- global にすでに check した module の全体を持っておく。
- module 単位での check ... 内部の宣言を全部 check する。
- context に親や自分の module での assum を全部入れておく。
- 各 declaration ごとに checker を動かすイメージ：
  - "内部の状態"としての「過去に行った型チェックの結果」を declaration ごとに持っておく。
  - これはデバッグをする上でも重要。
