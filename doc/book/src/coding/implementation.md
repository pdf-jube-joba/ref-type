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

## module について...
surface 側で定義しているけれど、 kernel 側では context にしてしまう。
```
mod A(
  P1: Set,
) {
  mod B(
    P2: Set,
  ) {
    mod B2(
      P22: Set,
    ) {
      definition t: P2 -> P22 -> Nat := (_: P2) => (_: P22) => Nat;
    }
  }

  mod C(
    P3: Set,
  ) {
    definition X: P3 -> P3 -> Nat := $root.A(P1 := P1).B(P2 := P3).B2(P22 := P3).t;
    definition Y: P3 -> P3 -> Nat := $parent.B(P2 := P3).B2(P22 := P3).t;

    import $parent.B(P2 := P3) as CB;
    definition Z: P3 -> P3 -> Nat := CB.B2(P22 := P3).t;
  }
}

```
こういう状況で `mod C` の検査をしているときにどうするか...
`mod C` の検査時に、 elaborator には次が入っている？
- `[["A", [(Var("P1")], Set)], ["C", [(Var("P3"), Set)]]]`

このとき、
- root の場合には、素直に代入をしていけばいい。
- parent の場合には、 root から同じ変数への代入を下と考えればいい。
- name の場合には事前に代入したものから再びたどっていく

いずれにせよ、 ModPath の解決後を持っておけばいい？
- `$root.A(P1 := P1).B(P2 := P3).B2(P22 := P3)` も `$parent.B(P2 := P3).B2(P22 := P3)` も、
  `"B2"` で指定される module に対して、 `P1 := P1, P2 := P3, P22 := P3` をしてからその item を得る。

全然実装がわからなかったので、 しばらく full-path でのみとする。
