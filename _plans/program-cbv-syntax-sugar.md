# Program 適用の型制約と省略記法の解決順を揃える

## 残る問題

[Program の elaborator](../src/front/src/elaborator/program_term_elaborator.rs) は、適用の型頭部を見て直接適用・`force`・`bind` と `force` を選ぶ。補完の判断が `solve_computation` による期待型との照合より先に行われるため、型穴が残る位置によっては判断を早く打ち切る。

例えば、次の定義は現在 `cannot determine whether Program application head is a function; add a type annotation` で失敗する。

```text
\module ProgramApplication(A: \VType) {
  \cdefinition apply(f: \U(_), x: A): \F(A) := f x;
}
```

`f: \U(A ~> \F(A))` と明示した定義は通る。`f: _` では値型のメタ変数に関数 thunk の形を与える処理があるが、`\U` の内部にある計算型のメタ変数には同じ推論が届かない。

## 方針

適用の補完判断と型制約の解決を協調させ、引数と期待型から決まる型穴は補完前に解決する。

- ラムダ・適用の期待型を、値／計算の制約解決と補完判断の両方で利用できるようにする。
- 型頭部が未確定の適用には front 内で保留する状態を持たせ、制約が進んだ時点で判断を再開する。
- 値型全体の穴と `\U` 内部の穴で、同じ関数型を推論できるようにする。
- 直接適用と計算結果への適用の解釈が最後まで決まらない場合は、型注釈が必要な位置を示す。
- 補完とメタ変数の解決を終えてから反映証明を生成し、lowering に渡す。

参照: [syntax.rs](../src/front/src/syntax.rs)、[program_term_elaborator.rs](../src/front/src/elaborator/program_term_elaborator.rs)、[構文仕様](../doc/book/src/coding/syntax.md)。

## 検証

- 上の `\U(_)` の例と明示的な型注釈を持つ例で、推論した型と項が一致する。
- 関数型全体・引数型・結果型・カリー化の途中に穴がある場合を、定義と検査コマンドで確認する。
- 期待型や後続の引数で決まる例と、最後まで曖昧な例を分けて検査する。
- 補完される束縛が局所変数を捕捉せず、Box と証明付き反映の対応を保つ。
- [既存の展開比較](../src/front/src/tests.rs)と[CBV の入力例](../tests/ok/program-cbv-syntax-sugar.ref)を使い、明示的な CBPV 構文との α 同値を確認する。
- 計算を値引数として渡す式や非関数への適用は引き続き拒否し、`cargo test --workspace` を通す。
