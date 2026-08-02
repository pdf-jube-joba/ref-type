# このリポジトリについて
proof checker を作る。 **コンパイルすることは忘れて** 単に形式的な記述をチェックするための言語を作る。

# 構成
- doc/ はドキュメント置き場
    - doc/book/ に考えている体系についての文章を書く
- formalization/ は他の定理証明支援系で現在の体系の性質を証明する
- src/ は実装
    - src/core/ はライブラリとしてのコア部分
    - src/terminal/ は CUI 用のプログラム
    - src/USAGE.md は CUI の使い方

# メモ
Cauchy から Dedekint の方向は
```
 ((n : Nat) -> ∃ q : Rat, P n q)
  ->
  ∃ a : Nat -> Rat, (n : Nat) -> P n (a n)
```
がほしいらしい。

Choice か Hilbert epsilon みたいなものでどうにかなる？
