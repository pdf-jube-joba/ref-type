# メモ
## 項の記述について
### application
$t_1 t_2$ だと空白が当然入らない。
かといって、 $t_1 \: t_2$ のように手書きで `\:` を入れるのもよくない。
なので、項の適用は $t_1 @ t_2$ のように書きたい。
### textop
いい感じに空白が入ってほしいので、（用途としてあっているかはさておき） `\mathop{\text{#1}}` を使う。

## 証明木について
証明木を書くのが難しい。
1. `dfrac` を使う
  - 箇条書きと相性が悪い
  - $\dfrac{1}{2}$
  - $\dfrac{3}{4}$
2. make で自動的にSVG差し替え
  - 明らかにだめ
3. markdown の html タグと css で頑張る
  - 辛そう

メンテナンスが楽なものがないので、証明木を書かない方針で行く。

## 入れ子
- abc
    - inner
- def

1. abc
    - inner
2. def
