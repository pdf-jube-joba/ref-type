## record eta 則
record に対する eta がない。 `s = { fiel1 := 2 #field }` が示せない。

## 命題を条件とする集合値の構成

命題の証明を引数に取り、集合値を返す関数を書きたい。
位相空間の正規性から得られる開集合や Urysohn 関数を、正規性の証明と閉集合の証明を引数とする集合値の関数として構成できると、存在証明を何度も展開せずに利用できる。

> [!note]
> この引用欄は人間のメモです。
> 矛盾しなさそうなのは言われているんですが、こういう Prop -> Set はちょっと許しがたい。

## 中間モジュールの子定義の参照

`Int.Math.Specification` のような中間モジュールを `\module Def;` と `\module Prop;` だけで構成し、親の `Int` から `Math.Specification.Def` の定義を利用したい。
現在は中間モジュールに共通の import を置いて、子定義が親の利用箇所より先に検査されるようにしている。

## 共通定義を持つ親の子モジュールの具体化

`calculus.Real` に実数型や演算の共通定義を置き、その子の `Limit.Def` と `Limit.Prop` から参照したい。
`Limit.Prop` が `\import \parent.Def[] \as Def;` で定義側を具体化する構成では、`Limit.Def` 内の親の `Real` 定義の参照が `Failed to access item at path` で失敗した。
共通定義を独立した `Real` モジュールに置き、兄弟の `Limit` と `Derivative` から import する構成では参照できる。
