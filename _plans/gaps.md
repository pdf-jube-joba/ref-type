## record eta 則
record に対する eta がない。 `s = { fiel1 := 2 #field }` が示せない。

## 中間モジュールの子定義の参照

`Int.Math.Specification` のような中間モジュールを `\module Def;` と `\module Prop;` だけで構成し、親の `Int` から `Math.Specification.Def` の定義を利用したい。
現在は中間モジュールに共通の import を置いて、子定義が親の利用箇所より先に検査されるようにしている。
