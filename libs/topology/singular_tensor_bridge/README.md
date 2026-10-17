# 整数次数と非負次数のテンソル鎖複体の比較

`Integer.Factor[C].With[negative]` は、負次数が自明な整数鎖複体 `C` と、その非負次数への制限の零拡張との鎖同型 `isomorphism` および鎖ホモトピー同値 `equivalence` を与える。
非負次数では元の元をそのまま使い、負次数では零に送る。
`negative` は各負次数のすべての元が零であるという条件で、比較同型そのものを仮定しない。

`Integer.Indices` は、自然数の次数和で指定する添字と、対応する整数の次数和で指定する添字を結び付ける。
`Integer.Tensor[C, D].With[leftNegative, rightNegative].Positive[n].isomorphism` は、次数 `n` の整数添字テンソル直和と、非負次数に制限した二重複体の全複体の項との加群同型である。
両因子が非負次数にある成分は同じテンソル項を対応させ、負次数の因子を持つ成分はその自明性から零となる。
`Negative[n].zero` は、負次数の全複体の項が自明であることを示す。

`Integer.Tensor[C, D].With[leftNegative, rightNegative].isomorphism` は、この次数ごとの同型を境界作用素と両立させ、整数添字テンソル全複体から、非負次数テンソル全複体の零拡張への鎖同型を与える。
`equivalence` は同じ前進写像を持つ鎖ホモトピー同値である。
境界の水平項・垂直項と符号を直和の各生成元で比較し、次数零を越える境界は負次数消滅から零となることを用いる。
`Integer.Lift[C, D].With[e]` は、非負鎖同型 `e` を両側の零拡張の鎖同型へ移す。

これらの構成では有限生成性や自由性を仮定しない。
直和の普遍性とテンソル積の普遍性を用いて、実際の線形写像と逆関係を構成する。

```sh
cargo run -p cli -- libs/topology/singular_tensor_bridge \
  --module singular_tensor_bridge.Integer.Factor.With --module-only
cargo run -p cli -- libs/topology/singular_tensor_bridge \
  --module singular_tensor_bridge.Integer.Tensor.With --module-only
```
