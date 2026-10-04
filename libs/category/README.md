# 圏論

`category` は対象の集合と射の集合族を持つ圏を扱う。
恒等射と合成のデータ、圏の法則、関手の写像とその法則を分けて保持する。
自然変換は自然性を満たす成分の関数として表し、変換の等式には関数の外延性を使う。

| モジュール | 内容 |
| --- | --- |
| `Category` | 圏、反対圏、射の合同則、同型と消去則 |
| `Constructions` | 終圏、終圏への関手、集合族上の関数の圏 |
| `Functor` | 関手、恒等関手、合成、反対関手、定値関手 |
| `Natural` | 自然変換、垂直合成、左右の whiskering、自然同型 |
| `FunctorCategory` | 関手圏と前合成による制限関手 |
| `Universal` | 始対象、終対象、普遍射と同型による一意性 |
| `Limits` | 錐、余錐、極限、余極限と同型による一意性 |
| `Adjunction` | Hom の自然な全単射による随伴、単位、余単位、三角恒等式、単位による普遍射 |
| `SetValued` | 集合値関手、表現可能関手、米田の全単射 |
| `Kan` | 左右の Kan 拡張、恒等関手に沿う拡張、自然同型による一意性 |

## Kan 拡張

`Kan.Along` は関手 \(K:A\to B\) と \(F:A\to C\) を受け取る。
`Left` は関手 \(L:B\to C\)、自然変換 \(\eta:F\Rightarrow LK\)、任意の \(\alpha:F\Rightarrow GK\) を一意に分解する自然変換 \(L\Rightarrow G\) を束ねる。
`Right` は自然変換 \(RK\Rightarrow F\) を使う双対の普遍性を束ねる。
拡張の関手は `extension`、比較する関手への自然変換は `factor` から取り出す。
自然性と因子化の等式は、各対象と各射について量化している。
`Kan.Along.Prop` の `leftUnique` と `rightUnique` は、同じ \(K,F\) に対する二つの拡張の間の自然同型を構成する。

```text
\import category.Category[] \as Cat;
\import category.Functor[] \as Functors;

\module Example(A, C: Cat.Category, F: Functors.Functor A C) {
  \definition identity: Functors.Functor A A := Functors.identity A;
  \import category.Kan[].Along[A := A, B := A, C := C,
    K := identity, F := F] \as Extension;
  \import category.Kan[].Identity[A := A, C := C, F := F] \as Identity;
  \definition left: Extension.Left := Identity.left;
  \definition right: Extension.Right := Identity.right;
}
```

集合値関手は `SetValued.On` の集合族として扱い、反変の場合は反対圏を使う。
関数の圏 `Constructions.functions` は、集合で添字付けられた集合族を対象として使う。

## 検査

```sh
cargo run --quiet --bin cli -- libs/category
cargo run --quiet --bin cli -- tests/projects/category
```

検査は一つずつ実行する。
大きな失敗の調査には `REF_TYPE_COMPACT_DIAGNOSTICS=1` を設定し、エラー本体とソース位置を確認できる。
