# 有限生成加群

整数の核・像・部分加群の基底、巡回加群、体上の有限次元部分空間を扱う。
公開 module は [root.ref](src/root.ref)、直接依存は [ref.toml](ref.toml) にある。

| module | 公開する内容 |
| --- | --- |
| `finitely_generated_modules.IntegerDiagonal` / `finitely_generated_modules.IntegerKernel` / `finitely_generated_modules.IntegerBasis` | 対角行列の核、Smith 標準形から得た元の行列の核の自由座標、実行可能な基底行列と逆座標行列、その成分と核の同型の対応、像の階数と自由基底。 |
| `finitely_generated_modules.IntegerIdeals` / `finitely_generated_modules.IntegerSubmodules` | 整数部分加群の主イデアル表示、有限自由整数加群の部分加群の有限生成性、生成行列から得た自由基底と部分加群との同型。 |

`finitely_generated_modules.FieldSubspaces.Over` は、体と有限座標空間の部分加群から線形な引き戻しの存在を証明する。
`Dimension.Of.Retraction` は部分空間への写像と包含との左逆の法則を持つ。
`existence` は次元による帰納法で引き戻しを構成し、`projective` は有限自由加群の直和因子として部分空間の射影性を示す。

検査方法と関連パッケージは [ライブラリ一覧](../README.md) を参照。
