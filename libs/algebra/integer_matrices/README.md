# 整数行列

整数行列の演算、Smith 標準形と変換行列を扱う。
公開 module は [root.ref](src/root.ref)、直接依存は [ref.toml](ref.toml) にある。

| module | 公開する内容 |
| --- | --- |
| `integer_matrices.IntegerMatrix` | 有限行列から自然数添字の表現への拡張と往復、整数行列の実行可能な積、行・列の基本変形、転置、恒等行列、領域内の非零成分の探索と型付き行列との対応。 |
| `integer_matrices.Smith` | 辞書式に停止する Smith 標準形の機械、非負の対角成分・整除列・階数の証明、実行可能な変換行列と逆行列、履歴からの可逆性と \(UAV=D\) の証明。 |

検査方法と関連パッケージは [ライブラリ一覧](../../README.md) を参照。
