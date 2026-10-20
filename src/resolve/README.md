# 名前解決と HIR

`resolve::resolve` は AST の名前を束縛 ID に解決し、型推論前の `Project` を返す。

| 表現 | 内容 |
| --- | --- |
| `hir::ModuleId` | module と構文上の namespace インスタンス |
| `hir::BindingId` | 宣言・parameter・局所変数の束縛 |
| `hir::Name` / `LocalAccess` | 表示名と束縛先 / 解決済みの参照 |
| `Project::bindings` / `imports` | 大域束縛の所属と parameter 位置 / import の namespace |
| `Project::order` | parameter と宣言の検査順 |
| `Project::references` | 参照先と source location |

ID は一つの `Project` 内で有効であり、elaboration で検査環境の ID に対応付ける。
`CheckStep::Parameters` と `Declaration` が検査順を表し、参照先を利用箇所より先に置く。
構造走査は `visit`、失敗は module path と source location を持つ `Diagnostic` を使う。

## 展開

macro 名は module 本体全体で収集し、子の同名 binding が親を隠す。
macro 参照は定義元の完成したスコープ、通常の項名は定義位置の項環境、capture は呼出側で解決する。
束縛 ID で衛生性を保ち、展開後には宣言・query と定義元の参照情報を残す。

module 引数も名前解決し、型検査と typed な具体化を elaboration へ渡す。
選択した namespace 経路だけを構築し、子は親の引数環境を引き継ぐ。
構造値の field 参照と準備用 import は同じ module ID に更新する。
Program parameter の反映は `Reflect` に元の ID と引数式を保持する。
`x.field` は field 名を持つ射影として残す。

## Package 成果物

`Session::boundary` で所有境界を取り、`export_package` で追加した scope・束縛・宣言・macro・構造情報を保存する。
依存 macro は定義 ID で参照する。
`reserve_import` で ID を予約し、`import_package` で再配置・参照検証を済ませてから公開する。
本文は `restore_sources` で現在の snapshot に接続する。

計測は [benchmarks](../../benchmarks/README.md)、展開規則は [マクロ](../../doc/book/src/language/macro.md) と [structure](../../doc/book/src/language/structure.md) を参照。

構造の namespace 引数の置換・具体化は、元の構文木の子を処理してから参照先を特殊化する。
特殊化が挿入した namespace 引数を同じ走査で再び処理すると、その引数に含まれる同じ参照を繰り返し展開して停止しなくなる。
`walk_sexp_postorder` は元の子だけを一度ずつ処理し、通常の macro 走査の順序は `walk_sexp_control` に残す。
接束の加法のように、ファイバーの直和を入れ子の構造引数へ渡す場合にも、この順序で有限の具体化を行う。
