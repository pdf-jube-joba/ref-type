# 名前解決と HIR

`resolve::resolve` は読み込み済みの AST を受け取り、名前を束縛先の ID に解決した、型推論前の `Project` を返す。
依存する処理は `syntax` の構文と source 情報である。

| 表現 | 内容 |
| --- | --- |
| `hir::ModuleId` | この HIR 内の module と構文上の namespace インスタンス |
| `hir::BindingId` | 宣言、module parameter、ローカル変数などの束縛 |
| `hir::Name` | 表示用の名前と、その名前が束縛を指す場合の ID |
| `hir::LocalAccess` | ID で確定したローカル参照または namespace 内の参照 |
| `Project::bindings` | 大域的な束縛の所属 module と parameter の位置 |
| `Project::imports` | import による namespace の対応付け |
| `Project::order` | 型検査へ渡す module 単位の依存順 |
| `Project::references` | 型推論前に確定した参照先と source location |

ID の有効範囲は一つの `Project` とする。
elaboration は HIR の ID を自身の workspace 内の ID に対応付ける。
ローカル変数の shadowing と macro の衛生性も束縛 ID に反映する。
macro の定義環境を保持して展開し、module parameter の捕捉は HIR の式として具体化する。
展開済みの module には検査対象の宣言と query を残し、macro template の参照情報は定義元の source location に保持する。

`#field{x}` は `x` の束縛を解決し、field 名を持つ射影式として保持する。
module の引数式も名前解決し、型検査と typed なインスタンスの構築を elaboration に引き継ぐ。
Program parameter の反映を含む macro は `Reflect` に元の parameter の ID と引数式を保持し、その parameter の型分類を elaboration で参照する。

構文全体の HIR は `hir`、構造走査は `visit` から利用できる。
名前解決の失敗は module path と source location を持つ `Diagnostic` になる。

```rust
let ast = syntax::parse::str_parse_modules(
    r"\module M { \definition id(A: \Set, x: A): A := x; }",
).unwrap();
let hir = resolve::resolve(&ast).unwrap();
```
