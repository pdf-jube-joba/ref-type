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
| `Project::order` | 型検査へ渡す module parameter と各宣言の実行順 |
| `Project::references` | 型推論前に確定した参照先と source location |

ID の有効範囲は一つの `Project` とする。
elaboration は HIR の ID を自身の workspace 内の ID に対応付ける。
`CheckStep::Parameters` は module parameter の検査、`CheckStep::Declaration` は展開済みの各宣言の検査を表す。
実行順は名前解決時に記録し、import 先の宣言の検査を利用箇所より先に置く。
ローカル変数の shadowing と macro の衛生性も束縛 ID に反映する。
macro の定義環境を保持して展開し、module parameter の捕捉は HIR の式として具体化する。
macro の名前は module 本体全体で収集し、子の同名 binding は親を隠す。
template 内の macro 参照は定義元の完成したスコープ、通常の項名は定義位置の項環境に結び付ける。
展開済みの module には検査対象の宣言と query を残し、macro template の参照情報は定義元の source location に保持する。

`#field{x}` は `x` の束縛を解決し、field 名を持つ射影式として保持する。
module の引数式も名前解決し、型検査と typed なインスタンスの構築を elaboration に引き継ぐ。
namespace の構文上のインスタンスは選択された経路にだけ作り、子 module は選択時に親の引数環境を引き継ぐ。
構造値を具体化するときは、フィールド参照と、その namespace を準備する import の対応表を同じ module ID に更新する。
構造の正規化では、射影の基部・関数適用の関数部分・移動した引数チェックの処理済み部分を再走査せず、新しく組み立てた部分を処理する。
Program parameter の反映を含む macro は `Reflect` に元の parameter の ID と引数式を保持し、その parameter の型分類を elaboration で参照する。

構文全体の HIR は `hir`、構造走査は `visit` から利用できる。
名前解決の失敗は module path と source location を持つ `Diagnostic` になる。
名前解決だけの計測には `cargo run --manifest-path benchmarks/Cargo.toml --bin resolve-bench -- libs/geometry/differential_forms` を使う。
`REF_TYPE_PROFILE_COSTS=1` で処理別の時間と呼び出し回数を出力する。

```rust
let ast = syntax::parse::str_parse_modules(
    r"\module M { \definition id(A: \Set, x: A): A := x; }",
).unwrap();
let hir = resolve::resolve(&ast).unwrap();
```

## Package 成果物

`Session::boundary` で package 開始前の所有境界を取り、`export_package` でその後の scope、束縛、宣言、macro と構造情報を取り出す。
保存する scope は明示的な ID を持ち、root の子 module は追加分を保存する。
依存先の macro template は定義 ID で参照し、所有 package の成果物に一度だけ保存する。

読み込み側は依存の対応表を用意し、`reserve_import` で自身の ID を予約してから `import_package` を呼ぶ。
module、束縛、macro、式ごとのローカル束縛、衛生的な名前、宣言 scope を共通の再配置表で更新する。
参照先と scope table の検証が成功した時点で session へ公開する。
source 本文は現在の snapshot から `restore_sources` で接続する。
