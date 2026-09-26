# Source syntax

`front-syntax` は字句解析・構文解析・module と package の読み込みを担当する。
`SourceFile`、`SourceSpan`、`SourceLocation` により、構文と元の source を対応付ける。

`parse_root` は root ファイルを解析し、`parse_items` は外部 module の宣言列を解析する。
parse error はメッセージと span を持ち、呼び出し側で表示できる。
`Module` は宣言列と各宣言の span を保持する。
`LocalAccess` と associated access は名前参照の span を保持する。

`SourceProvider` により module 読み込み時の source 取得と parse 処理を差し替えられる。
`DiskSource` はファイルを直接読み、`front` の provider は immutable な snapshot と parse cache を使う。
package loader は path dependency を訪問し、package 名による import を root からの module path に結合する。

構文には束縛・macro token・proof block・型に応じて分類する Program の構文を保持する。
macro の定義環境を固定する scope ID と captured term は展開時に付加され、elaboration が解釈する。
