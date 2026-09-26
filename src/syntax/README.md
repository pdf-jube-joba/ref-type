# Source syntax

`syntax` は字句解析・構文解析と AST を担当する。
`SourceFile`、`SourceSpan`、`SourceLocation` により、構文と元の source を対応付ける。

`parse_root` は root ファイルを解析し、`parse_items` は外部 module の宣言列を解析する。
parse error はメッセージと span を持ち、呼び出し側で表示できる。
`Module` は宣言列と各宣言の span を保持する。
`LocalAccess` と associated access は名前参照の span を保持する。

AST は名前の文字列、束縛、macro token、proof block、型に応じて分類する Program の構文を保持する。
`resolve` が AST を受け取り、束縛 ID と source span を持つ HIR へ変換する。
外部 module と package の読み込み、source snapshot は `project` が担当する。
