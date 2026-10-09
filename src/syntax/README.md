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

## 実行部と仕様の宣言

`\machine` と `\correspondence` は、型を明示する定義宣言として構文解析する。
`std.Program.Machine` は状態・遷移・停止証明を持ち、`std.Program.Correspondence` は実行部・仕様・対応証明を持つ。
これらのレコードの構築と各フィールドの証明は通常の型検査で確認する。

```ref
\machine Loop: Programs.Machine := Programs.Machine {
  State := Implementation.State, Output := Implementation.Output,
  step := Implementation.step, terminates := Implementation.certificate,
};
\correspondence Evaluate: Programs.Correspondence := Programs.Correspondence {
  T := Implementation.T, program := Implementation.program,
  specification := specification, coherence := Implementation.coherence,
};
```
