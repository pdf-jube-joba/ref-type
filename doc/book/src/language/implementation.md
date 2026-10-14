# 言語処理系

CLI と LSP は `sema::Database` を通じて source snapshot を検査する。

| crate | 担当 |
| --- | --- |
| [project](../../../../src/project/README.md) | source snapshot、package と外部 module の読み込み |
| [syntax](../../../../src/syntax/README.md) | 字句・構文解析、AST と source span |
| [resolve](../../../../src/resolve/README.md) | 名前解決、macro 展開、structure の展開、型推論前の HIR |
| [elaboration](../../../../src/elaboration/README.md) | 暗黙引数、表面構文の解釈、module の具体化、診断 |
| [kernel](../../../../src/kernel/README.md) | 型検査、単一化、代入、簡約、reflection、宣言登録 |
| [artifact](../../../../src/artifact/README.md) | package 成果物の保存用 identity、決定的な直列化、実行時 ID への対応付け |
| [sema](../../../../src/sema/README.md) | semantic query、依存関係、結果と環境のキャッシュ |

sort・型・項・証明は kernel と elaboration が共有する `Expression` arena に置く。
定義は文脈・型・本体を保持し、`DefinitionId` と文脈引数で参照する。
宣言確定時の `finish` が未解決メタ変数と残存制約を確認する。
検査済み package は自身の定義と依存成果物への参照を保存し、処理系・設定・ソース・依存入力と検査範囲が一致する場合に再利用する。
後続の検査では保存用 ID を読み込み先の ID に対応付け、必要な依存成果物を環境へ登録する。
実行・診断・計測は [利用方法](../../../../src/USAGE.md) を参照。
