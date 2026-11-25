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
検査セッションは resolver・raw/kernel の環境と完了台帳を共有し、後続の package 要求でも完了した検査ステップを再利用する。
native の保存経路は、入力・検査済み範囲・resolver と raw の索引・式グラフのページ参照を checkpoint に結び付ける。
復元後は内部 ID を維持し、必要な式ページを読み込んで検査を継続する。
処理系・設定・ソース・依存入力・強制検査範囲を照合して再利用を判定する。
保存形式と再利用の詳細は [sema](../../../../src/sema/README.md#再利用) を参照。
実行・診断・計測は [利用方法](../../../../src/USAGE.md) を参照。
