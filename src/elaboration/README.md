# Elaboration

`Checker` は `resolve::Project` を共有 `Expression` arena の kernel 項へ変換し、型検査と宣言登録を呼ぶ。

| 場所 | 担当 |
| --- | --- |
| [api.rs](src/api.rs) | HIR の検査、診断・goal・統計、checkpoint |
| [elaborator](src/elaborator) | 暗黙引数、block・induction・record・module の具体化 |
| [analysis.rs](src/elaborator/analysis.rs) | 表示型・名前参照・query 出力 |
| [metavariables.rs](src/metavariables.rs) | 穴の由来と solver 呼び出し |
| [raw](src/raw) | source view、module 環境、宣言 ID |
| [lowering](src/lowering) | parameter 捕捉、文脈引数、kernel への登録 |
| [kernel_bridge.rs](src/kernel_bridge.rs) | 遅延した具体化と kernel API の接続 |

型検査・単一化・簡約・reflection・束縛操作は kernel に委譲し、宣言確定時の `finish` で全メタ変数と保留制約を確認する。
module parameter は名前付き ID で保持し、kernel へ渡す際に参照する parameter を依存順に捕捉する。

具体化は元の module と引数列を索引にし、変更のない宣言と同値な引数列を共有する。
比較キャッシュは上限を持ち、探索中の変換失敗は環境が進むと再試行する。
引数列は共有配列、本文は遅延生成する。
置換 map の合成は DAG として共有し、探索中の同じ map とキーの組合せは失敗も含めて一度だけ調べる。

## API と診断

`Checker::check` は新しい検査環境で検査する。
`analysis`・`statistics`・`kernel_environment` が観測情報・統計・検証済み環境を返す。
診断は文脈・判断・制約・source location を持ち、[diagnostics.rs](src/diagnostics.rs) で表示量を制限する。

## 環境 checkpoint

`check_range` は検査順の区間を処理し、`check_range_with_progress` は各ステップの位置と時間も通知する。
`restore_environment` は圧縮 checkpoint から raw と kernel の arena を再接続する。
[declaration_checkpoint.rs](src/raw/declaration_checkpoint.rs) は引数列と置換を共有表として保存する。
照合と永続化は [sema](../sema/README.md#再利用) が担当する。

## package 成果物

`PackageChecker::artifact_boundary` で所有境界を取り、`export_artifact_for_input` で resolver と検査環境を別 object にする。
`ArtifactCatalog` は入力キー・保存用 identity と実行時 ID を対応付ける。
raw/kernel は共有 DAG とし、依存の式・macro・置換 map は所有成果物への参照にする。
依存 map の immutable snapshot を保ち、部分成果物の統合で map が成長しても既存の参照を維持する。

`import_artifact` は ID 予約・再配置・検証後に環境と catalog を公開する。
`import_artifact_owned` は checker と catalog を消費し、失敗時は両方を破棄する。
`append_selected_with_checkpoints` は選択 module と親の未検査ステップを処理し、同じ入力の部分成果物を任意順に統合する。
`export_resume_for_input` / `import_resume` は検査位置を復元し、`import_resume_owned` は消費型で処理する。
`append_selected_with_artifact_checkpoints` は借用した環境から package の差分を直接保存する。
