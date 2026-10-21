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
依存関係に制約されない parameter の順序は package・ソース位置から決め、成果物の復元順に依存させない。

具体化は元の module と引数列を索引にし、変更のない宣言と同値と確認できた引数列を共有する。
新しい具体化の作成時に過去の全引数列を比較する探索を省き、必要な変換可能性の判定は kernel に委譲する。
比較キャッシュは上限を持ち、探索中の変換失敗は環境が進むと再試行する。
名前空間は原形の不変なメンバー索引と共有引数を持つ view とし、検索したメンバーだけを具体化する。
宣言 ID の予約には疎な表を使い、未参照メンバーの宣言セルは確保しない。
view の同一性には原形の世代、引数、局所文脈、Program 文脈を含め、nominal identity を本文の具体化から独立させる。
引数列は共有配列、本文は遅延生成する。
元の module の引数列も共有し、parameter の追加と成果物の統合時にその索引を作り直す。
局所文脈を持たない論理的な定義は元の本文を一度 kernel に登録し、特殊化した参照から module 引数を明示して呼び出す。
名前付き import、局所変数を持つ import、Program の具体化は、それぞれの宣言と検査文脈の対応を view に保持する。
参照先の本文と引数の依存先は kernel 環境を借用する前に具体化する。
置換 map の合成は DAG として共有し、探索中の同じ map とキーの組合せは失敗も含めて一度だけ調べる。
具体化を確定するときも局所表だけを圧縮し、親の置換表の共有を維持する。

## API と診断

`Checker::check` は新しい検査環境で検査する。
`analysis`・`statistics`・`kernel_environment` が観測情報・統計・検証済み環境を返す。
診断は文脈・判断・制約・source location を持ち、[diagnostics.rs](src/diagnostics.rs) で表示量を制限する。

## 環境 checkpoint

`check_range` は検査順の区間を処理し、`check_range_with_progress` は各ステップの位置と時間も通知する。
`restore_environment` は圧縮 checkpoint から raw と kernel の arena を再接続する。
[declaration_checkpoint.rs](src/raw/declaration_checkpoint.rs) は引数列と置換を共有表として保存し、宣言の行をストリームで符号化する。
[module_checkpoint.rs](src/raw/module_checkpoint.rs) は namespace の不変な名前表とラベルの共有を復元する。
`PackageChecker::checkpoint` は resolver・検査環境・完了したステップを保持し、`restore` は現在のソースと名前参照を再接続する。
native のセッション保存では式ページと分割した索引を不変 object に保存し、本文を必要なページから読み込む。
照合と永続化は [sema](../sema/README.md#再利用) が担当する。

## package 成果物

`PackageChecker::artifact_boundary` で所有境界を取り、`export_artifact_for_input` で resolver と検査環境を別 object にする。
`ArtifactCatalog` は入力キー・保存用 identity と実行時 ID を対応付ける。
identity の種類と所有成果物を共有表にまとめ、各対応を整数の索引で保持する。
raw/kernel は共有 DAG とし、依存の式・macro・置換 map は所有成果物への参照にする。
依存 map の immutable snapshot を保ち、部分成果物の統合で map が成長しても既存の参照を維持する。
名前空間の置換には内容の identity を与え、生成された内部 module は保存する成果物ごとに識別する。
frontend atom のメタデータは生成時期にかかわらず、保存する式からの到達可能性で選ぶ。
局所変数を含む import は、呼び出し元と論理・Program の検査文脈をキーに特殊化宣言と namespace を共有する。

`import_artifact` は ID 予約・再配置・検証後に環境と catalog を公開する。
`import_artifact_owned` は checker と catalog を消費し、失敗時は両方を破棄する。
`append_selected_with_checkpoints` は選択 module と親の未検査ステップを処理する。
`export_resume_for_input` / `import_resume` は検査位置を復元し、`import_resume_owned` は消費型で処理する。
`append_selected_with_artifact_checkpoints` は借用した環境から package の差分を直接保存する。
大きい環境の保存前には再計算できる検査キャッシュを解放し、符号化に必要な一時領域を確保する。
