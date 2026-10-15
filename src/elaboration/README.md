# Elaboration

`elaboration::Checker` は `resolve::Project` の HIR を受け取り、表面構文を kernel の項へ変換して検査・宣言登録を呼ぶ。
項は kernel と共有する `Expression` arena に保持する。

| 場所 | 担当 |
| --- | --- |
| [api.rs](src/api.rs) | HIR の検査、診断・goal・統計、環境 checkpoint |
| [elaborator/](src/elaborator) | 束縛 ID、暗黙引数、block・induction・record・module の具体化 |
| [analysis.rs](src/elaborator/analysis.rs) | 表示用の型・名前参照・query 出力 |
| [metavariables.rs](src/metavariables.rs) | 穴の由来と kernel solver の呼び出し |
| [raw/](src/raw) | source 用 view、module 環境、名前と宣言 ID の対応 |
| [lowering/](src/lowering) | parameter の捕捉、文脈引数、kernel の宣言登録 |
| [kernel_bridge.rs](src/kernel_bridge.rs) | 遅延した具体化と kernel API への接続 |
| [kernel_bridge/terms.rs](src/kernel_bridge/terms.rs) | source 用 handle から kernel の束縛操作・簡約・評価を呼ぶ adapter |

型検査・単一化・簡約・reflection は kernel に委譲する。
項の子の順序・binder の深さ・自由な束縛変数の情報も kernel の共有 API を使う。
`raw/traversal.rs` は source 用 view の分類を行い、`raw/remapping.rs` は module parameter の置換と source の宣言 ID の付け替えを行う。
宣言の確定時に `finish` で全メタ変数と保留制約の解決を確認する。
namespace 引数の置換は、式が参照する宣言と module parameter を事前に調べ、その対応先が同じ間は結果を再利用する。
インスタンス化では引数と宣言の依存関係から変更の有無を先に調べ、変更されない宣言は仮 ID の予約前に元の ID を共有する。
選択経路に含まれる module もこの判定を使い、名前空間のメタデータだけを作る。
具体化の候補探索は、元の module と引数列ごとに位置と未確定の候補を保持する。
確定した不一致を候補から除き、等しいと確認した引数列の同値類は全宣言の ID 検索で共有する。
宣言の引数列は共通の配列を参照し、遅延宣言の本文用メモリは具体化時に確保する。
個々の項・引数列の比較キャッシュは上限を設け、再利用されたエントリを優先して残す。
インスタンスの候補探索中に失敗した kernel 項への変換は、その探索の間だけ記録し、宣言の具体化・kernel への登録・変換済み項の追加が進めば再試行する。

module parameter は名前付きの ID として保持し、局所変数の de Bruijn 文脈には追加しない。
kernel へ定義を渡すときに、実際に参照する parameter を依存順で捕捉する。
`\take` の結果型の独立性は、取り除く変数を含む部分だけを簡約して確認する。

## API と診断

`Checker::check` は新しい workspace で検査する。
`analysis` は semantic observations、`statistics` はノード数や具体化件数、`kernel_environment` は検証済み環境を返す。
診断は局所文脈・判断・制約・source location を保持し、共有 arena の大きな式には参照表記を使う。
表示量の上限は [diagnostics.rs](src/diagnostics.rs) に集約する。
CLI の診断モードと計測環境変数は [利用方法](../USAGE.md#診断と計測) を参照。

## 環境 checkpoint

`check_range` は検査順の指定区間を処理し、選んだ位置で環境を直列化する。
`check_range_with_progress` は各検査ステップの位置と所要時間も callback に通知する。
checkpoint は batch の検証成功後に公開し、失敗前の prefix は問い合わせ内の復旧にも使う。
直列化したデータを32 KiBずつ圧縮器へ渡し、環境全体の未圧縮バッファを作るための一時メモリを省く。
具体化の引数列と置換は、[declaration_checkpoint.rs](src/raw/declaration_checkpoint.rs) が共有配列の表と参照として保存する。
`restore_environment` は圧縮 checkpoint を復元し、raw と kernel の arena を再接続する。
identity と checksum の確認は呼び出し側の `sema` が行う。
再開時には binding・import・source text を現在の project に対応付ける。
永続化と再利用の条件は [sema](../sema/README.md#再利用) を参照。

## package 成果物

`PackageChecker::artifact_boundary` で依存の読み込み後の境界を取り、`export_artifact_for_input` で現在の package の resolver と検査環境を別々の object にする。
`ArtifactCatalog` は入力キーと package 内の identity を実行時 ID に対応付け、依存の読み込み順や部分検査の範囲をまたいで同じ宣言を共有する。
式の共有によって一つの実行時 ID に複数の所有元が対応する場合は、現在の依存閉包から参照先を選ぶ。
raw と kernel の式は一つの DAG として保存し、依存の式・macro 定義・置換 map は所有成果物への参照として保持する。
置換 map の identity は生成した namespace または合成元から決め、検査範囲に伴う参照元の増加から独立させる。
依存 map への参照は公開時の immutable snapshot を指し、部分成果物の統合で現在の map が成長しても、保存済みの利用側の参照先を維持する。
自身の map と symbol は保存対象から到達するものだけを取り出す。
`import_artifact` は resolver・raw・kernel の ID を予約し、検証と再配置が成功してから環境と catalog をまとめて更新する。
読み込みに失敗した環境を破棄できる呼び出し側は、checker と catalog を消費する `import_artifact_owned` を使い、依存閉包全体の複製を省く。
成功時には更新後の checker と catalog を返し、失敗時には両方を破棄する。

`append_selected_with_checkpoints` は package 全体を名前解決し、指定したソース module とその親の未検査ステップを処理する。
同じ入力から作った部分成果物は任意の順序で読み込め、検査済みステップの集合を統合する。
統合した成果物は自身の部分成果物を読む前の境界から export する。
`export_resume_for_input` と `import_resume` は同じ対応表を使い、途中の検査位置と完了したステップを復元する。
`import_resume_owned` は再開用の消費型 API である。
`append_selected_with_artifact_checkpoints` は検査中の環境を借用して package の差分を直接保存し、依存閉包全体の直列化と復元を省く。
