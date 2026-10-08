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
`restore_environment` は圧縮 checkpoint を復元し、raw と kernel の arena を再接続する。
identity と checksum の確認は呼び出し側の `sema` が行う。
再開時には binding・import・source text を現在の project に対応付ける。
永続化と再利用の条件は [sema](../sema/README.md#再利用) を参照。
