# Elaboration

`elaboration::Checker` は `resolve::Project` の HIR を受け取り、表面構文を解釈して kernel の判断と宣言登録を呼ぶ。
`sema` は対象の module 群を名前解決した後、この API に渡す。

| 場所 | 担当 |
| --- | --- |
| `api.rs` | HIR の検査、arena から独立した診断・goal・統計 |
| `elaborator/` | HIR の ID と宣言の対応、暗黙引数、block・induction・record の展開 |
| `elaborator/analysis.rs` | 型・名前参照・query 出力の semantic observations |
| `metavariables.rs` | 論理側の穴の由来と kernel solver の呼び出し |
| `elaborator/program_term_elaborator/inference.rs` | Program 側の穴の由来と同じ solver の呼び出し |
| `metavariables/diagnostics.rs` | ゴール・制約・source location の表示 |
| `raw/` | 共通 Arena の source 用 view、module の環境、名前と宣言 ID の変換 |
| `lowering/` | parameter の捕捉、文脈引数の構築、kernel の宣言登録 |
| `kernel_bridge.rs` | 遅延した module の具体化と kernel API への接続 |

項の保存先は kernel と共有する `Expression` の Arena である。
source 用 view は表面構文の論理・Program の解釈に使い、型検査・単一化・簡約・reflection は kernel の共通操作へ委譲する。
module の特殊化と未解決の名前参照は elaboration が処理する。

`_` は出現ごとの穴、番号付きの穴は宣言内で共有する穴として登録する。
`?` は通常の kernel メタ変数に検査用ゴールの情報を付け、解決済みの場合も表示して module の elaboration を失敗させる。
各宣言の終了時には kernel の `finish` を通し、自動生成した穴や残存制約も確認する。

## 宣言と診断

検証済み定義の `DefinitionId` に宣言名と module の情報を対応付ける。
定義の利用は明示的な文脈引数を持つ参照となり、診断では ID と引数から名前を表示する。
匿名の型注釈は期待型の検査に使い、その項の本体を後続の処理へ渡す。

`Diagnostic` と `Goal` は文脈・判断・制約の表示と source location を保持する。
`analysis` の表示済み情報は、`sema` が永続化する結果へ変換する。
各 `Checker::check` は新しい workspace を構築し、同じ HIR を繰り返し検査できる。

`Checker::statistics` はノード数・キャッシュ件数・module の具体化件数を返す。
`Checker::kernel_environment` から kernel の検証済み環境を参照できる。
`REF_TYPE_PROFILE_DECLARATIONS` は宣言ごとの処理時間を表示する。
`REF_TYPE_PROFILE_NAMESPACES` は import ごとの名前空間数・遅延宣言数・ID 対応表の件数を表示する。
同じ import で作る名前空間と遅延宣言は、完成済みの ID 対応表を共有する。
