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
`--diagnostics compact` または `REF_TYPE_COMPACT_DIAGNOSTICS=1` は制約の探索と一覧の生成を省略する。
`--diagnostics detailed` は詳細な制約表示を選び、CLI の指定は環境変数より優先する。
エラー本体・ゴール・source location を先に保持し、選ばれたエラーの詳細は API の診断への変換時に生成する。
制約の状態は検査と solver が記録し、診断では保存済みの状態を表示する。
制約の探索は 2,048 回・式ノード 32,768 個、表示は一覧ごとに 32 件、ゴールは 64 件までとする。
式は深さ 48・512 ノード・4 KiB、文脈は 128 項目・8 KiB、エラーメッセージは 64 KiB までとし、省略量を表示する。
ソースの抜粋はエラー位置を含む 240 文字までとし、元の行番号と列番号を保つ。
大きい共有式は `@expr0` などの参照を使って表示する。
大きな証明の失敗を調べるときも、エラー本体と source location を表示できる。
簡潔な診断を選んだ CLI のパッケージ検査では最初のエラーで停止し、独立したモジュールの後続検査も省略する。
このモードで構文エラーがある場合は、型検査を始める前にそのエラーを返す。
`REF_TYPE_PROFILE_DIAGNOSTICS=1` は診断の保存・ゴール生成・詳細生成・表示の時間と、プロセスの RSS および開始時との差を表示する。
`REF_TYPE_PROFILE_DECLARATIONS` の宣言時間は診断生成時間を除く。
`REF_TYPE_PROFILE_PHASES=1` は名前解決・検査・環境の保存と復元・kernel 登録などの経過時間と RSS を表示する。
kernel 登録は定義名ごとにも計測し、表面構文の宣言検査とは別に確認できる。
`REF_TYPE_PROFILE_MODULES=1` は読込・引数検査・具体化・失敗後の復旧を区別し、参照元・引数・環境の版・キャッシュの命中を記録する。
`REF_TYPE_PROFILE_NAMESPACES` は import ごとの名前空間数・遅延宣言数・ID 対応表の件数を表示する。
同じ import で作る名前空間と遅延宣言は、完成済みの ID 対応表を共有する。

## 検査環境の checkpoint

`Checker::check_range` は HIR の検査順に沿って処理を進め、指定した区切りで環境を直列化する。
保存した checkpoint は、その batch の検証成功後に公開する。
失敗前の検査済み prefix は問い合わせ内で保持し、独立したスコープの復旧に再利用する。
復旧時も HIR の配置と環境キーを保ち、失敗したスコープとその依存元を後続検査から除く。
問い合わせ内では名前解決に成功した HIR と checkpoint の計画を共有する。
`QueryStats::recovery_environment_hits` は復旧用の環境再利用回数を表す。
`Checker::restore_environment` は identity と checksum を確認したローカルの checkpoint を読み、raw と kernel が共有する arena を復元する。
名前解決で得た binding・import と source text は、再開時の project から更新する。
直列化と展開にはサイズ上限を設け、具体化の対応表は環境内の ID で共有する。
