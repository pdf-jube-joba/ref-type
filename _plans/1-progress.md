# Semantic architecture の実装記録

## 実装した経路

[sema](../src/sema/src/lib.rs) が source snapshot、構文回復、outline、宣言の検査状態、診断、参照、goal、編集提案を提供する。
CLI と module loader は、この入口を利用する。
Rust の実装は kernel、syntax、hir、elab、sema、cli の六つの crate に分割した。
`AnalysisHost::refresh_disk` が filesystem を入力へ取り込み、`AnalysisSnapshot` は取り込まれた入力を読む。
未保存 buffer、file の追加・削除・rename、外部 module の探索結果は snapshot に含まれる。
通常の名前付き宣言には `ItemId` を対応付け、`ItemVersion` は現在は到達可能な workspace 全体の内容を保守的に含める。
対応付けは snapshot 作成時に行い、対応表には現在の入力にある名前を保持する。
分岐した source database の更新にも異なる revision を割り当てる。

宣言と module parameter の検査境界で kernel への登録を行い、[raw arena](../src/elab/src/exp.rs) の作業ノードを回収する。
保存するノードは公開された root の到達可能部分であり、handle の index は同じ環境内で再利用されない。
`CheckedArtifact` は raw と kernel の所有環境を共有し、最後の成果物と snapshot の破棄で環境を解放する。
kernel の型付き handle は arena identity を持ち、別環境の項を検査・比較するときに所有元を照合する。
`MetaVarId` の定義は elab crate に置く。

失敗した検査環境を破棄し、失敗した宣言を unavailable として入力から再実行することで、独立した宣言の検査を続ける。
unavailable な名前は外側の同名宣言を隠し、その読み取りを `Blocked` の依存先として記録する。
この回復経路は失敗数に応じて成功済みの prefix を再検査する。

`GoalSnapshot` は表示用の context、target、制約、複数 occurrence を所有する。
`give` と `refine` は owner を再検査し、revision 付きの編集提案を返す。
macro の capture に渡した hole は編集可能な source occurrence を保持し、template 内の hole は生成元を区別して編集可否を返す。
未完成の宣言で解決済みの参照も、所有環境の破棄前に表示用の情報へ変換する。
取消と資源上限の到達は型エラーと区別し、中断した問い合わせの結果は cache に公開されない。

[stdio adapter](../src/cli/src/protocol.rs) は LSP の diagnostics、document symbols、definition、hover と、MCP の `check`、`goals`、`set_buffer`、`give`、`refine` を提供する。
LSP の位置は UTF-16、semantic API の位置は UTF-8 byte range である。

```sh
target/release/cli libs/real --lsp
target/release/cli libs/real --mcp
```

protocol の参照仕様は [LSP 3.17](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/) と [MCP 2025-06-18 stdio](https://modelcontextprotocol.io/specification/2025-06-18/basic/transports) である。

## Phase ごとの状態

| Phase | 実装と残る作業 |
| --- | --- |
| 0 | 変更前の test・library baseline、raw root の列挙、総割当数と宣言からの到達可能数の計測を追加した。 |
| 1 | VFS、版付き location、構造化診断、回復 AST、式・identifier・hole の range、AST の式 ID と source map、outline の ID 対応、共通 CLI 入口を実装した。 |
| 2 | 作業領域の回収、公開 root の保存、宣言境界の kernel check、goal snapshot、失敗時の再実行を実装した。保存領域の宣言ごとの独立所有と、再実行を置き換える局所 transaction が残る。 |
| 3 | 実際に選択された通常参照、論理 binder、record field の occurrence を記録する。AST と proof HIR を分離し、scope/capture の ID、macro 環境、Resolver interface を独立させた。展開ごとの呼出元・定義元・capture 元と親展開を source map で追跡する。通常参照の事前解決が残る。 |
| 4 | 完了。kernel-local な opaque ID、外側 context の level、開いた template、reflection と閉性検査、取消時の登録巻き戻し、所有環境を跨ぐ再配置・再検査を実装した。 |
| 5 | 同一入力 snapshot の結果を再利用し、本体・挿入・削除・名前・shadowing・import・構文回復・取消の編集列を cold result と比較する。変更後は全体を再検査するため、宣言単位の依存追跡・再利用が残る。 |
| 6 | goal の表示、`give`、`refine`、macro capture の編集可否、Program の局所参照、LSP・MCP の初期 adapter を実装した。診断・参照・goal は展開履歴と生成元を保持する。`apply`、case split、normalize、workspace index の完成が残る。 |
| 7 | path 依存の PackageGraph、manifest 入力、PackageId、package 間の import と、std・real・topology のライブラリ分割を実装した。各 package の宣言を dependency 経由で参照できる。 |
| 8 | ID 再配置と kernel 再検査の経路を実装した。永続形式と容量・検証方針を 1.md に確定し、宣言単位の serialization と disk store を残す。 |

## Baseline

変更前 revision は `0b0323f31916a7b05fdc71b1e6bd4f8e333a3e1f`、入力は `lib/root.ref` である。
`git ls-files lib` の各 path と内容をそれぞれ NUL で区切って連結した SHA-256 は `05ca1566f07f881637c9c7c374eb5e0b166330769b445262e31d454ab7fee550` である。
環境は x86_64 WSL2、Linux `6.18.33.2-microsoft-standard-WSL2`、`rustc 1.98.1 (48a229cea 2026-09-01)` である。
release build の時間を除き、`RUST_LOG` を解除して同じ入力を順に 3 回実行した。

```sh
cargo test --workspace --locked --offline
cargo build --release --locked --offline
env -u RUST_LOG /usr/bin/time -f 'elapsed=%e user=%U sys=%S maxrss_kb=%M' target/release/cli lib/root.ref --stats
```

| 実行 | elapsed 秒 | user 秒 | sys 秒 | max RSS KiB |
| --- | ---: | ---: | ---: | ---: |
| 変更前 1 | 8.79 | 8.26 | 0.34 | 734952 |
| 変更前 2 | 8.39 | 8.63 | 0.27 | 735472 |
| 変更前 3 | 9.77 | 9.23 | 0.34 | 735252 |
| 変更後 1 | 11.13 | 11.74 | 0.13 | 308988 |
| 変更後 2 | 12.48 | 11.91 | 0.09 | 308940 |
| 変更後 3 | 11.32 | 11.96 | 0.12 | 308888 |

変更前の raw 論理ノード数は 5,518,731、raw inference cache は 1,098,237、raw context bindings は 143,878、raw weak heads は 1,467,070 だった。
kernel の宣言から到達可能なノード数は 69,955 だった。
変更前の workspace test は CLI integration 13、front 142、kernel 34、doctest 3 件が通った。
変更後の中央値は elapsed 11.32 秒、peak RSS 308940 KiB であり、変更前に対して時間は約 29% 増え、peak RSS は約 58% 減った。
変更後の raw 論理ノードは総割当 7,947,353、保持 68,876 であり、kernel の宣言からの到達可能数は 69,955 で一致した。
成果物の所有環境と参照情報を保持する CLI の共通経路を含めた測定である。
変更後の workspace test は CLI protocol 3、CLI integration 13、front 166、kernel 35、doctest 3 件が通り、`cargo clippy --workspace --all-targets --locked --offline -- -D warnings` も通った。

既存の意味を確認する主要なテストは次のとおりである。

| 対象 | テスト |
| --- | --- |
| module の処理順・エラー位置 | `dependency_ordered_module_errors_include_source_location` |
| macro の宣言順 | `macro_templates_cannot_see_later_macro_declarations` |
| macro hygiene | `macro_binders_do_not_capture_call_site_expressions`、`imported_macro_resolves_free_names_at_its_definition_site` |
| 特殊化した macro | `imported_macro_uses_the_materialized_module_arguments`、`instantiated_macro_keeps_macros_used_by_its_definition_module` |
| instance の同一性 | [substitution-identity.ref](../tests/ok/modules/substitution-identity.ref) |
| Program reflection | `program_case_reflects_value_let_in_parameterized_branches`、`program_proofs_follow_local_binders_and_module_instantiation` |
| goal の分類・共有・context | `parses_implicit_and_goal_metavariables_as_atoms`、`named_goals_share_but_bare_goals_are_fresh`、`contextual_goal_reports_the_local_binder_context` |

## Raw の保存 root

宣言側の root は [retention.rs](../src/elab/src/environment/retention.rs)、macro 側の root は [macros.rs](../src/sema/src/macros.rs) の `retained_raw_roots` で列挙する。

| 保持元 | 生存する項 |
| --- | --- |
| 定義 | Set/Prop と Program の型・本体 |
| inductive・record | parameter、index、constructor telescope、recursive field の index |
| Program datatype | constructor field の型と reflection の宣言 |
| module | parameter の型、checking context |
| namespace instance | 合成された引数 |
| 遅延特殊化 | 代入する論理項・Program 項と反映済み引数 |
| nominal identity | 比較に使う特殊化引数 |
| macro | template の解決済み項、遅延 remapping の代入項 |
| query output | 表示を待っている論理項・Program 項 |

raw の inference cache、context interner、weak-head cache、metavariable store は unit 終了時に解放する。
kernel の検査済み宣言に対する cache は snapshot の検査中に共有し、検査終了時に解放する。
`--stats` の `raw allocated nodes` は総割当数、`raw nodes` は保持数、`raw declaration nodes` は宣言 root からの到達可能数を示す。
既存の `REF_TYPE_PROFILE_DECLARATIONS` と `REF_TYPE_PROFILE_LOCAL_DEFINITIONS` は引き続き利用できる。

## Package 化と構文の移行

`libs/std`、`libs/real`、`libs/topology` は、それぞれ `ref.toml` と `src/root.ref` を持つ。
ライブラリ全体の利用例は `tests/library` の package に移した。
package の表示名と依存の参照名を分離し、manifest の実体に対応する `PackageId` で名前空間を区別する。
コンストラクタは `|` で区切り、inductive 宣言全体を `;` で終える。
移行後の workspace test は 227 件が通った。

## 責務ごとの crate 分割

`syntax` は source の AST と parser、`hir` は展開用の構文と proof block を持つ。
AST から HIR への変換は `hir::ModuleItem::from` と `hir::SExp::from` を入口にし、source location と構造を引き継ぐ。
module scheduler は AST を参照し、検査する宣言と module parameter ごとに HIR を作って処理後に解放する。
後続の宣言が使う macro template は sema の macro 環境が保持する。
macro の scope、宣言順、展開深さ、生成された hole の origin は HIR に保持する。
HIR の `ScopeId` と `CapturedId` の意味は sema の resolver と capture table が管理する。

`sema` に module scheduler、名前解決、macro 環境と展開、宣言の公開を移した。
`elab` に推論用の項、arena、簡約、metavariable、制約、kernel bridge をまとめ、論理項と Program 項の elaborator は `Handler` trait で sema に接続する。
macro の capture table にある項も宣言境界の保存 root に含め、module の特殊化では新しい capture を作る。
これにより `raw` crate の責務は移行先に収まり、workspace と依存関係から削除した。

依存方向は `cli → sema → elab → hir → syntax` と `elab → kernel` を基本とする。
`syntax` と `hir` は推論環境や kernel への依存を持たない。
kernel の nominal ID と module context の分離は、後述する Phase 4 で実装した。
宣言成果物の独立所有、通常参照を事前に解決した HIR、宣言単位の incremental query、永続 cache は後続の作業として残る。

分割後の `cargo test --workspace --locked --offline` は doctest を含む 228 件が通った。
追加した `captured_parameters_survive_specialization_and_rechecking_parsed_syntax` は、二段階の module 特殊化、宣言境界の回収、同じ AST を使った別環境での再検査を確認する。
`cargo clippy --workspace --all-targets --locked --offline -- -D warnings` と `cargo fmt --all -- --check` も通った。

release build の `tests/library/ref.toml --stats` は成功し、1 回の実行で elapsed 18.05 秒、peak RSS 444080 KiB だった。
推論用の論理項は総割当 7,973,220、保持 70,679、kernel の宣言から到達可能なノードは 71,941 だった。

## Program の局所参照

Program の lambda、宣言引数、let、sequence、case 分岐の束縛位置を保持し、変数の解決時に occurrence を記録する。
datatype・record・associated item の型引数にも束縛位置を対応付ける。
`\run` と `\runCase` の証明を検査する論理 context にも位置情報を引き継ぎ、`definition_at` から Program 側の束縛元を取得できる。
case 分岐の検査が失敗した場合も、分岐に入る前の context と束縛位置へ戻す。

追加した semantic API のテストは、lambda・let・sequence の shadowing、case 分岐間と分岐後の scope、型引数、反映された証明 context の参照先を確認する。
`cargo test --workspace --locked --offline` は library examples と doctest を含む 232 件が通った。
`cargo clippy --workspace --all-targets --locked --offline -- -D warnings` と `cargo fmt --all -- --check` も通った。

## AST の式範囲と HIR の対応

AST の式を `Expr<K>` と構文の種類に分け、source occurrence に `AstId` と UTF-8 byte range を付けた。
Program の値型・計算型・値・計算・適用の先頭にも同じ構造を使い、構文の分類時に occurrence を引き継ぐ。
括弧を含む式全体の範囲と、内部のコメントを含む適用などの範囲を保持する。
AST の clone は ID を引き継ぎ、別の parse には別の ID を割り当てる。

HIR の式は `origin: Option<AstId>` を持ち、[source map](../src/syntax/src/source_map.rs) が AST の occurrence と元ファイル、展開・生成の履歴から位置を取得する。
`AnalysisSnapshot::ast_location` は、その snapshot の到達可能な module tree にある ID を版付きの位置へ変換する。
elaboration 中のエラーは、失敗した式の origin を使って診断位置を取得する。
macro capture は渡された式の origin を保持し、template 由来の失敗は呼出位置へ戻す。
外部 module の parameter は宣言元のファイル、本体は読み込んだファイルに対応付ける。

追加したテストは式の範囲、occurrence の同一性、Program の構文分類、AST から HIR への対応、診断後の回復、macro capture と呼出位置、外部ファイル、snapshot 間の ID と位置を確認する。
`cargo test --workspace --locked --offline` は library examples と doctest を含む 241 件が通った。
`cargo clippy --workspace --all-targets --locked --offline -- -D warnings`、`cargo fmt --all -- --check`、`git diff --check` も通った。

## 展開・生成の履歴と検査項の対応

source map は AST の位置に加えて `Expansion`、`Template`、`Capture`、`Generated` の対応を持つ。
展開ごとに新しい ID を割り当て、呼出 occurrence、定義名、template 内の occurrence、capture 元を辿れる。
入れ子の展開は呼出 occurrence を通じて親展開へ接続し、module の特殊化を経た template も定義元の対応を保持する。
履歴用の ID と AST の ID は同じ一意性空間にあり、`ast_location` は snapshot の AST に属する ID を解決する。

生成理由は糖衣展開、暗黙の型、推論中の関数型、elaboration、kernel lowering を区別する。
HIR の構造を辿って生成元を補い、elaboration の結果に含まれる生成された raw 部分項にも個別の対応を作る。
zonk と kernel lowering は元の項の occurrence を引き継ぐ。
goal の履歴には、制約を通じて関係する暗黙の型の生成元も含める。

[provenance](../src/elab/src/provenance.rs) は、共有された raw・kernel handle とは別に elaboration の occurrence tree を保持する。
論理・Program・metavariable の検査は失敗した項から外側へ向かう検査経路を記録し、その経路と occurrence tree を照合して診断位置を取得する。
同じ項を複数回使う適用では、祖先の経路から失敗した引数を区別する。
一意に復元できない共有項は候補の共通の AST occurrence へ戻す。
kernel の `check_error` は失敗した検査経路を公開し、成功した次の検査で解放する。
構文分類の試行を切り替える際は、採用するエラーの origin を保存してから検査履歴を初期化する。

AST の identifier と hole token にも occurrence ID を付け、HIR の identifier、binder、hole は対応 ID を保持する。
括弧を含む式の範囲と hole token の編集範囲を分離する。
参照位置と binder 位置はそれぞれ source map から元ファイル込みで取得する。
同じ template の参照を複数回展開した場合は、表示する参照位置をまとめつつ各展開の履歴を保存する。
`Diagnostic`、`Occurrence`、`GoalSnapshot` は snapshot の版付き位置へ変換した `SourceOrigin` を保持し、macro の定義元は診断の secondary location にも含める。

この節の四項目は実装済みである。
通常参照の事前解決と workspace index は、未使用の template や未解決の宣言も列挙する経路が必要なため、Phase 3・6 の作業として残る。
宣言成果物の独立所有、局所 transaction、incremental query、永続 cache の残作業は Phase ごとの表に示した。

追加した九つのテストは、論理・Program の共有引数の診断位置、曖昧な共有項の共通 AST への対応、生成 raw 部分項、kernel 検査経路、暗黙の型の生成元、入れ子の展開、外部 template の複数展開、括弧内の capture hole を確認する。
`cargo test --workspace --locked --offline` は library examples と doctest を含む 250 件が通った。
`cargo clippy --workspace --all-targets --locked --offline -- -D warnings`、`cargo fmt --all -- --check`、`git diff --check` も通った。

## Phase 4: Kernel bridge と所有環境

semantic な `ModuleId`、`ModuleParamId`、`DefId` と nominal ID は [elab/ids.rs](../src/elab/src/ids.rs) に置いた。
kernel は所有環境付きの opaque な `GlobalId`、`InductiveId`、`ProgramInductiveId` を発行し、[bridge](../src/elab/src/lowering/bridge.rs) が semantic ID との対応を保持する。
kernel のコードと README に project の ID への参照は残っていない。

module parameter は kernel の外側 context へ写す。
外側の変数は de Bruijn level、式内の binder は従来の de Bruijn index で参照し、context を拡張しても検査済み template の項を変更する必要がない。
`push_binding` は prefix の下で classifier を検査してから context を拡張する。
`register_definition_template` は開いた宣言を検査し、`instantiate_template` は利用側の context の下で引数・body・classifier・局所 telescope と Program reflection を検査する。
module 特殊化と nominal identity の選択は semantic layer にあり、証明 parameter を持つ module に追加の product rule は要求されない。

再帰 spec の一時登録には RAII の transaction を置いた。
型エラーと取消では一時 spec、同時生成した mirror、公開履歴、推論・簡約 cache を巻き戻す。
検査経路のデバッグ情報は、scope の終了後も有効な handle を保持する。

[Environment::transfer](../src/kernel/src/transfer.rs) は公開済み context と宣言を依存順に新しい arena へコピーし、nominal ID と mirror の対応を再割当てして再検査する。
DAG の共有を維持し、移送元を破棄した後も移送先だけで検査できる。
`CheckedArtifact::transfer_kernel` は raw 環境を参照しない `KernelArtifact` を返し、コピーと kernel 再検査の所要時間を別々に報告する。
現在の移送単位は snapshot の所有環境であり、使用中の snapshot・成果物の最後の参照がなくなると環境が回収される。

追加テストは環境間の handle・nominal ID の取り違え、依存する外側 context、局所 binder を含む同時代入と reflection、取消後の再登録、移送元と移送先の独立した回収を確認する。
`substitution-identity.ref`、Program の関連定義と namespace identity を新しい環境へ繰り返し移し、到達可能ノード数の安定も確認する。

release の `tests/library/ref.toml --stats` は単独実行で elapsed 18.77 秒、peak RSS 835868 KiB だった。
source map・provenance の変更を含む作業ツリー全体での計測であり、先の crate 分割時の測定とは実装条件が異なる。
raw の論理項は総割当 7,973,219、保持 70,679、kernel の宣言から到達可能なノードは 71,941 だった。
取消時の巻き戻しを含む最終実装でライブラリ全体の移送を再計測し、2,705 宣言、71,941 ノードのコピーに 0.192 秒、kernel 再検査に 9.227 秒かかった。
移送後の到達可能ノード数も 71,941 である。

```sh
cargo test -p sema library_transfer_measurement --release --locked --offline -- --ignored --nocapture
```

最終の workspace test は library examples と doctest を含む 255 件が通り、通常実行では除外する上記の全ライブラリ移送計測も個別に成功した。
`cargo clippy --workspace --all-targets --locked --offline -- -D warnings`、`cargo fmt --all -- --check`、`git diff --check` は成功した。
`src/kernel` 内の `ModuleId`、`ModuleParamId`、`DefId`、`ModuleParam` の検索結果は 0 件だった。

### 対象の完了条件と残る作業

Phase 4 の完了条件である calculus の情報だけによる kernel 検査、module substitution と nominal identity の維持、環境間の再配置、旧環境の回収を満たした。
kernel から project ID が消える段階への到達を、実装・依存・テストで照合した。

保存用 raw の宣言ごとの独立所有と sema の局所 transaction は、現在の snapshot 共有・失敗時再実行を宣言単位の再利用へ細分化する作業として残る。
通常参照の事前解決は、既存の Resolver interface と occurrence 記録から、未使用 template も含めた事前 index を作るために残る。
これらは kernel が project ID を必要とする理由ではなく、Phase 2・3 の細分化と Phase 5・6 の incremental/index 経路に関わる。
永続 cache は Phase 8 の対象であり、確定した保存仕様に従う serialization・disk store と cache 有無の比較を残す。
現在の kernel 移送は読み込まれた DAG の再配置・再検査部分として利用できる。
