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
| 1 | VFS、版付き location、構造化診断、回復 AST、identifier・hole の range、outline の ID 対応、共通 CLI 入口を実装した。式全体の range は追加対象である。 |
| 2 | 作業領域の回収、公開 root の保存、宣言境界の kernel check、goal snapshot、失敗時の再実行を実装した。保存領域の宣言ごとの独立所有と、再実行を置き換える局所 transaction が残る。 |
| 3 | 実際に選択された通常参照、論理 binder、record field の occurrence を記録する。AST と proof HIR を分離し、scope/capture の ID、macro 環境、Resolver interface を独立させた。完全な展開 origin と通常参照の事前解決が残る。 |
| 4 | arena identity、成果物の所有環境、`MetaVarId` の移動を実装した。kernel の opaque nominal ID、module parameter の context 化、環境間の成果物移送が残る。 |
| 5 | 同一入力 snapshot の結果を再利用し、本体・挿入・削除・名前・shadowing・import・構文回復・取消の編集列を cold result と比較する。変更後は全体を再検査するため、宣言単位の依存追跡・再利用が残る。 |
| 6 | goal の表示、`give`、`refine`、macro capture の編集可否、LSP・MCP の初期 adapter を実装した。完全な展開 origin、Program の局所参照、`apply`、case split、normalize、workspace index の完成が残る。 |
| 7 | path 依存の PackageGraph、manifest 入力、PackageId、package 間の import と、std・real・topology のライブラリ分割を実装した。各 package の宣言を dependency 経由で参照できる。 |
| 8 | 永続 artifact cache、ID の復元、kernel 再検査の経路が残る。 |

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
kernel の nominal ID と module context の分離、宣言成果物の独立所有、通常参照を事前に解決した HIR、宣言単位の incremental query、永続 cache は後続の作業として残る。

分割後の `cargo test --workspace --locked --offline` は doctest を含む 228 件が通った。
追加した `captured_parameters_survive_specialization_and_rechecking_parsed_syntax` は、二段階の module 特殊化、宣言境界の回収、同じ AST を使った別環境での再検査を確認する。
`cargo clippy --workspace --all-targets --locked --offline -- -D warnings` と `cargo fmt --all -- --check` も通った。
release build の `tests/library/ref.toml --stats` は成功し、1 回の実行で elapsed 18.05 秒、peak RSS 444080 KiB だった。
推論用の論理項は総割当 7,973,220、保持 70,679、kernel の宣言から到達可能なノードは 71,941 だった。
