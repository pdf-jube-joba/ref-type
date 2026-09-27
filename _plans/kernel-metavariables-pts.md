# PTS 形式の共通項と kernel のメタ変数・単一化

## 到達点

kernel と elaboration が、sort・型・項・証明・メタ変数を表す共通の `Expression` を使う。
定義は専用 arena に保持し、項からは `DefinitionId` と文脈引数で参照する。
kernel は型規則、代入、簡約、reflection、メタ変数への代入、単一化、制約の保留と再実行を所有する。
elaboration は表面構文の解釈、名前解決結果の利用、暗黙引数とゴールの生成、module の特殊化、source location を使った診断を担当する。
`doc/book/src/system.md` は、単一の項構文と PTS の判断で体系を記述する形へ書き直す。

`check` と `infer` の公開 API は、必要な情報が未解決なら未解決メタを示すエラーを返せる設計にする。
未完成の項の型制約を扱う処理も kernel にまとめ、elaborator からはその操作を呼び出す。
宣言登録は、文脈・本体・型・付随する証明のメタ変数と制約を解決し、完成した項を検査してから行う。

## 実行方針と成果の提示

実装開始後は、この計画の全工程と完了条件を一つの作業単位として、自律的に完了まで進める。
実施順序は実装者の内部手順とし、各工程の検証結果に基づいて修正と次の工程への移行を判断する。
API の詳細、移行中の接続方法、実装上の選択は、到達点と型規則に沿って実装者が決定する。
途中で見つかった不整合やテスト失敗は、その原因の調査・修正・再検証まで同じ作業に含める。
ユーザーには、全工程を終えた実装・文書・重複実装の整理を含む完成形と、検証結果・計測結果・重要な設計判断をまとめて提示する。

## 現在の対応箇所

| 場所 | 現在の役割 | 移行後 |
| --- | --- | --- |
| `src/kernel/src/syntax.rs` | 十二 family の構文と arena | 単一の項 handle と node、共通 arena |
| `src/kernel/src/environment.rs`、`src/kernel/src/ids.rs` | `GlobalId` をキーとする定義登録 | 定義 arena と、登録時に返す `DefinitionId` |
| `src/kernel/src/check.rs` | 分類済み構文の型検査 | PTS 形式の型検査と共通の型制約生成 |
| `src/kernel/src/sort.rs` | sort と product signature | sort の公理・product 関係の共通実装 |
| `src/kernel/src/structure/`、`src/kernel/src/calculus.rs`、`src/kernel/src/reflection.rs` | family ごとの構造操作と意味論 | 共通項に対する操作 |
| `src/elaboration/src/metavariables.rs` | 論理側のメタ変数・型推論・単一化 | kernel の共通 solver と elaboration の診断情報へ分配 |
| `src/elaboration/src/elaborator/program_term_elaborator/inference.rs` | Program 側のメタ変数・単一化 | 同じ kernel solver へ統合 |
| `src/elaboration/src/raw/` | 独自の項・型検査・簡約・reflection | 共通 kernel API へ移行し、elaboration 固有の情報を整理 |
| `src/elaboration/src/lowering/` | raw の分類、構文変換、宣言登録 | 捕捉する parameter の整理、ID の対応、kernel 宣言登録 |

論理側は `MetaStore::infer_pts` と `raw::derivation` の両方に型規則を持ち、lowering も raw の型推論を呼んでいる。
Program 側にも独立した型検査と solver があるため、両系列を移行対象にする。

## 共通項の設計

`Expression` は単一の intern 済み handle とし、子の項、binder の型、型引数、証明を同じ handle で保持する。
sort 自身も項として表し、型推論を文脈の下での \(\Gamma\vdash e:A\) に揃える。
sort の公理と product 関係は、現在の \(\mathcal A\) と \(\mathcal R\) を検査する。
上位 sort は項として表現し、その形成可能性を公理と型規則に従って判定する。

変数は共通の de Bruijn index、文脈は依存する型を順に持つ telescope とする。
`SymbolId` は表示用の名前、`DefinitionId` と帰納型 ID は宣言の同一性を表す。
構築時に必要な情報は演算の種類・引数・binder とし、結果の sort・level・product rule は型検査で導出する。
Set/Prop の簡約と Program の評価位置を区別する演算 tag は、統一した node の中に保持する。
構文の分類が必要な操作は、型検査の結果またはその演算 tag を利用する。

refinement の集合と述語、Box の computation、Program の型引数などの適切さは、それぞれの型規則の前提として検査する。
Program type/kind の変数依存条件は、型変数だけを含む文脈での形成検査として扱う。
non-cumulative な level、CBPV の評価位置、証明注釈、帰納型の positivity、Program と Set の reflection を共通項上に移す。

## 定義 arena と参照

定義 arena の各 entry は、検証済みの `Definition { context, ty, body }` を保持する。
登録 API は文脈・宣言型・本体の検査を完了して entry を追加し、その handle として `DefinitionId` を返す。
定義は登録後に不変とし、各宣言に固有の handle を割り当てる。
本体と型の構造共有は項 arena の interning が担当する。

共通項に `Definition { id: DefinitionId, arguments: Vec<Expression> }` を設ける。
参照の型推論は、引数列を宣言文脈の telescope に対して検査し、宣言型に同時代入した結果を返す。
弱頭簡約や定義的等価性が展開を必要とするときに、本体へ同じ引数列を代入する。
参照のシフト・代入・zonk は引数列を変換し、定義 ID を保持する。
自由変数・閉性の検査では、参照先が検証済みであることと、明示された文脈引数を用いる。

定義の名前、source location、module の所属は elaboration 側で `DefinitionId` に対応付ける。
診断は参照 ID と引数列から名前付きの式を表示し、展開済みの項はその構造を表示する。
module の特殊化と再読み込みでは、元の宣言と新しい定義 handle の対応を構築する。
Program の反映先も検証済み定義として登録し、元定義と反映先の handle の対応を保持する。
reflection は参照先と文脈引数の対応を使って、Set 側の定義参照を構築する。

handle の有効範囲は所有する arena に揃え、定義から到達する文脈・型・本体は項 arena の回収時にも保持する。
永続化された宣言の識別子と実行中の `DefinitionId` は、読み込み時の対応表で接続する。
kernel の `GlobalId` と `Annotated`、`identified`・`annotated`・`global_id` API は、この参照方式へ移行して削除する。
匿名型注釈は elaboration で期待型に対する検査を行い、項本体へ落とす形に整理する。
宣言された型を保持する役割は、定義 arena の `ty` が担う。

## メタ変数と単一化

### 状態と文脈

kernel に `MetaContext` と `ConstraintStore` を置く。
各メタ変数は宣言時の telescope、期待される型またはその形成制約、代入状態、依存するメタ変数を保持する。
出現は `Meta { id, arguments }` とし、`arguments` は宣言文脈から出現文脈への代入を表す。
項・型・sort が未確定な場合も、この共通表現と形成制約で扱う。
level の数値は現行の sort の添字として扱い、sort 全体の確定を待って product 関係を検査する。

メタ変数 ID は session または世代を含めて識別し、宣言ごとの状態回収と整合させる。
名前付き穴の共有範囲、暗黙引数、明示ゴールなどの由来は elaboration 側で ID に関連付ける。
kernel の制約には不透明な由来 ID を付け、source location と表示上の名前は診断時に結び付ける。

### 型検査との接続

| 操作 | 結果と役割 |
| --- | --- |
| `infer(context, expression)` | 確定した型、型エラー、または未解決情報を返す |
| `check(context, expression, expected)` | 型規則を検査し、成功・型エラー・未解決情報を返す |
| 型制約の登録 | 同じ型規則を用いて未完成の項の検査を進め、必要な判断を制約として保持する |
| `unify(context, left, right)` | メタ変数への代入を進め、解決・保留・矛盾を区別する |
| `solve_pending()` | 依存するメタ変数が更新された制約を再実行する |
| `zonk(expression)` | 解決済みメタ変数を文脈引数で具体化する |
| 宣言の確定 | 残ったメタ変数と制約を診断し、完成した宣言を再検査して登録する |

API 名は実装時に揃える。
通常の型検査と制約生成は型規則の実装を共有し、判断に必要な情報が不足した場合の処理を切り替える。
内部では宣言済みメタ変数の型を参照して検査を進められるようにし、公開 `check`・`infer` の成功は対象の未解決情報が解消した時点で返す。
文脈と期待型に残るメタ変数も、未解決情報の対象に含める。

### 解決手順

1. 解決済みメタ変数を展開し、kernel の弱頭簡約と定義的等価性を使って両辺を比較する。
2. rigid な構文は演算・宣言 ID・引数を比較し、binder の下では文脈を拡張して制約を分解する。
3. 相異なる文脈変数への適用になっているメタ変数について、引数の対応を逆に辿って右辺を宣言文脈へ戻す。
4. occurs check、scope、文脈引数の型、期待型との整合性を確認して代入する。
5. 型の整合性に追加情報が必要なら、候補とその検査義務を追跡し、義務の解消を解決完了の条件にする。
6. 同じメタ変数の異なる引数への出現、両辺がメタ変数の場合、一般の関数適用への出現は、解ける場合を処理して残りを依存情報付きで保留する。
7. 代入により依存先が更新された制約を再実行し、矛盾・未解決・完了を診断へ返す。

現在の論理側 solver の identity spine と Program 側 solver の abstraction を調べ、共通の文脈代入・抽象化操作にまとめる。
定義参照の比較では、同じ ID と等価な引数列による一致を先に調べ、必要に応じて本体を展開する。
引数を使わない定義や異なる定義の等価性も扱えるよう、定義の引数比較と展開の選択を制約処理に組み込む。
候補の試行には snapshot と rollback を用意し、失敗時には代入・制約・キャッシュを整合する状態へ戻す。
型や文脈を通じた依存も循環検査に含める。
reflection が未解決の Program 項に依存するときは、その変換を制約として保持し、元のメタ変数の更新に合わせて再実行する。

### 共有とキャッシュ

構文ノードは不変とし、メタ変数への代入は `MetaContext` に保持する。
メタ変数を含む項の推論・弱頭簡約・zonk のキャッシュは session に属し、初期実装では代入更新と rollback ごとに無効化する。
完成した項のキャッシュは検証済み環境に保持する。
arena の一時ノード回収は、メタ変数の文脈・型・候補・制約から参照されるノードも生存対象に含める。
現在のノード数・キャッシュ数・宣言別計測・tracing を共通項と solver に対応させる。

## system.md の PTS 形式への書き直し

冒頭の注意書きはそのまま保持する。
体系の定義を `system.md` に、solver の状態管理と実装 API を kernel の説明に記述する。

1. `Syntax family` と各構文表を、sort・変数・積・lambda・適用・各固有演算から生成する単一の項構文へ置き換える。
2. term・type・kind の分類を、共通の型判断と sort の関係で定義する。
3. 変数の分類と context の形成条件を型判断で与え、Program の型形成には型変数文脈を使う。
4. family の所属条件として与えていた引数の制限を、各型規則の前提へ移す。
5. capture-avoiding substitution を共通項上で定義し、binder 注釈・型引数・証明を含めた束縛範囲を揃える。
6. family 添字付きの簡約・定義的等価性を共通項上の関係へ置き換え、論理の compatible closure と Program の evaluation context の適用範囲を明記する。
7. `RfKind`・`RfType`・`RfTerm` の定義を共通項の reflection と型判断による適用条件へ整理する。
8. 帰納型の宣言・constructor・case・Set の鏡像を含めて、family に依存する表と前提を更新する。

product signature、non-cumulative な level、Program type/kind の依存条件、Box の閉性、run の証明条件、positivity を規則の前提として揃える。
過去の版は記法の参考とし、現在の各演算・型規則との対応表を作って書き直す。
既存の rule label は規則を参照する略記として整理し、実装では必要な演算 tag と推論で得る product 関係を区別する。
関連する `doc/book/src/props/` と `language/implementation.md` の構文・判断への参照も追跡する。

## 実施順序

### 1. 仕様と基準の固定

`system.md` の PTS 形式への書き直しと、各構文に必要な型検査の前提の棚卸しを行う。
kernel・論理側 raw・Program 側 raw の演算を対応付け、共通項に移す一覧を作る。
既存テストと標準ライブラリを同じ revision・ビルド条件で実行し、結果・時間・ノード保持量を記録する。

### 2. kernel の共通項への移行

共通項の arena、sort を含む項、文脈、構造走査、代入、表示を実装する。
定義 arena と参照ノードを実装し、宣言型を使った型推論、必要時の本体展開、Program の反映先への対応を接続する。
簡約・型検査・reflection・帰納型登録を移し、構文の型が保証していた条件を checker に移す。
elaboration の lowering を新しい kernel 項へ接続し、この段階で既存の完成した項を通す。
一時的な接続部分は対応する呼び出し元の移行に合わせて整理する。

### 3. kernel solver の実装

共通項に contextual metavariable と制約状態を追加する。
型規則を共有した制約生成、pattern の抽象化、代入検査、保留・再実行、rollback、zonk を実装する。
公開 `check`・`infer` の未解決エラーと、宣言を確定する入口を接続する。
reflection とキャッシュの更新をこの段階で検証する。

### 4. elaboration の移行

論理側と Program 側を、共通項の構築と kernel の型制約・単一化 API の呼び出しへ移す。
暗黙引数、名前付き穴、明示ゴール、block、induction、Program の型推論を順に接続する。
module parameter の捕捉・特殊化、帰納型 ID の対応、診断に必要な情報を整理する。
定義登録が返す handle を名前解決結果に対応付け、lowering の本体付き注釈を定義参照の構築へ置き換える。
匿名型注釈の期待型検査を elaboration に集約する。
macro・query・評価・LSP の型表示も、共通項と kernel API を参照する形に揃える。
永続キャッシュの検証済み状態と形式を点検し、型検査の変更を識別する version または fingerprint を更新する。

### 5. 重複実装の整理と全体検証

移行済みの raw 構文・型検査・簡約・reflection、論理側と Program 側の solver を削除する。
lowering に残る作業を宣言登録や module の処理へ整理し、不要になった分類用コードを削除する。
`Annotated` と `GlobalId` の構築・走査・表示・変換を削除し、利用箇所と既存テストを定義参照の API に揃える。
`src/kernel/README.md`、`src/elaboration/README.md`、`src/USAGE.md` と関連文書を更新する。
全体検証と移行前後の計測を行い、差が出た規則と処理を調べる。

## 検証

各段階では変更箇所に対応する既存テストと、次の性質を確かめる kernel テストを実行する。

- 文脈の弱化・並べ替えに伴うメタ変数の具体化と、依存する binder の下での単一化。
- 直接・間接の循環、scope 外の変数を捕捉する候補、期待型に合わない代入の検出。
- 保留した等式・型形成・reflection の制約が、代入後に再実行されること。
- rollback 後の代入・制約と、代入前後の推論・弱頭簡約キャッシュの整合性。
- 未解決の本体・型・文脈・証明に対する API の結果と、解決後の宣言登録。
- 同じ本体を持つ別定義の識別、宣言型を使った参照の型推論、依存する文脈引数の検査と具体化。
- 異なる定義や引数を使わない定義の展開による等価性と、単一化による引数の解決。
- 定義参照の reflection・module 特殊化・名前付き表示と、一時ノード回収後の handle の有効性。
- 匿名型注釈を含む入力の期待型検査と、注釈を処理した項を使う後続の型検査。
- refinement、Box、Program の型形成、level、positivity の型規則。
- メタ変数の解決後にも、Program の評価順序と Set 側の reflection が既存の結果に一致すること。
- 型の位置の `_`、暗黙引数、名前付き穴、block、induction、Program、module 特殊化を使う既存の成功例と診断。

`.ref` の fixture やライブラリを編集する場合は、少量ずつ `--parse-only` を通してから型検査する。
全体の gate は次を基本とする。

```sh
cargo fmt --all -- --check
cargo check --workspace --all-targets --locked --offline
cargo test --workspace --locked --offline
cargo run --release --locked --offline -p cli -- libs/std --no-cache --stats
```

性能は同じ入力・ビルド条件で、宣言別時間、arena の保持ノード数、キャッシュ件数、全体のメモリ使用量を比較する。
必要な箇所を `/usr/lib/linux-tools/6.8.0-139-generic/perf` で調べる。

## 完了条件

- `system.md` の項・代入・簡約・reflection・帰納型が単一の項構文と PTS の型判断で記述されている。
- kernel と elaboration が共通項を使い、論理側と Program 側の単一化を kernel が処理している。
- 定義 arena が宣言型と本体を保持し、参照・型推論・簡約・表示が `DefinitionId` と文脈引数を使っている。
- 型規則、構造操作、簡約、reflection の実装が kernel に集約されている。
- 未解決情報・型エラー・保留制約を区別でき、宣言登録時に必要な検査が完了する。
- 標準ライブラリ、既存の成功例と診断、kernel の検証が通り、計測・表示・tracing が利用できる。
