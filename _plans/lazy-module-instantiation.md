# モジュールのインスタンス化を項単位で遅延する

## 実装状況

- 完了: 仮想名前空間の安定 ID、定義・帰納型・datatype の項単位実体化とキャッシュ、
  実体化済み項だけを対象にする lowering、実体化数の計測。
- 完了: マクロ scope は source と代入環境を保持し、初回の可視性検索・展開時にだけ
  テンプレートを変換してキャッシュする。
- 完了: context を持つ関連定義の検査済みテンプレートを kernel 環境に保持する。
- 完了: 128 定義を16回 import する未使用／各1項使用の性能ケース。
- 未完了: 内部 instance の名前空間と ID スロット自体の疎なオンデマンド生成、raw の
  infallible getter をすべて fallible resolver に移行する作業、全 force 比較経路。

## 提案

インスタンスを「元モジュール・引数・参照先の対応を持つビュー」として作り、定義や帰納型は必要になったときだけ実体化する。インスタンスの生成と、構文への代入・ID の付け替え・検査を分離する。

最初の実装では **項単位の lazy materialization** を採用する。一つの定義を要求したら、その型・本体・反映証明と、検査に必要な依存先を実体化する。型だけを要求した場合も、その定義の本体は検査する。式の各ノードに遅延代入を持たせたり、本体の検査を評価時まで延期したりするところまでは行わない。

kernel は、元の宣言の検査結果を保持する入口と lowering の連携を整える。初版ではインスタンスの具体的な宣言も通常の kernel 検査を通す。これなら、代入の正しさを新しい信頼境界として一度に導入せず、未使用の項を複製しない効果を先に得られる。

この文書はコードを調査した実装案であり、性能改善率は未計測。

## 現状と変更が必要な理由

| 箇所 | 現在の処理 | 変更点 |
| --- | --- | --- |
| `ModuleManager::instantiate_module_from` | 引数を検査した後、経路上のモジュールとその `instances()` を列挙し、全項を `PendingItem` に展開する | 経路と引数の確定、およびインスタンスの生成までにする |
| 同関数・`materialize_associated_definitions` | 型・本体・帰納型仕様・関連定義・反映証明を代入し、ID を付け替えて登録する | 要求された項と依存先に対して一度だけ行う |
| `CrateEnv::ModuleInstance` | `materialized: ModuleId` と全体の `InstanceRemapping`、origin 表を持つ | 軽量な名前空間と代入環境、実体化済み項のキャッシュを持つ |
| `get_item`・マクロの解決 | 複製先モジュールの項やマクロを参照する | 元の名前表とインスタンスのビューから参照を作る |
| `Lowerer::lower_all` | raw の全 parameter・inductive・datatype・definition ID を走査する | 元の宣言を全検査し、派生インスタンスは要求されたものだけ lowering する |
| `Lowerer::checked_templates` | 型引数付きの関連定義などの検査済み状態を、個々の Lowerer に保持する | 同一 kernel 環境内で持続する検査済みテンプレートとして扱う |

特に `lower_all()` を残したまま getter だけ遅延化すると、最後に全項が実体化される。`add_new_module_to_root()` の終了処理まで含めて変更する必要がある。

参照コード:

- [module_manager.rs](../src/front/src/elaborator/module_manager.rs)
- [modules.rs](../src/front/src/elaborator/modules.rs)
- [raw/environment.rs](../src/front/src/raw/environment.rs)、[raw/dependencies.rs](../src/front/src/raw/dependencies.rs)
- [lowering/declarations.rs](../src/front/src/lowering/declarations.rs)、[elaborator.rs](../src/front/src/elaborator.rs)
- [kernel/environment.rs](../src/kernel/src/environment.rs)

## 維持する意味論

1. **Generative な同一性。** 同じモジュールに同じ引数を渡しても、別のインスタンスを作る操作なら帰納型の ID は別になる。`(source, arguments)` によるインスタンスの共有はしない。同じ import alias からの複数回の参照は同じ ID を返す。
2. **親の共有。** `P.Child(...)` は既存の `P` を親として保持する。別途 `P.Child(...)` を実行すると child は新しくなるが、親を作り直さない。フルパスからの生成では経路の各成分に新しい同一性を与える。
3. **宣言順と可視性。** 元の宣言は未使用でも elaboration と kernel 検査の対象とする。遅延化によって不正な未使用宣言や前方参照を許可しない。
4. **引数の検査。** 名前・個数・カテゴリ・依存する型をインスタンス作成時に検査する。metavariable を解決してから引数を保存し、不正な未使用 import もその場で拒否する。
5. **反映と閉性。** Program datatype と Set の鏡像の同一性、証明付き反映、Box の閉性検査、帰納型の positivity 検査を維持する。

1 と 2 は [現在の構文仕様](../doc/book/src/coding/syntax.md) および `repeated_instantiation_is_generative_and_remaps_internal_definitions`、`inductives_from_two_instances_are_distinct_types` などの既存テストを基準とする。内部の数値 ID の割り当て順自体は互換性の対象にしない。

## データ構造

### 元の宣言とインスタンスのビュー

元モジュールの名前表・宣言スロット・関連項一覧・マクロのスコープを共有する。公開済みモジュールの内容は固定し、構築中のモジュールについては参照可能だった宣言の範囲を保持する。後から追加された名前が過去の参照に見えるようにはしない。

概念上、以下の情報を持たせる。名前は仮称。

```rust
struct InstanceView {
    source: ModuleId,
    namespace: ModuleId,             // 宣言本体を持たない仮想名前空間
    parent: Option<ModuleInstanceId>,
    substitution: SharedSubstitution,
    scope: CapturedScope,
    // (この instance, 元の内部 instance) ごとの派生 instance をメモ化
    // 実体化した定義・帰納型・datatype を疎なキャッシュに保持
}

enum Materialization<T> {
    Pending,
    Computing,
    Ready(Rc<T>),
    Failed(MaterializationError),
}
```

`SharedSubstitution` は親への参照とその段で追加する引数から構成し、子を作るたびに親の全 remapping を clone しない。lookup の結果や必要になった合成結果をメモ化する。raw arena と kernel arena の handle は混ぜず、各環境で別の代入表を持つ。

### ID の発行と実体の生成を分ける

現行の `DefId { module, index }`、`InductiveId`、`ProgramInductiveId` は維持できる。仮想名前空間内では、`index` を元の同種の宣言スロットに対応させる。公開名の並びではなく、関連定義・自動生成された射影・鏡像を含む各 ID のスロットを使う。

これにより、名前や依存先の ID を取得するだけなら、項の本体を読まずに済む。名前空間を区別すれば同じ引数でも ID は異なり、同じ項の二回目の lookup は必ず同じ ID を返す。仮想名前空間のスロット数だけ `Pending` を確保することも避け、キャッシュ未登録を未実体化として扱う。

`materialized` は移行中は仮想名前空間の ID として残せるが、最終的には `namespace` へ改名する。`ModuleEnv` の実データ用 `Vec` を直接読む箇所は lookup API に集約する。origin は `(instance, source slot)` から導出し、全定義分の逆引き表を生成しない。

## 解決と実体化の流れ

### インスタンス作成

1. モジュール経路を解決し、現在の `solve_module_arguments` と引数検査を実施する。
2. 経路の各成分について新しいビューを作る。base instance がある場合はその環境を継承する。
3. 後続のパラメータ型が親の帰納型や定義を参照する場合、親ビューで ID を解決する。型検査に必要な項はこの時点で実体化してよい。
4. 検査が完了したビューを import alias へ公開する。全項の列挙・本体の代入・マクロの一括複製は行わない。

経路全体で使う親ビューは一つに固定する。後続引数の型検査用に作った親と、最終的な child の親が別インスタンスになってはいけない。失敗した経路の仮想 ID は外部へ公開しない。ID の欠番は許容する。

### 内部のインスタンス

`Outer` の宣言中に作られた `Inner(...)` は、`Outer` のインスタンス化時に引数を外側の環境で置換する必要がある。元の内部 instance の provenance を保存し、`(outer instance, source internal instance)` をキーに派生ビューを作る。同じ派生ビューを参照ごとに生成し直さない。

これは名前付き import に限らない。元の `instances()` が保持している、式中のアクセスで生成された匿名のインスタンスも対象にする。異なる外側のインスタンスでは、内部の引数が偶然同じでも派生ビューを共有しない。外側の環境に属さない既存の外部 instance への参照はそのまま共有する。

参照元の所属を判定して派生ビューへ振り分け、最終的な source 定義 ID だけに潰さない。同じ source に由来する二つの内部 instance を区別するためである。親・内部 import の対応はオンデマンドで生成し、未使用の内部 instance の木を再帰的に展開しない。

### 項の要求

名前解決は元の項のメタデータからインスタンス側の ID を返す。型推論・定義展開・帰納型検査などが実体を要求した時点で、次の処理を行う。

1. ID から元の宣言とビューを求める。キャッシュ済みならその結果を返す。
2. 元の型・本体・反映証明に代入と参照の付け替えを行う。他の宣言の本文までは展開しない。
3. 変換した宣言の依存先を収集し、必要な実体を準備する。型注釈・証明・Program の内部にある Set 参照も含める。
4. raw 側で現在行っている検査を実施し、成功した値を `Ready` にする。kernel が必要とする場合は、この具体的な宣言を lowering して kernel に登録する。

最初は型・本体・反映証明を一組として扱う。帰納型は arity・全コンストラクタと自己参照を一組にする。関連定義は帰納型の仕様とは別の項として遅延する。Program datatype とその Set 鏡像は両 ID を先に確定し、一組として整合性を検査・公開する。

依存先を準備する順序は現在の `raw/dependencies.rs` と `Lowerer::definition()` の明示的な worklist を拡張する。長い import chain を Rust の再帰呼び出しだけで処理しない。通常の定義の `Computing` 再入は循環エラーとし、帰納型の自己参照だけは検査中の専用ビューで許可する。

### 代入の規則

元の式の global 参照をビューで解決し、module parameter に達したら呼び出し側の引数を適切に shift して挿入する。**挿入した引数を、さらに参照元モジュールの remapping で走査しない。** 引数に含まれる呼び出し側の型・定義を、誤って新インスタンスの型・定義へ付け替えることを防ぐ。

合成は `instantiate(inner_argument, outer_view)` を確定してから内側の代入に使う。binder depth と family ごとの規則を保ち、Program の型引数・値引数・Set に反映した引数を区別する。kernel の既存 `substitute_parameters()` は `ModuleParam` を処理する関数なので、将来 kernel 内で実体化する場合は `ReflectedProgramParam` の置換も別途実装する必要がある。

局所変数を含む引数には生成時の context を保持する。現在も `add_module_in_scope` と `checking_contexts` がこの用途で使われ、`nested_instance_materializes_parent_dependencies` が `Bound(0)` の場合を検証している。context の長さだけをキーにした共有はしない。kernel の通常の名前付き定義には自由な `Bound` を登録できないため、raw の context 保存をそのまま kernel での閉性保証とみなさない。局所変数を含む場合は既存の lowering の受理範囲を維持し、必要な抽象化・適用を省略しない。

## lookup API とエラー処理

raw の `definition()`・`inductive()`・`program_inductive()` は現在、存在する実体への参照を返す。遅延化後は実体化が失敗し得るため、例えば `resolve_definition(id) -> Result<Rc<DefinedConstant>, MaterializationError>` に置き換える。メタデータだけを読む API と、実体を要求する API を分ける。

`CrateEnv` を共有参照で使う checker・reducer からも呼べるよう、疎なキャッシュと状態には内部可変性を使う。キャッシュの borrow は状態の取得・更新時だけに限定し、依存先の解決や checker の呼び出し中には保持しない。`Rc` で取得済みの結果を保持し、再入時の `RefCell` panic を避ける。式変換のメモ化キーにはビューと binder depth を含める。

この変更は環境だけでは閉じない。raw の derivation、calculus、program_calculus、reflection、dependencies と、その呼び出し元を更新する。現在 infallible な評価入口にも実体化エラーを伝える経路を設け、lookup 失敗を「展開できない定数」や `OutOfFuel` に置き換えない。

検査失敗は同じ不変ビュー内ではキャッシュする。検査途中の項や失敗した datatype/mirror の組は通常の lookup に公開しない。登録によって変わる正規化・型推論キャッシュは既存の invalidation 規則を維持し、失敗時にも検査中の結果が残らないようにする。診断には元の宣言位置とインスタンス作成位置を保持する。

## kernel と lowering の変更

初版では kernel の式に instance や suspension の新しい構文を追加しない。`Constant`・帰納型の参照は従来の ID のままとし、kernel が検査・評価する時点では必要な具体的宣言を登録済みにする。

`lower_all()` は以下に分割する。

- `check_source_declarations()`：新しく追加された元の宣言をすべて kernel で検査する。未使用の宣言も対象とし、宣言が参照するインスタンスは依存先として要求する。
- `ensure_lowered(id)`：問い合わせや宣言の lowering が実際に参照したインスタンス項を、その依存先とともに登録する。
- raw 側ですでに実体化した項を現行の最終検査と同様に保証するための要求キュー：最終処理はこのキューを消化し、仮想名前空間の全スロットは列挙しない。

元の宣言の検査に依存先が必要なら、その依存先まで遅延させることはできない。たとえば元のモジュール自身が内部 import の全項を参照していれば、その検査コストは残る。

型引数付きの関連定義については、現在の `definition_ready()` が context 内で検査し、通常の `register_definition()` には登録せず `checked_templates` に記録している。この経路を kernel の検査済みテンプレート API にまとめる。

- テンプレートは body・classifier・context・certificate を持ち、既存と同じ検査を kernel 内で行う。
- 成功時だけ opaque な検査済み handle を返す。front が任意の ID を「検査済み」として登録できる API にはしない。
- context を持つテンプレートを、閉じた名前付き `Constant` として公開しない。型引数適用の lowering は現行の処理を維持する。
- 保存先は同一 kernel 環境の寿命に合わせる。別 arena の handle や、再登録された別の宣言に検査結果を流用しない。

具体的なインスタンスは引き続き `register_definition`・`register_inductive`・`register_datatype` の検査を通す。source の検査成功だけを理由に、インスタンス側の型検査・positivity・certificate 検査を省略しない。

## マクロ・関連項・表示

[macros.rs](../src/front/src/macros.rs) の `materialize_macros()` は、現在スコープ全体を clone し、`Resolved` な module ID と `ResolvedExp` を置換している。これを元のマクロとビューの組にする。マクロ本体の変換はそのマクロを選択・展開する際に行い、結果をキャッシュする。

マクロの宣言順・`use` の範囲・定義位置での名前解決は元のスコープから取得する。呼び出し位置の同名の項へ結び直さない。`LocalAccess::Resolved` の仮想 module ID も同じビューの lookup で解決する。

record の射影や型関連項は、元の所有型と関連定義のスロットから解決する。`record_for_inductive()` のために全モジュールを実体化して探索しない。名前一覧・エラー表示・origin 表示はメタデータだけを使い、表示しただけで本体を force しない。

## 実装順序

1. **互換性と計測の足場。** generativity、親の共有、内部 import、局所引数の既存テストを基準にし、実体化した項数・代入したノード数・検査数を数えられるようにする。
2. **ビューと安定 ID。** 元の宣言と仮想名前空間を分け、名前解決・origin・record/関連項の逆引きを変更する。この段階では比較用に新ビューを全 force してよい。
3. **項単位の resolver。** 代入・依存先の準備・検査・キャッシュ・失敗処理を一か所に移す。raw の推論・評価・反映から利用し、Program と鏡像の組を扱う。
4. **全件走査の除去。** インスタンス生成時の `PendingItem` 全件生成と、最終 lowering の仮想項全件列挙を止める。元の宣言の全検査と、要求した項の kernel 検査を維持する。kernel のテンプレート検査を永続化する。
5. **内部 instance とマクロの遅延化。** provenance に沿った派生ビューとマクロの展開時変換を完成させる。大きな import 木でも未使用の枝をたどらないことを確認する。
6. **比較して移行完了。** テスト用の全 force 経路と比較し、後述の性能ケースを計測する。旧 `PendingItem`・全体 remapping・一括マクロ複製を削除し、kernel README とモジュールの実装説明を更新する。

各段階で意味論を保ち、4 と 5 の完了を初版の lazy instantiation の到達点とする。

## 検証と受け入れ条件

### 意味論・健全性

- 同じ引数の二つの instance の帰納型は交換できず、同じ alias の二回の参照は同じ型になる。参照順を逆にしてもこの関係は変わらない。
- `P.Child(...)` の二つの child は別の型を持ち、どちらからも親 `P` の型を共有する。親の未使用項は実体化されない。
- 同じ source から作った二つの内部 import を区別する。外側の再インスタンス化・三段以上の内部 import・匿名 instance にも外側の引数が届く。
- `nested_instance_materializes_parent_dependencies` の局所引数、binder の下での代入、呼び出し側由来の帰納型を含む引数を確認する。
- 関連定義、record の射影、Program datatype と Set 鏡像、証明付き再帰と Box を確認する。型や certificate のみに現れる依存先も準備される。
- 未使用の不正な元宣言、未使用 import の引数誤り、未解決 metavariable、前方参照を従来どおり拒否する。
- 循環依存は通常エラーになり、帰納型の自己参照は検査できる。検査失敗後に再参照しても未検査の値や鏡像が現れない。
- `tests/ok/macros/definition_scope_hygiene.ref`・`module_visibility.ref` と、後続マクロを参照できない異常系を維持する。
- テスト用の全 force 経路と lazy 経路で受理・拒否、型、評価結果を比較する。ID の数値は対応表で比較し、generativity による非同一性も別途検査する。

既存の module manager の単体テストには複製先の `items()` を直接読むものがあるため、表現の検査を resolver 経由に変える。意味論の assertion は維持する。最終的に `cargo test --workspace` を通す。

### 性能

大きな source の構築・全検査を済ませた状態から、インスタンス作成と参照のコストを分けて計測する。別に end-to-end も測り、元の宣言の全検査にかかるコストを隠さない。

| ケース | 期待する観測 |
| --- | --- |
| N 個の独立した定義を持つモジュールを K 回 import し、何も使わない | 引数の検査に必要なものを除き、派生した定義本体の実体化は 0。項数 N に比例するインスタンスごとのコピーをしない |
| 各 instance で一つの独立した定義だけ使う | 実体化は K 個とその必要依存先に限定される |
| 一つの定義が長い依存鎖を持つ | その鎖だけを各 instance につき一度準備し、stack overflow を起こさない |
| 同じ項を繰り返し参照する | 二回目以降に代入・宣言の再検査を繰り返さない |
| すべての項を使う | lazy の管理コストを測る。高速化するとは仮定しない |
| 大きな親・内部 import 木・マクロ群の一部だけ使う | 未使用の本体・内部ビュー・マクロ本体を一括複製しない |

元の宣言の総サイズを S、引数検査等のコストを A、実際に実体化する各宣言のサイズの総和を D とすると、狙いは全複製による概ね `K × S` の仕事を、元の検査 `S` と `A + D` に近づけること。ただし依存型の変換可能性検査や正規化の計算量まで線形と主張するものではない。

[既存のベンチマーク](../src/cli/benches/README.md) にケースを追加し、`check/library` と `pipeline/library` も比較する。壁時計時間だけでなく、raw/kernel の割り当て数・実体化数・検査数・ビューの保持量も測る。実装前後は同一入力とビルド条件で比較する。

## 次の最適化と今回採用しない案

**kernel 内でのインスタンス実体化**は次の候補とする。検査済みの indexed な元宣言と、kernel が検査した代入・名前空間対応を登録し、要求された宣言だけ kernel 内で変換すれば、インスタンスごとの raw → indexed の再分類を削減できる。ただし局所 context、型引数付き関連定義、Program の反映パラメータ、検査中の帰納型の扱いをそろえる必要がある。まず上の計測で再 lowering が残る主要コストかを確認する。

**型だけ実体化して本体は unfold 時に変換する方式**は、さらにその次の段階とする。元の宣言と検査済み代入から型の正しさを再利用する kernel の規則が必要であり、未検査の本体を型だけで信用させる変更にはしない。現行の本体・反映証明の検査を保ったまま getter を二つに分けるだけでは、最初の検査が結局本体を要求する。

モジュール全体を最初のアクセスまで遅らせるだけの方式は変更が小さいが、一項を使うと全体をコピーするため今回は採用しない。全式に suspension を加える方式も初版には含めない。インスタンスの同一性を引数で共有する applicative な仕様への変更は、本案とは独立した言語仕様の検討事項とする。
