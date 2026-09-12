# モジュール実体化の管理コストとエラー処理を改善する

## 対象

定義・帰納型・Program datatype は、instance 側の ID を要求すると source の宣言を変換し、`OnceCell` に保持する。この項単位の実体化を前提に、instance 作成時のメタデータ確保、内部 instance の展開、失敗の伝播を改善する。

| 箇所 | 現在の処理 | 残る課題 |
| --- | --- | --- |
| `ModuleManager::instantiate_module_from` | 経路上の module と内部 instance を列挙し、全項の名前・ID・空スロット・origin を用意する | 未使用の項・内部 instance にも作成コストがかかる |
| `LazyDefinition` / `LazyInductive` / `LazyProgramInductive` | 宣言ごとに代入列と `InstanceRemapping` を所有する | 全体の対応表を宣言数分 clone する |
| `CrateEnv::resolve_definition` | 変換・検査が成功すると保存し、失敗は `String` としてキャッシュする | source の解決と検査中の依存先要求が再帰的になる |
| `definition` / `inductive` / `program_inductive` | `definition` は resolver のエラーを panic にし、帰納型の getter も実体化を直接行う | checker・reducer・lowering に通常のエラーとして返す経路が揃っていない |
| `record_for_inductive` | 全モジュールの項メタデータを探索する | 疎な名前空間に対応する逆引きが必要 |

参照: [module_manager.rs](../src/front/src/elaborator/module_manager.rs)、[raw/environment.rs](../src/front/src/raw/environment.rs)、[raw/dependencies.rs](../src/front/src/raw/dependencies.rs)、[lowering/declarations.rs](../src/front/src/lowering/declarations.rs)。

## 1. instance 作成と初回参照を分けて測る

[既存ベンチマーク](../src/cli/benches/performance.rs)の `instantiate/128x16-unused` と `instantiate/128x16-one-each` は、元モジュールを含む elaboration と、派生定義の実体化数 0／16 を確認する。

これを基準に、元宣言の検査を済ませてから instance 作成と参照を別々に測るケースを加える。元宣言を含む全体時間も継続して測る。

| 負荷 | 観測するもの |
| --- | --- |
| 宣言数 N・instance 数 K を変え、項を使わない | ID スロット・名前表・代入列・対応表・内部名前空間の確保量 |
| 各 instance の一項だけを使う | 必要依存先を含む実体化数、初回参照時間 |
| 同じ項を繰り返し使う | キャッシュ利用時の時間、変換・検査の回数 |
| 全項を使う | 管理処理の時間と保持量 |
| 深い内部 import と長い依存鎖 | 未使用の枝の確保量、再帰深度、必要な枝の実体化数 |
| 親の型・関連定義・Program datatype を使う | 親の共有、関連項と Set 鏡像の準備コスト |

`materialization_stats` に加え、名前空間数・予約スロット数・対応表の要素数とコピー量を診断実行で測る。未使用の派生定義本体の実体化数が 0 でも、メタデータ確保の費用は別に評価する。

## 2. 代入列と対応表を共有する

現在は全 ID の予約後に、同じ `remapping.clone()` を各 lazy 宣言へ設定する。まず対応表と代入列を不変な共有データにし、宣言には source ID と共有環境への参照を保持させる。

- 同じ instance 内の宣言で共有し、別の instance の generative な ID を混同しない。
- base instance から child を作る場合は、親の環境と child の追加分を共有する構成を比較する。
- マクロ scope が保持する対応表も同じ共有環境を参照できるようにする。
- binder の下での代入と反映引数の区別を保ち、呼び出し側から渡した引数の参照を別 instance へ付け替えない。
- 共有表の構築中は通常の lookup に公開せず、再帰的な解決・検査中に内部可変性の borrow を保持しない。

対応表のコピー量と保持量が減り、全項を使う場合にも lookup の管理費が過大にならないことを確認する。

## 3. 名前空間と宣言スロットを必要時に生成する

元モジュールの名前表・宣言メタデータを共有し、`(instance, source slot)` から参照先の ID を求める。全項分の `OnceCell` と lazy descriptor を事前に確保する処理を、要求された項の保存へ移す。

- 同じ項の lookup は参照順にかかわらず同じ ID を返し、別の instance は別の ID を持つ。
- slot は公開名だけでなく、型関連定義・record の射影・Program datatype の Set 鏡像を含めて区別する。
- origin は instance と source slot から求め、全定義分の逆引き表を作る費用を減らす。record の所有型から関連項を取得できる索引も整える。
- 名前一覧・origin・エラー表示では本体を要求しない。
- 宣言順と参照時の可視範囲を保存し、後から追加された名前を過去の参照に見せない。

内部 instance は `(outer instance, source internal instance)` をキーにした派生ビューとして必要時に作る。同じ source 由来の二つの内部 import を区別し、匿名 instance も扱う。外側を変えると内部の代入も変わるが、外側に属さない既存 instance は共有する。

`P.Child(...)` では既存の親 `P` を共有する。後続パラメータの検査で必要な親の宣言はその場で解決し、公開する child からも同じ親を参照する。

[front の性能計画](front-performance.md)にある宣言キューと合わせ、名前空間や ID を列挙しただけで未使用の本体を要求しないようにする。

## 4. 実体化エラーを resolver から伝播する

`resolve_definition` を checker・reducer・reflection・dependencies・lowering の宣言取得に使用し、帰納型と Program datatype にも失敗を返せる resolver を揃える。

- 実体化状態を未処理・処理中・成功・失敗で区別する。通常の循環依存はエラーにし、帰納型の自己参照は検査用の経路で扱う。
- 未検査の定義を成功として保存しない。帰納型の変換済み仕様と kernel の登録・検査成功も区別する。
- datatype と Set 鏡像は安定した両 ID を確保し、検査失敗時に片方だけを利用可能な検査済み宣言として扱わない。
- 評価側にも実体化失敗を返す経路を通す。失敗を展開不能な定数や `OutOfFuel` に変換しない。
- 失敗の再参照で同じ診断を返し、source 宣言と instance 作成位置を追える情報を保持する。
- 宣言登録・失敗時のキャッシュ更新を整理し、検査途中の結果を再利用しない。

`Lowerer::definition` の worklist は lowering の依存順を管理している。一方、raw resolver の source 解決と検査からの依存先要求は再帰を使うため、こちらも明示的な作業列に移して長い鎖を処理する。型注釈・certificate・Program 内部の Set 参照にある依存先も対象にする。

## 検証と採用条件

名前空間の変更には、同じ入力を必要な項だけ解決する経路と、テスト用に全項を解決する経路で比較する検証を用意する。数値 ID の割り当て順を対応表で吸収し、型の同一性と非同一性を別に検査する。

- 同じ alias の複数参照で型を共有し、同じ引数から作った別 instance の帰納型は交換できない。
- 親を共有する child、外側の再インスタンス化、三段以上の内部 import、匿名 instance の引数と参照が正しい。
- 局所変数を含む引数の context、binder の下の代入、呼び出し側の帰納型を含む引数を保つ。
- 関連定義・record・Program datatype と鏡像・証明付き再帰・Box の型と評価結果を保つ。
- 不正な未使用元宣言、未使用 import の引数誤り、前方参照、循環依存を拒否する。
- 失敗後の再参照が panic せず、未検査の定義や鏡像を公開しない。
- マクロの定義位置での名前解決、宣言順と可視性を保つ。

各段階で `cargo test --workspace` を実行する。性能変更は対象ケースの時間・割り当て量・保持量と `check/library`・`pipeline/library` を比較し、元宣言と具体的な instance 宣言の kernel 検査を維持したうえで採用する。
