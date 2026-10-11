# package 単位の独立した検査成果物とキャッシュ

## 到達点

検証済み package を、依存成果物への参照と自身の定義からなる独立した成果物として保存する。
別の利用側、依存 package の訪問順、無関係な package の追加によって、同じ成果物の再検査や再保存が発生しない構成にする。
検査結果の参照、後続 package の検査、実行途中からの再開をそれぞれ独立した保存・読み込み経路にする。
ディスクとメモリの保持量を管理し、キャッシュを継続利用できる状態まで実装する。

この文書は採用する設計と、その実装を最後まで進めるための一つのプランである。
各段階は中間検査点であり、完了条件を満たした時点を実装完了とする。

## 現状と変更理由

[sema の package 処理](../../src/sema/src/packages.rs)は、依存順の prefix をキーにし、それまでの検査結果と環境を package 境界ごとに保存する。
[PackageChecker](../../src/elaboration/src/package.rs)の保存対象は、累積した `resolve::Session` と `GlobalEnvironment` である。
例えば A を共通依存とする B と C でも、訪問順によっては C の成果物に A と B の環境が含まれる。
このため、保存量と無効化範囲が依存グラフ以上に広がる。

`.pkg` は未圧縮の検査結果 JSON と圧縮済み環境を連結する。
検査結果は module ごとの `.json` にも保存し、結果だけが必要な場合も `.pkg` 全体を読み込む。
2026-10-11 の作業ツリーでは、`refcache/` 配下の `.pkg` 1,326 個が約27.2 GiBを占め、結果 JSON が約12.9 GiB、圧縮済み環境が約14.3 GiBだった。
これは過去の実行分を含む集計であり、単一検査の保存量とは区別する。

[永続化](../../src/sema/src/cache.rs)にはチェックサム、サイズ検査、一時ファイルからの置換がある。
これらを土台に、成果物単位の公開と参照関係に基づく回収を導入する。
[実装 fingerprint](../../src/sema/build.rs)と、現在の [semantic API](../../src/sema/README.md)も新しい単位に合わせて更新する。

## 1. package グラフと成果物の identity

`project` に、package 自身のソース集合、manifest、依存名と依存先、正規化した package identity を明示的に保持するグラフを用意する。
manifest から到達する依存グラフを再利用判定の基礎にし、検査の訪問順とは分離する。
直接依存は宣言されたものを保守的にすべてキーへ含め、名前解決や macro 展開によって初めて現れる利用も覆う。
package 内の参照先選択と部分検査には、既存の module 依存解析を利用する。
循環依存や依存名の衝突は、成果物の読み込みに先立って診断する。

次の identity を区別する。

| identity | 意味 |
| --- | --- |
| `PackageInstanceId` | snapshot 内で同じ package を指すための identity。path dependency は正規化した root を基礎にする。 |
| `PackageInputKey` | 処理系、設定、package identity、自身の入力、名前付き直接依存の入力キーから計算する。 |
| `ArtifactKey` | package の入力キーと、正規化した検査範囲から計算する。 |
| `ObjectDigest` | 保存する個別オブジェクトの内容から計算する。 |

キーは型付きの構造を決定的にエンコードして計算し、可変長項目に長さと種別を持たせる。
ソースは package 相対パスと内容の digest、manifest は検査に影響する設定と依存名の対応を含める。
依存一覧と検査範囲は正規順序にそろえる。
親の成果物は、自身の検査で必要だった依存成果物のキーと検査範囲を manifest に記録する。
依存の部分成果物と全体成果物の参照には、同じ入力と対象範囲を確認する規則を設ける。

同じ package が diamond dependency の複数経路から現れる場合は、一つの instance として扱う。
別の root にある同内容の package は独立した instance とし、nominal な型 identity を保持する。
object の内容共有と、言語上の package identity は別々に管理する。
入口 package や利用側の絶対パスは、依存 package の成果物キーから独立させる。
保存する source location は package と相対パスに分け、API へ返す際に現在の snapshot の絶対パスへ戻す。

処理系 fingerprint は実行時の意味と保存形式に影響する crate のソース、build script、依存解決、toolchain、target、feature・cfg・生成入力を追跡する。
テスト専用ファイルと examples は追跡対象から分離し、実装ソース変更時の保守的な無効化は維持する。
同じソースファイルに埋め込まれたテストの分離が必要な箇所は、ファイル構成を整理する。

## 2. 保存用 ID と実行時 ID の分離

保存形式には、所有 package、対象テーブルの種別、package 内の local ID を持つ参照を導入する。
外部参照は依存表の slot と依存 package 内の local ID で表す。
実行時には既存の整数 ID と arena を活用し、読み込み時に保存用 ID から現在の環境の ID へ対応付ける。
この対応付けを resolver、raw、kernel それぞれの明示的な import/export API に集約する。

| 層 | 対象 |
| --- | --- |
| resolver | `ModuleId`、`BindingId`、scope、import、macro の定義環境と hygiene identity、structure 展開、parameter と置換。 |
| raw | module・宣言・parameter の ID、symbol、namespace、remapping、具体化した宣言、引数列と共有する表。 |
| kernel | expression arena、`DefinitionId`、`InductiveId`、`ProgramInductiveId`、`ParameterId`、reflection の対応。 |
| analysis | 宣言参照、source location、型表示、診断、query 出力とその順序。 |

現在の kernel `DefinitionId` は arena identity を含み、raw の inductive と parameter は module 番号から kernel ID を組み立てる。
独立に作成した成果物の同じ数値を読み込んでも、別の型や定義が混同されないように、すべての対応を新しい import API で確定する。
式のノード番号、namespace の合成表、遅延具体化の捕捉、macro の内部参照まで同じ対応表を通す。
型名の一致による統合は、nominal identity の判定と分離する。
束縛変数の index と局所文脈は各式の構造として保持し、大域 ID の再配置とは区別する。

保存用 local ID は package 自身の宣言順と決定的なグラフ走査から割り当てる。
同名 module の複数出現と synthetic な module は、元の宣言位置と生成位置で区別する。
部分検査と全体検査で共有する宣言は同じ export identity を持ち、必要に応じて成果物内の圧縮したテーブル番号へ別途対応付ける。
hash map の列挙順、実行時の割当番号、別 package の読み込み順から保存内容を独立させる。

import は ID の予約、内容の再配置、参照と不変条件の検証、環境への公開という順に行う。
相互参照を含む宣言群も、この二段階の構築で復元する。
失敗時は仮の環境を破棄し、利用中の環境は成功した import 単位で更新する。
依存は読み込み済みの `(PackageInstanceId, PackageInputKey)` の表で共有し、diamond の共通依存を一度だけ登録する。
同じ instance の異なる入力版を一つの検査環境へ持ち込む要求は、不整合として扱う。

## 3. package が所有するデータだけを export する

各環境の宣言と保持するノードに所有 package を追跡できる情報を持たせる。
成果物の根は、その package の検証済み宣言、利用側の名前解決に必要な scope・macro・structure 情報、型検査と簡約に必要な定義群とする。
根から到達する自身のノードを保存し、依存 package が所有する定義は外部参照として保存する。
簡約に使う定義本体、帰納型と Program datatype、reflection、module parameter、namespace の対応を含める。

依存への具体化によって利用側の検査中に生まれた宣言や式は、その利用側が所有する。
読み込んだ依存成果物を immutable な入力とし、具体化、置換、メモ化による追加データは現在の package の層へ置く。
依存の本体が必要な場面は外部参照を解決し、共有する元の定義と具体化結果の所有を区別する。
既存の shared map、引数列、式 arena の共有は、到達グラフを一度走査する保存形式で維持する。
推論・簡約・lookup の再構築可能なメモ表は読み込み後に再生成する。
検証済み成果物の export 境界では、未解決の metavariable と未完了の宣言が到達グラフに残っていないことを確認する。

`PackageChecker` は、読み込んだ依存成果物と現在検査する package を明示的に分ける。
完了時には現在の package の結果と export データを返す。
独立した package の処理が終わった環境は解放でき、後続は自身の依存閉包だけを import する。
単一の live 環境を使い回す最適化を設ける場合も、可視な名前と export の所有範囲を package グラフで制限する。

## 4. 保存形式と読み込み経路

成果物は小さな manifest と、内容の digest で指定する immutable な object に分ける。
検査結果、resolver export、raw/kernel export を別々の object とし、独立して読み込み・検証・展開できるようにする。
raw と kernel が共有する式ノードは一つの export 表で扱う。
object は用途別の version、codec、格納長、展開長、checksum を持ち、展開時のサイズとテーブル要素数を検査する。
既存の postcard とストリーミング圧縮を活用し、native と WebAssembly の codec をヘッダーで識別する。
結果データにも圧縮した構造化形式を用い、manifest から module ごとの結果 object を参照する。

```text
refcache/
  v2/
    artifacts/<key-prefix>/<artifact-key>.manifest
    objects/<digest-prefix>/<object-digest>
    checkpoints/<session-key>/<coverage-key>.checkpoint
    leases/<session-id>
    access/
    tmp/
```

結果だけが必要な無変更検査では、入力と検査範囲を照合した manifest と結果 object だけを読む。
型検査を続ける場合に、必要な依存閉包の resolver と raw/kernel object を読む。
破損した環境 object があっても、独立に検証できる結果 object は結果照会に利用できる。
後続の検査に必要な object が欠損・破損している場合は、その package から再構築する。
object の checksum はローカル保存データの整合性を保証し、検証済みという信頼の単位は現在と同じローカルキャッシュとする。

writer は object を一時ファイルへ書き、検証・同期・公開を済ませてから、全参照を持つ manifest を原子的に公開する。
同じキーへの競合書き込みは、既存の正常な object の再利用として解決する。
結果の正しさとキャッシュ保存の成功は分離し、保存失敗は理由と統計を報告する。
サイズ上限を超えた環境は、その package の結果 object と独立に扱う。
manifest には環境の有無を記録し、後続検査で必要な再構築へ進める。

## 5. 部分検査と途中再開

manifest に検証済みの module・宣言範囲とその依存閉包を記録する。
完全な成果物は含まれる部分範囲へ利用でき、部分成果物は要求範囲を覆う場合に利用する。
複数の部分成果物を組み合わせるときは、同じ入力版と export identity を確認し、重複する宣言は同じものとして登録する。
package 全体の結果は、すべての要求範囲が検証済みになった時点で確定する。
独立した scope のエラー回復、未完了の結果、query 出力の重複排除も現行 API と照合する。

途中再開は `ResumeCheckpoint` として、検証済み成果物とは別に保存する。
checkpoint は依存成果物の参照と現在の package の作業状態、解決済みの検査順、次の位置を持つ。
package 間の累積 prefix に代わり、現在の package 内の途中状態を再開する。
未確定の metavariable、失敗の境界、source identity、復元後に再生成するメモ表を明示的に分類する。
保存境界は現在の source module 完了境界を引き継ぎ、既定30秒と保存コストに応じた間隔調整を維持する。
同じ再開キーの checkpoint を置き換え、成果物の公開成功後に対応する checkpoint を回収する。
依存入力、設定、検査範囲が異なる場合は、対応する成果物から新たに検査する。

単独 package 内の編集では、module 依存による結果の再利用と、一致する package 内 checkpoint からの再開を維持する。
無関係な package による ID の変化を取り除き、必要な再検査範囲を module の依存関係と現在の package 内の検査状態に限定する。

## 6. ソースの確認と実行オプション

通常検査と `--full-check-local` は、現在の snapshot に含まれるすべての到達可能な path dependency の入力を確認する。
`--full-check-local` は入口 package の再検査を強制し、依存は現在の内容が一致する成果物を利用する意味にそろえる。
推移的な依存の編集も入力キーを通じて利用側へ伝播する。
ソースの取得と内容 digest の保持は独立した source cache に集約し、保存済み snapshot は内容一致を確認した入力の復元に使う。
mtime とサイズは読み込み候補の判定に利用できるが、通常の新規プロセスでは内容を確認する。
LSP は未保存 buffer を含む immutable snapshot から同じキーを計算する。

`--full-check` は今回の検査で生成する成果物を使って全要求範囲を再検査し、成功した成果物を通常の保存先へ公開する。
`--no-cache` は実行をまたぐ永続再利用を省き、分割 worker 間で必要な成果物は実行専用の保存先に保持する。
`--trace` と統計収集は要求された検査を実行し、診断の詳細度と出力の扱いを明示する。
`--cache-dir` と入力ディレクトリの既定 `refcache/` は維持し、同じ保存先を使う利用側の間で依存成果物を共有する。

CLI supervisor の snapshot 固定、検査中のソース変更検出、時間・メモリ制限による batch 分割を新形式へ接続する。
現在の `Workspace::publish` のファイル列挙を、object の公開後に manifest を公開する store API に置き換える。
分割 worker は同じ session lease を使い、別プロセスで作成した部分成果物と checkpoint を利用する。
LSP と playground も同じ成果物モデルを使い、ディスク機能を持たない環境ではメモリ store を使う。

## 7. 容量管理と観測

ディスク容量の既定 budget は8 GiBとし、CLI・API から変更可能にする。
公開後の総量が budget を超えたら、現在利用中の成果物を保護したうえで、古い利用世代から manifest と checkpoint を回収する。
残る manifest・checkpoint が参照する object を mark し、共有 object は最後の参照がなくなった時点で回収する。
旧形式の既知のキャッシュファイル、古い checker 世代、公開されなかった一時 object も回収対象として扱う。
サイズ超過した有効データを保持する必要がある間は、一時的な budget 超過として容量と理由を表示する。

session lease は現在読む成果物と依存閉包を保護する。
manifest の取得と pin、公開、回収は短い store lock の中で調停し、直列化と型検査は lock の外で行う。
終了済み session の lease と一時ファイルは、生存確認と猶予期間を経て回収する。
並行 reader・writer・GC と異常終了を含めて、公開済み成果物の可読性を検証する。

メモリは圧縮済み object の保持量に加え、parse・query・module result の各 cache に budget または世代管理を設ける。
live な検査環境と呼出側が保持する `Arc` は、cache が解放できる保持量と区別して報告する。
利用後に依存閉包を解放できるようにし、LSP の連続編集で不要な過去版が蓄積する経路を整理する。

`--cache-stats` は、結果 hit、環境 import、checkpoint 再開、入力不一致、形式不一致、破損、欠損、サイズ上限、保存失敗を区別する。
結果と環境それぞれの読込・書込 byte 数、圧縮・展開・再配置時間、共有 object 数、回収 byte 数を計測する。
性能分析用の機能は通常のデバッグにも利用できる形で残す。

## 8. 実装順序

1. `benchmarks/` に再現可能な cache 計測を追加し、現在の実装の cold・warm・編集・別利用側・中断再開の基準値を採る。
   `project` の package グラフと入力キーを整備し、無関係な依存の訪問順からキーを分離する。
2. resolver・raw・kernel の保存対象と ID の対応を型として定義し、各層に export/import API を実装する。
   単独 package の往復、独立した二つの成果物の結合、diamond dependency、nominal identity を先に通す。
3. package の所有権と immutable な依存層を導入し、`PackageChecker` を依存閉包と現在の package に分ける。
   macro、structure、module parameter、Program と reflection を含む成果物を、別の環境へ import して後続を検査する。
4. manifest と object store、結果だけを読む経路、範囲別の成果物を実装し、`Database` の通常検査を切り替える。
   package 内の module 増分検査とエラー回復をこの経路へ統合する。
5. 現在の package の `ResumeCheckpoint`、部分成果物の組合せ、CLI supervisor の公開・分割処理を実装する。
   `--full-check-local` の入力確認、LSP の buffer、playground のメモリ store を接続する。
6. lease と GC、メモリの保持管理、容量設定、統計と failure reason を整備する。
   旧形式は cache miss として再構築し、既知の旧ファイルを回収対象として認識する。
   置換された累積 `.pkg`、module `.json`、`.env`、`.sources.json` の経路を整理し、新しい一組のモデルに統一する。
7. 意味の一致と性能を検証し、`src/sema/README.md`、`src/project/README.md`、`src/resolve/README.md`、CLI 利用説明と実装説明を更新する。
   計測結果と残る制約を記録し、以下の完了条件をすべて確認する。

## 9. 検証と完了条件

### 意味と identity

- cold 検査、成果物からの検査、途中再開で、成功・失敗、診断位置、型、参照先、query 出力が一致する。
- 別プロセスで生成した A と B を、無関係な package を含む環境へ訪問順を変えて import できる。
- diamond の共通依存は同じ nominal identity を保ち、独立した同内容の package は別の nominal identity を保つ。
- macro の hygiene、同名 module、structure の synthetic module、module parameter、具体化、Program datatype と reflection を含む後続検査が cold 検査と一致する。
- 直接・推移的依存の編集、manifest 変更、ソース追加・削除、module 構成変更、LSP の未保存編集に応じて必要な利用側が再検査される。
- 部分検査を順番を変えて組み合わせても、範囲外の未完了 module は未完了として残り、既に検証した範囲を正しく共有できる。

### 保存と障害回復

- package の環境 object に依存 package の定義本体が重複して格納されず、外部参照として表現される。
- 結果だけの warm 検査では、環境 object の読込 byte 数と展開回数がともにゼロになる。
- source・検査範囲・設定が同じ成果物は、別プロセスでも同じキーと決定的な保存内容になる。
- checksum 不一致、途中までの書き込み、参照 object の欠損、ID の範囲外、展開上限、書込失敗から、正常な再計算または説明可能な保存省略へ進む。
- object 公開と manifest 公開の間の中断、同じキーへの並行書込、GC と reader の競合、worker 強制終了から復帰できる。
- package 完了前の複数の境界で停止・再開し、完了した依存の再検査と累積環境の再保存を省ける。
- 小さい budget のテストで回収を発生させ、共有 object と利用中の成果物が保持され、終了後に回収可能になる。

### 実プロジェクトと性能

`benchmarks/` の小さい chain・diamond・独立 package の fixture で、依存数を増やした場合の保存量と無効化範囲を確認する。
固定サイズの各 package からなる chain では、環境 payload の総量が各 package 自身のデータと外部参照の合計に沿って増えることを確認する。
依存本体の累積コピーを構造検査でも確認し、圧縮率だけに依存した評価を避ける。

`libs/std` と、複数の共通依存を持つ `libs/algebra/homological/computations`、`libs/geometry/differential_forms` を実データの代表にする。
各計測は専用の保存先で、cold、warm、入口編集、依存編集、別利用側、途中再開を区別する。
wall time、peak RSS、保存総量、読込・書込量、検査した module 数、再配置時間を報告する。
既存の蓄積済み30 GiBと新規生成量を比較する代わりに、同じ入力と実行列で旧設計と新設計を比較する。
大きなキャッシュや profiler の生データは計測時の作業領域に置き、リポジトリにはスクリプトと小さい集計結果を保存する。

影響する crate のテスト、CLI の既存統合テスト、LSP・playground の対応 target のビルドを実行する。
ライブラリ検査は通常のキャッシュ付き検査を使い、cold との比較は専用の計測ケースで行う。
cold の検査時間と peak RSS は基準比10%を調査開始の目安とし、反復計測で回帰が再現する場合は原因と改善を確認する。
warm と別利用側の再利用では、環境を読む必要がない経路と依存を再検査しない経路が実測でも成立することを必須にする。

成果物の独立性、入力変更の検出、部分検査と再開、容量管理、利用側の移行、実データでの検証が揃った時点で完了とする。

## 実装結果

2026-10-12に各段階の実装と検証を完了した。
packageごとの独立成果物、結果と環境の分離、部分成果物と再開、容量・保持量の管理、CLI・LSP・playgroundへの接続を実装した。
実プロジェクトのcold・warmとCLI統合テストを含む検証結果は[計測記録](../../benchmarks/cache-artifacts.md)にまとめた。
無変更検査では実プロジェクトでも環境読込量とimport回数が0になった。
標準ライブラリの保存量は約69%減った一方、coldの処理時間・peak RSSには回帰が残り、大きいresolver成果物では要素数上限による環境保存省略が発生する。
原因調査と改善内容、数値と測定条件を計測記録に残した。
