# キャッシュなしのライブラリ検査

## 測定条件

2026-10-05、Linux x86_64、Rust 1.95.0、既存の dev profile（`opt-level = 2`、debug assertion と debug 情報あり）で測定した。
基準は category の高速化を統合済みの main `62285441fd9f895732494b9b81110f316bd25997` の処理系であり、比較する両方の版に整理後の同じ `libs/` を与える。
各ライブラリを新しい CLI プロセスで3回検査し、`--no-cache --diagnostics compact` を指定する。
検査中にビルドや別の計測を並行実行しない。
経過時間にはプロセスの起動から終了までを含め、Linux の `wait4` でプロセスごとの user/system CPU 時間と最大 RSS を採る。
ディスクの検証済み結果は読み書きせず、依存ライブラリも各プロセスで検査する。
OS のファイルキャッシュは消していない。

```sh
cargo build -p cli
python3 tests/bench_libraries.py --binary target/debug/cli --runs 3 --output /tmp/library-after.json
python3 tests/bench_libraries.py --binary /path/to/before-cli --runs 3 --output /tmp/library-before.json
REF_TYPE_PROFILE_PHASES=1 REF_TYPE_PROFILE_DECLARATIONS=1 REF_TYPE_PROFILE_MODULES=1 \
  target/debug/cli libs/category --no-cache --diagnostics compact --stats
```

計測スクリプトは CLI とライブラリソースの SHA-256、実行設定、個々の測定値、検査ログを保存する。
プロファイル用の環境変数は通常のベンチマークから除き、プロファイル実行は時間比較とは別に行う。

## 改善の内容

- lowering の共有キーから、各部分式の変換には使わない文脈の型列を除き、束縛の深さを使う。
  捕捉する parameter や nominal スコープの変更時には共有表を切り替え、Program の深さとモードも区別する。
  kernel の型検査は完全な検査文脈を引き続き使う。
- 型への同時代入を、項・引数列・入れ子の深さごとに共有する。
  同じ DAG の部分式を再利用し、全自由変数を覆う恒等代入は元の項を返す。
  引数の型検査と期待型との比較は従来の経路を通る。
- kernel に登録済みの不変な parameter・帰納型・Program datatype の依存関係は、bridge で再び具体化しない。
  個々の参照の実引数は走査し、初回登録と各使用箇所の型検査は維持する。
- module 引数の閉性は、式ごとに保持する自由変数情報から求める。
  共有 DAG を木として何度も走査する処理を既存の情報の利用に置き換えた。

代入結果は環境内だけで共有し、直列化しない。
定義登録の一時ノード回収に合わせて一時的な引数列 ID と関連する結果を破棄し、古い ID を使った再利用を防ぐ。
メタ変数への代入内容には依存せず、メタ変数を含む構文とその引数だけを変換する。
solver の状態変更・rollback・最終的な未解決メタ変数の検査は従来の経路を通る。
main の適用モード判定、構文属性の配列、文脈の接頭辞共有、段階別計測はそのまま利用する。

## 結果

各値は3回の中央値（最小〜最大）、RSS は3回で観測した最大値である。
合計は各巡の経過時間の和の中央値であり、各行の中央値の和とは一致しない場合がある。

| ライブラリ | main 秒 | 統合版 秒 | 短縮率 | 最大RSS 前→後 MiB |
| --- | ---: | ---: | ---: | ---: |
| `std` | 2.608（2.543〜2.646） | 2.469（2.430〜2.557） | 5.3% | 571.4 → 577.6 |
| `real` | 6.952（6.812〜7.318） | 6.580（6.511〜6.651） | 5.4% | 881.8 → 902.9 |
| `complex` | 8.107（7.873〜8.280） | 7.550（7.264〜7.574） | 6.9% | 948.2 → 957.1 |
| `linear_algebra` | 10.414（10.397〜10.477） | 9.541（9.277〜9.603） | 8.4% | 1075.4 → 1095.5 |
| `topology` | 11.247（11.098〜11.309） | 10.071（10.000〜10.389） | 10.5% | 1194.5 → 1211.9 |
| `calculus` | 7.456（7.371〜7.502） | 7.120（7.036〜7.134） | 4.5% | 930.7 → 951.8 |
| `integration` | 9.584（9.535〜9.755） | 8.697（8.695〜8.852） | 9.3% | 985.5 → 1002.4 |
| `category` | 9.753（9.738〜9.915） | 8.302（8.225〜8.912） | 14.9% | 716.0 → 754.3 |

合計は **66.099秒 → 60.618秒、8.3%短縮**した。
各巡の合計は main 66.649, 66.099, 65.945 秒、統合版 59.828, 60.618, 60.994 秒だった。
category は **9.753秒 → 8.302秒、14.9%短縮**し、既存の高速化を保った。
全24回の最終ライブラリ検査が成功した。
追加の共有表によってメモリは増え、全ライブラリ中の最大値は1194.5 MiBから1211.9 MiBとなった。
category 単体の最大値は716.0 MiBから754.3 MiBとなった。

[生データ](benchmarks/library-checks-2026-10-05.json)の `main_integration` に、この比較の user/system CPU 時間、最大RSS、終了コード、ソース・CLI の fingerprint、検証結果を保存している。
同じファイルの先行データは、旧ベース `643d3fa` に対する初期調査の記録であり、この表とは基準が異なる。
旧ベースでの合計中央値は88.044秒から75.803秒だった。

統合版の別実行による category のプロファイルは、問い合わせ全体8.376秒、検査 batch 6.784秒、名前解決1.091秒、category の最終 lowering 0.226秒だった。
`FunctorCategory.Restriction.functor` の登録を含む lowering は0.066秒だった。
各段階の時間は入れ子になっており、加算する値ではない。
main の改善によって最終 lowering の負荷は小さくなり、残る時間は主に依存先を含む検査 batch と名前解決にある。

## 初期調査での比較

旧ベースでの CPU サンプリングは文脈の intern、構文属性の参照、同時代入、型推論を改善候補として示した。
サンプリング値は候補の特定に使い、速度の比較には通常実行の経過時間を使った。
同一の文脈・項・期待型について完了済みの検査判断を共有する案は、当時の category が23.69秒から25.35秒となり、最大 RSS も約1252 MiBから1366 MiBに増えた。
一般の連続変数列への代入を既存のシフト表へ振り分ける案も、当時の20.45〜21.22秒に対して21.99秒となった。
この二つの案は最終実装には含まれない。
構文属性の配列も当初の単独実験では明確な差がなかったが、統合先の main では適用モード判定などとともに改善済みの実装を使う。

## 変更ファイルと検証

| ファイル | 変更 |
| --- | --- |
| `src/elaboration/src/lowering.rs`, `lowering/logical.rs`, `lowering/captures.rs` | 変換の共有キーとスコープ管理、文脈と reflection の回帰テスト |
| `src/elaboration/src/lowering/declarations.rs` | 既存の計測コードを rustfmt で整形 |
| `src/elaboration/src/kernel_bridge.rs` | 登録済み宣言の依存先の再走査を省く |
| `src/elaboration/src/raw/namespaces.rs`, `raw/tests.rs` | 引数の閉性判定と、大きい共有式・開いた Program 引数の回帰テスト |
| `src/kernel/src/calculus.rs`, `environment.rs`, `check.rs`, `tests.rs` | 同時代入の共有、回収との連携、恒等代入と引数・束縛・ID 再利用のテスト |
| `src/elaboration/README.md`, `src/kernel/README.md` | 共有の範囲と寿命を説明 |
| `tests/bench_libraries.py` | 新しいプロセスでの反復測定、時間と RSS、ソースと CLI の fingerprint |
| `doc/performance-library-checks.md`, `doc/benchmarks/library-checks-2026-10-05.json` | 測定条件・結果・生データ |

ライブラリ整理の責務・依存関係は [libs/README.md](../libs/README.md)、公開定理の移動先は [real/README.md](../libs/real/README.md#移動した公開定理) に記載した。

統合後の最終コードに対する `cargo test --workspace` は307件成功、失敗0件、無視0件だった。
今回の回帰テスト5件と main 側の回帰テストに加え、成功例95ファイルと失敗例129ファイル、ライブラリと圏論のプロジェクト例、キャッシュの復元・無効化、メタ変数の rollback、帰納型の positivity、診断の検査を含む。
`cargo fmt --all -- --check` と `git diff --check` も成功した。
計測後の最終整形では `Analysis/Distance.ref` と `std/README.md` の末尾空行を一つずつ削除し、全307テストと全8ライブラリ1巡を再検査して成功した。
その結果とソースの fingerprint は生データの `main_integration.final_validation` に保存している。
全8ライブラリのキャッシュなし検査と全テストで未実行のものはない。
