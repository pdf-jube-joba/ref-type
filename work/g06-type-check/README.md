# G06 型検査修復の記録

基点は main の `4640f66e357691eadaec5632aa07bd0eff643979`、修復ソースは `6c55189d9908022e04f88e22357c61f81539302b`。
checker はこの処理系ソースから Rust 1.100.0 で構築した。
`target/release/cli` の SHA-256 は `ffff71f26ce98f7558c99846cb544115200534504c50d5f9c838b0eb870afa64`。

`Compact.patchAt` の兄弟 module の参照を親から明示し、signature の import、部分集合型の点と等式、連続性の始域・値域、分岐の結論を明示した。
既存の逆写像則と部分集合の等式補題を使って証明を整理した。
定義の引数に依存する写像型は `InverseOn` 補助 module で構成した。
[`gaps.md`](../../gaps.md) に、スコープエラーを再現する6行と通過する補助 module 版10行を記録した。
既存定理の仮定・結論を保ち、追加公理は導入していない。
数学ライブラリの変更範囲は `libs/geometry/tubular_neighborhoods/src/`。
この修復の検査結果と、[G06 計画](../../_plans/math/g06-tubular-neighborhoods.md)に残る数学的な要件の完了判定は別である。

## 検査結果

| 検査 | 結果 | 検証済み / 対象 | 新規ソース検査 | 有効なキャッシュ再利用 |
| --- | --- | ---: | ---: | ---: |
| G06 と参照先の限定検査 | accepted | 1,202（G06 対象46/46） | 46 | 1,156 |
| G06 パッケージと全依存 | accepted | 8,831 / 8,831 | 2,922 | 5,909 |
| ライブラリ全体 | failed（別パッケージのエラー） | 11,499 / 15,746 | 2,765 | 8,734 |

各行はその実行内の集計で、行間では合算しない。
G06 自身の対象46モジュールは対象一覧と照合済みで、限定検査・依存閉包検査とも検査漏れは0。
全体検査では `grassmannian_cells` が先に失敗し、G06 のスコープには到達していない。
全体検査の未確認範囲は4,247モジュールで、失敗スコープ内の部分的な成功は全体の通過件数に加えていない。
3つの検査とも保存失敗・破損キャッシュの読み込みは0件。

全体の最初の阻害箇所は [`libs/geometry/grassmannian_cells/src/Symbols/FreeCount.ref:3:1`](../../libs/geometry/grassmannian_cells/src/Symbols/FreeCount.ref) の次の診断。
このパッケージは基点コミットから変更されていない。

```text
Resolution Error: child module 'FreeEnumeration' was not found
```

全依存の単一 CLI 実行は3,600秒の時間上限になり、同一入力での再実行はパッケージ別ドライバへ切り替えるため中断した。
それらは通過結果として数えていない。
後続の `scripts/check_all.py` による依存閉包検査は約926秒で全対象を通過し、全体検査は約1,430秒で上記エラーを報告した。

## 証跡と入力

件数・ハッシュ・ローカルの生ログの位置は [`evidence.json`](evidence.json) に記録した。
生の集計レポートは [限定検査](reports/target.json.gz)、[依存閉包](reports/package.json.gz)、[全体検査](reports/all.json.gz)。
各スコープの JSON レポートは [依存閉包](reports/package-scopes.tar.gz) と [全体検査](reports/all-scopes.tar.gz) に保存した。
全体検査の最初の失敗は [JSON レポート](reports/all-first-failure.json.gz) と [標準エラーログ](reports/all-first-failure.log.gz) を保存した。
ドライバの [標準出力](reports/all-driver.stdout.gz) と [標準エラー](reports/all-driver.stderr.gz) も保存した。
大きなソーススナップショットと作業中ログはローカルの `runs/` に保持している。

依存閉包のスナップショットは7,744ファイル、SHA-256 は `9873434fc7db5159686962501a57f3278a1710e084166b5ff14f736cc726291e`。
全体は14,295ファイル、SHA-256 は `ac428eacada610e2a4841af5c40f2ecdee4b2d1fd1c85cbd24ec60c3993422f0`。
すべての入力ファイルが追跡済みソースと一致し、checker のハッシュが同一であることを確認した。
ドライバはスナップショットを固定し、通過スコープの網羅性を確認する。
依存閉包の成功時は最後に入力と対象一覧を再列挙して一致を確認した。
通常の `libs/refcache` を使用した。
旧ソースの再開レポートは使用していない。

## コマンド

ビルドは `RUSTUP_HOME=/workspace/.ref-type-toolchain/rustup`、`CARGO_HOME=/workspace/.ref-type-toolchain/cargo` とし、`$CARGO_HOME/bin` を `PATH` に追加した環境で実行した。

```sh
cargo +1.100.0 build --locked --offline --release -p cli -j 4 > work/g06-type-check/build.stdout 2> work/g06-type-check/build.stderr

REF_TYPE_PROFILE_DECLARATIONS=1 target/release/cli libs/geometry/tubular_neighborhoods --module tubular_neighborhoods --memory-mib 12288 --time-limit-seconds 1800 --cache-stats --diagnostics compact --report-json work/g06-type-check/runs/target-33.json > work/g06-type-check/runs/target-33.stdout 2> work/g06-type-check/runs/target-33.stderr

python3 scripts/check_all.py libs/geometry/tubular_neighborhoods --binary target/release/cli --state-dir work/g06-type-check/runs/package-driver --memory-mib 12288 --cache-budget-mib 24576 --time-limit-seconds 7200 > work/g06-type-check/runs/package-driver.stdout 2> work/g06-type-check/runs/package-driver.stderr

python3 scripts/check_all.py libs --binary target/release/cli --state-dir work/g06-type-check/runs/all --memory-mib 12288 --cache-budget-mib 24576 --time-limit-seconds 7200 > work/g06-type-check/runs/all-driver.stdout 2> work/g06-type-check/runs/all-driver.stderr
```

全体検査の状態は `runs/all/20261120T073238.035585Z/report.json`、入力は同じディレクトリの `source.json`、スコープごとの結果は連番の JSON ファイルにある。
同一入力で通過済みスコープを引き継ぐ場合は、次のコマンドを使用できる。
これは現在の独立したエラーを再び報告する。
ソースまたは checker を修正した場合は `--resume-report` を付けずに新しく検査し、通常の有効なキャッシュを再利用する。

```sh
python3 scripts/check_all.py libs --binary target/release/cli --state-dir work/g06-type-check/runs/all --resume-report work/g06-type-check/runs/all/20261120T073238.035585Z/report.json --memory-mib 12288 --cache-budget-mib 24576 --time-limit-seconds 7200 > work/g06-type-check/runs/all-resume.stdout 2> work/g06-type-check/runs/all-resume.stderr
```

`git diff --check` は通過した。
