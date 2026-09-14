# front の整理と性能比較

front の Rust コードを **31,090 行から 30,141 行へ、949 行削減**した。
追加した共通処理も含む `src/front/src/**/*.rs` の物理行数で比較している。

- 論理構文の lowering は 1,731 行から 819 行へ削減した。適用・product・lambda・
  帰納型には既存の `kernel::construction` を使い、その他の構文は family ごとの
  ノード確保を小さなマクロに集約した。フィールドの型は引き続き Rust が検査する。
- 単一の型引数の代入は、既存の複数引数の代入処理を使う形にまとめた。
  kernel 側の変更は構築関数の公開と説明の追加であり、独立した型検査は維持している。

型の反映処理からは、使用されていなかった巡回検出用の集合と中継関数を削除した。
定義を辿る値・計算の反映では、従来の巡回検出を使う。

恒等関数の適用 `(λx. x) a` は、構文走査と添字調整が不要なので直接 `a` を返す。
正規化の単体比較で残っていた遅れを抑えるための小さな簡約である。

## 全ケースの結果

単位は ms。変化率が負なら高速化。CV はサンプル間のばらつきの目安。

| ケース | 変更前 | 変更後 | 変化率 | CV 前 / 後 (%) |
| --- | ---: | ---: | ---: | ---: |
| parse/mccarthy91 | 0.084373 | 0.085272 | +1.07% | 3.91 / 14.74 |
| load/library | 6.068405 | 5.700197 | -6.07% | 8.32 / 6.45 |
| check/library | 2475.756058 | 2383.888397 | -3.71% | 7.23 / 10.01 |
| pipeline/library | 2345.783833 | 2297.769970 | -2.05% | 5.36 / 6.49 |
| pipeline/mccarthy91 | 44.477513 | 43.339204 | -2.56% | 9.76 / 3.92 |
| instantiate/128x16-unused | 1.469698 | 1.512482 | +2.91% | 4.18 / 4.29 |
| instantiate/128x16-one-each | 1.528730 | 1.543789 | +0.99% | 4.55 / 6.14 |
| normalize/beta256 | 0.005952 | 0.005940 | -0.21% | 5.30 / 3.96 |
| kernel/closure64x128 | 0.005177 | 0.005461 | +5.47% | 4.02 / 7.22 |
| evaluate/countdown32 | 0.184680 | 0.185185 | +0.27% | 6.19 / 6.48 |
| evaluate/countdown128 | 2.468231 | 2.474286 | +0.25% | 2.87 / 12.64 |

ライブラリ型検査は **2.476 秒 → 2.384 秒（-3.71%）**、読み込みを含む全工程は
**2.346 秒 → 2.298 秒（-2.05%）**だった。正規化は -0.21%、評価は +0.27% / +0.25%
でほぼ同等だった。主要な検査・評価で性能退行は見られなかった。

小さいケースでは、実体化が +2.91% / +0.99%、独立した kernel 閉性判定が +5.47%
（5.177 µs → 5.461 µs）だった。これらは CV と実行間の変動も併記して判断する。
測定値はこのマシンと入力での結果であり、有意差検定は行っていない。

集計は [summary.tsv](summary.tsv)、生サンプルは [before-1.tsv](before-1.tsv)、
[after-1.tsv](after-1.tsv)、[after-2.tsv](after-2.tsv)、[before-2.tsv](before-2.tsv) に保存した。
全 440 サンプルの正常終了印、CPU 固定、反復回数と所要時間を確認し、中央値と CV を
別途再計算した。測定した実装と作業ツリーの一致、入力・実行ファイルの SHA-256 も検証済み。

## 条件と再実行

- 比較元: `ab4a67c0c4ec1a73eb80d942ac3a300c0ba5ccfd`
- 比較先: このリファクタリングを適用した作業ツリー
- CPU: Intel Core i5-12400、Linux CPU 0 に固定
- OS: WSL2 Linux `6.18.33.2-microsoft-standard-WSL2`、x86_64
- Rust: `1.98.1 (48a229cea 2026-09-01)`、LLVM 22.1.8
- Cargo: 最適化した bench profile、`--locked --offline`、変更前後で別のビルド先
- 順序: before-1 → after-1 → after-2 → before-2
- 各実行: ウォームアップ 1,000 ms 以上、10 サンプル、サンプル実時間 200 ms 以上
- 集計: 各ケース・各実装につき計 20 サンプル、全 440 サンプル

リポジトリのルートで実行する。Python 3.12 以上が必要。

```sh
python3 scripts/bench_compare.py ab4a67c --offline --rounds 2 --samples 10 --warmup-ms 1000 --sample-ms 200
```

今回は先に正規化ケースを比較して両方の実行ファイルを作り、その同じ実行ファイルで
全ケースを再実行した。ソース snapshot・入力・実行ファイル・ビルド時の記録は
`target/benchmarks/front-refactor-beta/`、全ケースの実行記録は
`target/benchmarks/front-refactor-final-results/` に保持している。
同じマシンで保存した実行ファイルを再実行する場合は、保存先を新しい名前にして次を使う。

```sh
python3 src/cli/benches/results/front-refactor-2026-09-14/replay.py target/benchmarks/front-refactor-beta target/benchmarks/front-refactor-replay --filter '' --rounds 2 --samples 10
```

`replay.py` は保存したソース・入力・実行ファイルの SHA-256 を検証してから、
元と同じ CPU に固定して測定する。実行ファイルには snapshot の絶対パスが
埋め込まれるため、元の保存先は移動しない。
toolchain、CPU、入力、実行ファイルの詳細は [experiment.json](experiment.json) を参照。

## 性能比較で取り下げた変更

定義の型引数の代入や ID 置換まで汎用走査へ置き換える案も試したが、短いケースに
遅れが出た。ウォームアップと測定時間を増やし、ケースを絞った比較でも、
型引数の汎用代入を含む版は `evaluate/countdown128` が +7.44%、
ID 置換の共通化を残した版は実体化が +6.63% / +6.89%、正規化が +10.78% だった。
このため、これらの専用走査を維持し、構文構築と代入の入口の重複を削る変更を採用した。

各試行の集計と元データの保存先は [iterations.tsv](iterations.tsv) に残した。
同ファイル内の `beta` と `final` が最終構成、それ以前は検討途中の案である。
これらの生サンプルと snapshot も記載した `target/benchmarks/` 配下に保持している。

## 検証

- `cargo test --workspace --locked --offline`: 161 テスト成功（doc-test を含む）。
  CLI の統合テストは 180 個の `.ref` 入力とライブラリ全体を検査する。
- `cargo clippy --workspace --all-targets --locked --offline -- -D warnings`: 成功。
- `cargo fmt --all -- --check`: 成功。
