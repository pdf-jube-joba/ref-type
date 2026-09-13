# 閉性判定のキャッシュ再利用による高速化

`kernel::calculus::locally_closed` の独立した走査を削除し、shift・substitution が
使っている `Arena::max_loose_bound` の解析結果を再利用した。
ノードは不変なので、共有された定義を別の場所から使う際も解析結果を利用できる。
束縛の深さ、型注釈、Program の証明を含む既存の走査規則は共通のままである。

ライブラリ型検査の中央値は **5.508 秒から 2.562 秒（53.48% 短縮、約 2.15 倍の速度）**、
読み込みを含む処理全体は **5.515 秒から 2.647 秒（52.00% 短縮）**になった。

## 条件と再実行

- 比較元: `c78d1913336f14915c448c8f8a67c6374b231ea2`
- 比較先: この変更を適用した未コミットの作業ツリー
- CPU: Intel Core i5-12400、Linux CPU 0 に固定
- OS: WSL2 Linux `6.18.33.2-microsoft-standard-WSL2`、x86_64
- Rust: `1.98.1 (48a229cea 2026-09-01)`、LLVM 22.1.8
- Cargo: 最適化した bench profile、`--locked --offline`、変更前後で別のビルド先
- 順序: before-1 → after-1 → after-2 → before-2
- 各実行: ウォームアップ 200 ms 以上、10 サンプル、サンプル実時間 50 ms 以上
- 集計: 各ケース・各実装につき計 20 サンプル、全 440 サンプル

リポジトリのルートで実行する。Python 3.12 以上が必要。

```sh
python3 scripts/bench_compare.py c78d191 --offline --rounds 2 --samples 10
```

今回使った保存先は `target/benchmarks/refactor-comparison/`。
上のコマンドは新しい保存先を自動生成する。
Rust バージョンを合わせる場合は `--toolchain 1.98.1` を指定する。
詳細な条件・入力と実行ファイルの SHA-256 は [experiment.json](experiment.json) にある。
元のソース snapshot、実行ファイル、実行した Python スクリプト `runner.py` は
今回の `target/benchmarks/refactor-comparison/` に保持している。

両方の実装で現在の同じ入力とベンチマークコードを使った。
既存ベンチマークにあった、同一 import の実体化数の古い期待値と、
停止証明のない旧 `Prun` 入力は、両方に同じ修正を適用した。
ライブラリ・テスト入力・ベンチマークディレクトリがバイト単位で一致し、
実行ファイルの SHA-256 が異なることを確認した。

## 全ケースの結果

単位は ms。変化率は負なら高速化。CV はサンプル間のばらつきの目安。

| ケース | 変更前 | 変更後 | 変化率 | CV 前 / 後 (%) |
| --- | ---: | ---: | ---: | ---: |
| parse/mccarthy91 | 0.091567 | 0.086062 | -6.01% | 9.00 / 9.89 |
| load/library | 5.943847 | 5.907629 | -0.61% | 5.36 / 5.99 |
| check/library | 5508.143547 | 2562.246691 | -53.48% | 2.05 / 2.34 |
| pipeline/library | 5514.709759 | 2647.057417 | -52.00% | 2.23 / 3.47 |
| pipeline/mccarthy91 | 47.180852 | 46.873934 | -0.65% | 7.00 / 7.55 |
| instantiate/128x16-unused | 1.562163 | 1.557276 | -0.31% | 8.03 / 3.95 |
| instantiate/128x16-one-each | 1.606288 | 1.697703 | +5.69% | 5.01 / 6.41 |
| normalize/beta256 | 0.006628 | 0.006650 | +0.34% | 3.77 / 9.21 |
| kernel/closure64x128 | 19.976061 | 0.005600 | -99.97% | 9.71 / 6.25 |
| evaluate/countdown32 | 0.198548 | 0.194676 | -1.95% | 6.80 / 7.82 |
| evaluate/countdown128 | 2.784833 | 2.852866 | +2.44% | 28.95 / 9.92 |

閉性判定の単体ケースは、64 段の共有された型を 128 回判定する負荷であり、
最初のキャッシュ構築時間も含む。ライブラリの型検査は、各回の中央値でも
変更前 5508 / 5507 ms、変更後 2556 / 2591 ms と改善が再現した。
それ以外の小さな差については、CV と実行間の変動もあるため優劣を断定しない。
測定値はこのマシンと入力での結果であり、有意差検定は行っていない。

集計用 TSV は [summary.tsv](summary.tsv)。生サンプルは
[before-1.tsv](before-1.tsv)、[after-1.tsv](after-1.tsv)、
[after-2.tsv](after-2.tsv)、[before-2.tsv](before-2.tsv) に保存した。

## 検証

- `cargo test --workspace --locked --offline`: 161 テスト成功（doc-test を含む）。
- `cargo clippy --workspace --all-targets --locked --offline -- -D warnings`: 成功。
- 全ベンチマークで期待結果と正常終了を確認。
- 保存済みサンプルから中央値を別途再計算して集計値との一致を確認。
- 基準比較、未完了データの拒否、上書き防止、フィルタ、CPU と保存先の指定を検証。
