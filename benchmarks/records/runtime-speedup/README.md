# 処理系の実行時間の比較

比較元は main の `e31c458c`、比較先はこのディレクトリと同じ変更に含まれる実装。
AMD Ryzen 5 7535U、WSL2 Linux x86_64、rustc 1.98.1 で計測した。
両方を release でビルドし、変更後には ThinLTO と CLI の mimalloc を含む。
計測時にはビルドとテストを停止し、CLI の起動から worker の終了とキャッシュ処理までを含めた。

## 計測結果

| ライブラリ | キャッシュなし（変更前 → 後） | 倍率 | 再利用（変更前 → 後） | 倍率 |
| --- | ---: | ---: | ---: | ---: |
| `libs/std` | 2.938 → 1.684 秒 | 1.74倍 | 0.549 → 0.083 秒 | 6.61倍 |
| `libs/category` | 4.314 → 2.859 秒 | 1.51倍 | 0.548 → 0.084 秒 | 6.52倍 |
| `libs/algebra/integer_matrices` | 17.372 → 11.344 秒 | 1.53倍 | 0.751 → 0.145 秒 | 5.18倍 |
| `libs/algebra/linear_algebra` | 14.971 → 9.482 秒 | 1.58倍 | 0.792 → 0.144 秒 | 5.50倍 |

キャッシュなしは1.51〜1.74倍で、目標の2倍には達していない。
再利用はソースが変更されていない場合の測定。
`cold` は変更後の整数行列の計測途中で終了しており、`after-cold.json` は未完了の記録。

## 検証

Rust workspace のテスト353件と CLI の受け入れテスト423件が成功した。

```sh
CARGO_PROFILE_RELEASE_LTO=false cargo test --workspace --release --locked -j 2 --no-fail-fast
python3 tests/tests.py --command /path/to/after-cli
```

## 計測条件

- `off`: 永続キャッシュなしで各ライブラリを3回検査した中央値。
- `shared`: 空の共有キャッシュから各ライブラリを4回検査し、各対象の初回を除いた3回の中央値。
- `cold`: 毎回空のキャッシュから検査して保存する1回の測定。

`--diagnostics compact --no-progress --memory-mib 3072 --cache-budget-mib 8192` を両実装に指定した。
1回の上限時間は300秒。
JSONには各回の経過時間、CPU時間、最大RSS、終了状態、ソースと実行ファイルのSHA-256、実行コマンドを保存する。
共有キャッシュには4ライブラリの結果が入り、再利用時の測定にはその保存先全体が存在する。

## 変更内容

完全なソーススナップショットの検査結果を直接再利用し、毎回の構文・依存グラフの再構築を省いた。
キャッシュ容量の記録に基づいて回収を判断し、変更のない読み込み時の全ファイル走査を減らした。
成果物の識別子を名前空間ごとの数値表で変換し、同じ識別子の文字列確保と収集を繰り返さないようにした。
型検査では束縛文脈と置換結果の共有を改善し、読み取り専用の式走査、メタ変数探索、パラメータの有無の検査にかかる処理を減らした。

## 再実行

変更前後の release CLI を別々に保存し、リポジトリルートから実行する。

```sh
bash benchmarks/records/runtime-speedup/measure.sh /path/to/before-cli /path/to/after-cli
```

各実行のログと一時キャッシュは `benchmarks/runs/speedup/comparison-*` に置き、比較用JSONをこのディレクトリへコピーする。
