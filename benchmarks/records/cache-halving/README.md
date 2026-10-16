# 実行時間とキャッシュ保存量の比較

比較元は main の `7dbb0e12721b874892717eccab44fb7602f3abeb`、比較先はこの PR の実装。
両方を `cargo build -p cli --release --locked` でビルドし、別名の実行ファイルを保存して比較した。
Linux x86_64 / Debian 13、Intel Xeon Platinum 8573C、CPU quota 4 cores、rustc 1.95.0 を使用した。
測定中にはビルドやテストを並行実行していない。
実行時間には CLI の起動、ソース読み込み、監督プロセスと worker の処理を含む。

## 結果

| 測定対象 | main | 変更後 | 短縮・削減 |
|---|---:|---:|---:|
| std: キャッシュなし | 10.567 s | 4.036 s | 61.8% |
| category: キャッシュなし | 18.868 s | 6.227 s | 67.0% |
| std: 全結果の再利用 | 0.647 s | 0.304 s | 53.0% |
| std: 圧縮環境キャッシュのメモリ | 8,555,165 bytes | 3,351,766 bytes | 60.8% |
| std: ディスクキャッシュ | 9,274,378 bytes | 4,072,407 bytes | 56.1% |
| std: 初回検査と保存 | 12.072 s | 8.539 s | 29.3% |
| category: std の環境を import して検査・保存 | 8.565 s | 8.184 s | 4.4% |
| category: 全結果の再利用（1回） | 0.859 s | 0.409 s | 52.4% |

単一環境・2ライブラリの測定であり、各回のばらつきは JSON の個別値で確認できる。

## 条件

- `off`: std と category を各3回、`--no-cache` で検査した中央値。
- `shared`: 空のキャッシュから std を6回実行し、初回保存を除く5回の中央値。
- `cold`: 毎回空のキャッシュから std を検査・保存する3回の中央値。
- `consumer`: std のキャッシュを用意した後、category を2回実行した個別値。
  初回は依存環境の import と category の検査・保存、2回目は全結果の再利用。

`--diagnostics compact --no-progress --memory-mib 3072 --cache-budget-mib 8192 --cache-stats` を両実装に指定した。
1回の上限時間は300秒。
キャッシュの圧縮環境メモリは `MemoryCacheStats.compressed_environment_bytes`、ディスク保存量は benchmark runner の `cache_bytes` を用いる。
プロセス全体の最大RSSはこれらと別の指標で、JSONの `peak_rss_kib` に記録されている。
全測定で検査成功、ソース不変、実行ファイル不変を確認した。
JSONには各回の時間、最大RSS、入力と実行ファイルのSHA-256、実際のコマンドを残している。
`cache-statistics.json` は `--cache-stats` のログから、保存メモリと再利用・import の件数などを抜き出したもの。
`runs/` 配下のログと大きな実行ファイルは保存対象外。

## 再実行

リポジトリルートから `bash benchmarks/records/cache-halving/measure.sh` を実行する。
比較元と比較先の release CLI を、事前に `benchmarks/runs/halving/before-cli` と `benchmarks/runs/halving/after-cli` に置く。
スクリプトの `comparison-before-cache` と `comparison-after-cache` は空の状態から開始する。
