# A06 最終検査記録

全要件を実装した最終ソース `b182f3af4d519c3a0129151d7bd7f01ae55119da` の記録である。
Schwartz 可積分性、微分・座標乗算・平行移動・畳み込み公式、Schwartz 保存、Gaussian 変換、近似単位による反転公式と Schwartz 値の逆写像を含む。
正規化の π は Gaussian 積分による定義で構成し、逆係数は \((2\pi)^{-n}\) である。

通常全体検査は 11130/11130 対象を受理した。
新規検査 0、再利用 11130、保存失敗 0、破損読み取り 0、worker 回復 0、終了コード 0。
開始・終了のソース snapshot と対象一覧は一致し、checker バイナリも不変である。
全ソースの実際のバイト列が snapshot と一致することを保存時に確認した。

対象パッケージの `--full-check-local` は新規 131、再利用 734、保存失敗 0 で受理した。
A05 `lp_spaces` と G01 `smooth_partitions` の回帰も受理し、各検査前後の snapshot と全体検査 snapshot との一致を確認した。

通常 release checker は現在の Rust ソースからビルドした。
SHA-256 は `a92c84f2ffd0ab3f333a01de0301f647e347a2ec774f30cbba85c062c4346726`。
16 GiB の cgroup 上限に対し、通常全体検査の初期・最大メモリ上限はいずれも 12 GiB。
既存キャッシュは保持し、ソース・依存・処理系の照合を伴う通常検証を使用した。
実測時間・資源・キャッシュ統計は [verification.json](verification.json) と圧縮した各報告に記録する。

[targets.json.gz](targets.json.gz) は全対象一覧、[source-manifest.json.gz](source-manifest.json.gz) は読み込んだ全ファイルの SHA-256 一覧である。
foundation と preservation の記録は以前のソースに対する途中段階の記録である。

```sh
cargo build -p cli --release --locked
python3 scripts/check_all.py --initial-memory-mib 12288 --memory-mib 12288 --state-dir work/a06-complete-whole --min-free-mib 512
```
