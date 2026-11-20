# A09 型検査記録

2026-11-20 UTC に検査した。
起点は `origin/main` の `132946b79f3e1e181c11d737530752f4a4651b7b`、修正対象コミットは `8472e5ad3236870c01a27d42c926351dfcc03e1e`、ブランチは `fix/a09-typecheck`。
ソース変更は `libs/analysis/euclidean_sobolev` の13ファイルで、module の参照先、関数引数、帰納法の仮定、場合分けの結論を明示した。
既存の証明を使い、定理の追加や公理の追加はない。

## 検査器とコマンド

```sh
RUSTUP_HOME=/workspace/.ref-type-toolchain/rustup \
CARGO_HOME=/workspace/.ref-type-toolchain/cargo \
/workspace/.ref-type-toolchain/cargo/bin/cargo +1.100.0 build --locked --release -p cli -j 4

python3 scripts/check_all.py libs/analysis/euclidean_sobolev \
  --state-dir /workspace/a09-check/package-final --cache-dir libs/refcache \
  --memory-mib 8192 --cache-budget-mib 12288

python3 scripts/check_all.py libs \
  --state-dir /workspace/a09-check/repository --cache-dir libs/refcache \
  --memory-mib 8192 --cache-budget-mib 12288
```

検査器の SHA-256 は `ffff71f26ce98f7558c99846cb544115200534504c50d5f9c838b0eb870afa64`。
ドライバーの SHA-256 は `5400a85680b1835c4c108ca753ac0511d5d07a0598577bcabd26ad220b89faa4`。
最終検査後に現在のソースと対象一覧を再列挙し、全体検査の保存済み snapshot・対象一覧との完全一致も確認した。

## 結果

| 検査 | 結果 | 確認済み / 対象 | 新規検査 / 再利用 |
| --- | --- | --- | --- |
| A09 と依存パッケージ全体 | accepted、34パッケージ | 3,274 / 3,274 | 0 / 3,274 |
| 全体の初回実行 | 出力先の Broken pipe で中断 | 10,529 / 15,524 | 4,021 / 6,508 |
| 同一入力からの全体再開 | tubular_neighborhoods で rejected、94パッケージ通過 | 11,546 / 15,524 | 5,683 / 5,863 |

新規検査・再利用はドライバーの分類で、全体再開の件数は引き継いだ accepted scope を含む。
A09 本体31 module は修正後ソースの検査で全て通過し、上表の最終検査では検査器が現行入力と照合したキャッシュを再利用した。
全体検査でも A09 の scope は accepted。
上表の各実行の保存失敗と破損キャッシュ読み込みは0件。
全体を成功扱いにはしていない。

## 全体検査の阻害箇所と再開

最初の型検査の阻害箇所は `libs/geometry/tubular_neighborhoods/src/Euclidean/On/Of/With/Compact.ref:9` の `Resolution Error: child module 'Frame' was not found`。
このパッケージは A09 の依存閉包に含まれず、該当ソースは起点の main と同一。
最後に accepted となった全体 scope は `thom_spaces`。
拒否された scope の CLI 記録は `last_module = thom_spaces.Thom.Tube`、`last_checkpoint = 17159`。
未確認の全体対象は3,978 module。

初回の環境中断時は driver が `[Errno 32] Broken pipe`、実行中の `singular_finite_algebra` が `interrupted` を記録した。
その scope の `last_module` は `homological_algebra.Kunneth.Integer.Theorem.At`、`last_checkpoint` は24759。
標準出力・標準エラーをファイルに保存して再開し、このパッケージはその後 accepted になった。

同一のソース・検査器で accepted scope を引き継ぐコマンドは次のとおり。
ソースや検査器が変わった場合は `--resume-report` を外し、同じキャッシュを使って現在の入力を再検査する。

```sh
python3 scripts/check_all.py libs \
  --state-dir /workspace/a09-check/repository --cache-dir libs/refcache \
  --memory-mib 8192 --cache-budget-mib 12288 \
  --resume-report /workspace/a09-check/repository/20261120T010158.559646Z/report.json \
  > /workspace/a09-check/repository-resume-next.log 2>&1
```

## 保存した証跡

| 対象 | report.json | source snapshot の SHA-256 |
| --- | --- | --- |
| A09 と依存パッケージ | `/workspace/a09-check/package-final/20261120T004312.432174Z/report.json` | `ccf5bdd9dcba00ae20ee6004e5ab13e1f607e2c170d5ddded635844a2acf8311` |
| 全体初回 | `/workspace/a09-check/repository/20261120T004432.959570Z/report.json` | `74de0269a382a73a67deb013e6a2f97102bfb9ed6bdf0db360f0c4c176f82c09` |
| 全体再開 | `/workspace/a09-check/repository/20261120T010158.559646Z/report.json` | `74de0269a382a73a67deb013e6a2f97102bfb9ed6bdf0db360f0c4c176f82c09` |

各ディレクトリに source snapshot、対象一覧、scope ごとの JSON とログがある。
最終阻害箇所の詳細は `00006-tubular_neighborhoods.log` と同名の JSON に保存した。
最終差分は `git diff --check origin/main...HEAD` と `git diff --check` を通過した。
