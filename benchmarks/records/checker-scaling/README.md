# 依存チェーンと全体検査の時間・メモリ

変更前は main の `4626c588`、変更後はこのディレクトリと同じ変更を含む実装。
WSL2 Linux x86_64、rustc 1.99.0、`cargo build -p cli --locked` の dev profile（opt-level 2）で計測した。
比較用の計測はビルド・テストを終えてから順番に実行した。
仮想メモリ上限は各プロセス3072 MiB、キャッシュ容量上限は8192 MiB。

## 依存の深さによる増加

[scaling.py](../../scaling.py) で各 package に16宣言を置き、直前の package を参照するチェーンを生成した。
各回とも空のキャッシュを使い、時間は3回の中央値。
行数は依存先を含む `.ref` ファイルの合計である。

| 依存の段数 | 行数 | 変更前 | 変更後 |
| ---: | ---: | ---: | ---: |
| 8 | 151 | 0.264秒 | 0.243秒 |
| 16 | 303 | 0.626秒 | 0.465秒 |
| 32 | 607 | 2.218秒 | 0.908秒 |
| 64 | 1215 | 16.456秒 | 2.057秒 |

32段から64段では行数が約2倍で、変更前の時間は7.4倍、変更後は2.3倍になった。
64段の検査は8倍速くなった。
このケースでは、変更前に \(N^2\) より急な増加が見える。
一般の検査費用には依存構造・型の正規化・証明の内容も関わる。

全実行のコマンド、digest、CPU時間、最大RSSは [before.json](before.json) と [after.json](after.json) に保存した。

## manifolds 全体

`libs/geometry/manifolds` とその全依存1143モジュールを検査した。
変更前は提示された `topological_algebra.FiniteDimensional.Over (declarations)` のメモリ不足を再現し、128.298秒・最大RSS 2942 MiBで未完了になった。
[failure.json](failure.json) はphase計測を有効にした失敗記録で、同条件の時間比較は上の依存チェーンの表で行う。

| 変更後の検査 | 回数 | 時間の中央値 | 最大RSS | 結果 |
| --- | ---: | ---: | ---: | --- |
| `--full-check` | 2 | 49.563秒 | 1728 MiB | 全1143モジュール受理 |
| 無変更の通常検査 | 3 | 0.203秒 | 139 MiB | 保存済みの検証結果を再利用 |
| `--full-check-local` | 1 | 18.730秒 | 1282 MiB | 入口を再検査し、依存を再利用 |

全再検査は各回とも実行専用の空のキャッシュから検証し、終了後に共通の保存先へ公開した。
全再検査の2回とも時間・メモリによる分割と再試行は発生せず、レポートは `accepted`・`verification_reused: false` になった。
通常検査と入口再検査は、その公開済みキャッシュを使った。
詳細は [full.json](full.json)、[warm.json](warm.json)、[local.json](local.json) に保存した。

## 原因と変更

- 全体検査の依存環境が、利用側の参照範囲より大きかった。
  各 package の参照閉包を求め、大きい依存環境はその範囲だけを復元する。
  小さい成果物と検査済みの小さい依存チェーンは共有する。
- 成果物の公開時に、依存全体の identity catalog を複製していた。
  追加分を先に検証し、catalog に差分を公開する。
  部分成果物とcheckpointの復元も環境を消費するAPIに統一し、破損時は環境を解放して再構築する。
- 合成した置換 map はDAGとして共有していたが、探索は木として同じ経路を再訪していた。
  一回の探索で同じ map・キーの組合せを記録し、不一致の結果も共有する。
- live checker の引き継ぎで、依存の式に含まれる型が後からkernelへ登録される場合があった。
  その新しい型宣言も成果物の到達可能性に含める。

workerが異常終了した場合も検証済みの途中結果を公開し、再実行で利用できる。
メモリ不足の診断後に、存在しない最終レポートを読もうとして別のエラーに置き換わる経路も修正した。

## 検証と再実行

Rust workspace の既存テスト375件、受け入れテスト400件、benchmark utility の既存テスト6件が成功した。
`cargo fmt --all -- --check` と `cargo clippy --workspace --all-targets --locked -- -D warnings` も成功した。

```sh
cargo build -p cli --locked
python3 benchmarks/scaling.py --binary /path/to/before-cli --depths 8 16 32 64 --runs 3 --width 16 --output benchmarks/runs/compare-before/report.json
python3 benchmarks/scaling.py --binary target/debug/cli --depths 8 16 32 64 --runs 3 --width 16 --output benchmarks/runs/compare-after/report.json
python3 benchmarks/bench.py run libs/geometry/manifolds --binary target/debug/cli --cache-mode shared --cache-dir benchmarks/runs/compare-manifolds/cache --runs 2 --seconds 180 --output benchmarks/runs/compare-manifolds/full.json --extra --full-check
python3 benchmarks/bench.py run libs/geometry/manifolds --binary target/debug/cli --cache-mode shared --cache-dir benchmarks/runs/compare-manifolds/cache --runs 3 --output benchmarks/runs/compare-manifolds/warm.json
python3 benchmarks/bench.py run libs/geometry/manifolds --binary target/debug/cli --cache-mode shared --cache-dir benchmarks/runs/compare-manifolds/cache --runs 1 --output benchmarks/runs/compare-manifolds/local.json --extra --full-check-local
```
