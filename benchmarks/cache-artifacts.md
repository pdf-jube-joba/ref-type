# package artifact の計測

`cache_artifacts.py` は固定サイズの package からなる chain と diamond を生成し、cold、warm、利用側変更、入口編集、推移依存編集、訪問順変更、途中再開を順番に計測する。
`--project` で実ライブラリの cold と warm を追加する。
各ケースの wall time、peak RSS、終了状態、保存量、CLI の cache 統計を JSON に記録する。
新形式では object の種類別に格納量と展開量も記録し、依存本体の増加を圧縮率から独立して比較する。

```sh
python3 benchmarks/cache_artifacts.py target/release/cli \
  --output benchmarks/cache-artifacts-after.json \
  --project libs/std
```

一時データは既定で `refcache/artifact-benchmark-scratch/` のディスク領域を使う。
`--work-dir` で保存先を指定する。
各検査プロセスの仮想メモリ上限は既定1536 MiB、ケースごとの時間上限は120秒、cache の上限は2048 MiBとし、`--memory-mib`、`--timeout`、`--cache-mib` で調整する。
実行優先度を下げ、終了時と中断時は同じ process group の子プロセスを回収する。
ビルド・検証・計測は直列で実行する。
大きい実例では `--retain-project-caches refcache/cache-measurement` で新しい保存先を指定し、完了済みの成果物を検証後も保持できる。
`--resume-project-cache` と一つの `--project` を指定すると、その保存先からの再開と無変更検査を計測する。
再開は JSON の `resume` として記録する。

旧実装の初回記録は [cache-artifacts-before.json](cache-artifacts-before.json) にある。
この記録の実行中には Rust のビルドが並行し、`/tmp` の tmpfs によるメモリ消費も発生した。
`computations` の cold と warm は一時領域の容量不足により失敗しており、完走した性能比較から除外する。

ビルドを止め、ディスク上の一時領域で取り直した旧実装の記録は [cache-artifacts-before-controlled.json](cache-artifacts-before-controlled.json) にある。
同じ実行条件で chain の段数を32へ増やした記録は [cache-artifacts-before-chain32.json](cache-artifacts-before-chain32.json) にある。
旧実装の `std` は cold 4.774秒・419,572 KiB、warm 0.522秒・121,912 KiB、保存量29,911,933 bytesだった。
`computations` と `differential_forms` は各120秒の上限で停止したため、成功した検査の所要時間として扱わない。

## 新形式の比較

最終実装の同条件の記録は [cache-artifacts-after-controlled.json](cache-artifacts-after-controlled.json)、32段の記録は [cache-artifacts-after-chain32.json](cache-artifacts-after-chain32.json) にある。
各記録には使用した release バイナリの SHA-256 を含める。
新形式の記録には user time と system time も含める。
以下の保存量は専用 cache 全体の実測値で、編集や別利用側のケースでは先行ケースの成果物も含む。

| ケース | 旧 wall 秒 | 新 wall 秒 | 旧 peak RSS KiB | 新 peak RSS KiB | 旧保存 bytes | 新保存 bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| chain 8 cold | 0.228 | 0.810 | 11,428 | 14,544 | 157,688 | 34,205 |
| chain 8 warm | 0.069 | 0.136 | 7,164 | 8,068 | 157,688 | 34,205 |
| 別利用側 | 0.069 | 0.230 | 11,316 | 14,360 | 185,716 | 38,529 |
| 入口編集 | 0.069 | 0.229 | 11,464 | 14,360 | 215,127 | 43,497 |
| 推移依存編集 | 0.169 | 0.665 | 11,368 | 14,296 | 302,938 | 74,769 |
| 中断再開 | 1.127 | 13.334 | 15,904 | 21,796 | 587,043 | 235,486 |
| std cold | 4.774 | 24.113 | 419,572 | 592,512 | 29,911,933 | 9,246,343 |
| std warm | 0.522 | 0.968 | 121,912 | 81,428 | 29,911,933 | 9,246,343 |

`std` の保存量は約69%減り、warm の peak RSS は約33%減った。
warm の `checked_modules`、`environment_read_bytes`、`environment_imports` はすべて0で、結果だけを読み込む経路が成立している。
別利用側は依存18 moduleを再利用し、自身の2 moduleだけを検査する。
検証した小ケースでは `package_skips` と `save_failures` は0だった。
中断再開の fixture は各 source module 境界で保存するため `--checkpoint-seconds 0` を使い、通常の既定30秒より保存処理の影響を強く受ける。

chain 8 から32へ増やすと、旧形式の総保存量は157,688から1,576,765 bytes、新形式は34,205から187,935 bytesへ増えた。
新形式の raw/kernel object の展開量は5,580から21,818 bytesであり、保存量の改善は圧縮率だけによるものではない。
resolver object の展開量は38,823から211,235 bytesで、raw/kernel とは別に集計する。
resolver object は両層の保存用参照表と依存範囲も含み、推移的な参照やscopeのID対応は深さに応じて増える。
この数値からresolver全体の厳密な線形増加は主張しない。
構造上はresolverの定義・入出力・structure表を所有範囲で選別し、既に検査済みの依存を具体化するときも依存の定義本体をコピーしない。
diamond のmacro成果物のテストも、利用側の保存表に依存macroの定義本体が入らないことを確認する。

## cold の回帰調査

[初回の新形式の記録](cache-artifacts-after-initial.json)では `std` cold が19.820秒、peak RSS が638,268 KiBだった。
単独で繰り返した `perf` 計測でも15.58秒・638,268 KiBとなり、回帰を確認した。
CPU profile では保存用 identity の生成と表の検索、割当・解放が目立った。
参照ラベルを固定長にし、グラフの整列キーを一度だけ計算し、identity 収集時の共有グラフ複製と参照表の二重保持を減らした。
保存前には不要になった検査環境を解放する。
object・manifest・容量会計の耐久性を維持しつつ、再構築可能なアクセス情報やleaseの更新は原子的置換にまとめた。

最適化直後の `std` cold は9.749秒・592,464 KiBとなり、時間とメモリの改善を確認した。
最終バイナリの計測では24.113秒・592,512 KiBとなったが、user 7.95秒とsystem 2.21秒の合計は10.16秒であり、wall timeには約13.95秒の非CPU時間を含む。
この待ち時間の原因は確定していないため、最適化直後のwall timeを最終結果として代用しない。
旧形式よりcoldのコストは大きく、peak RSSも約41%増えている。
独立成果物の抽出、決定的な参照ラベルの生成、公開単位の細分化には依然としてコストがあり、小さい package の cold と頻繁な checkpoint 保存にも現れる。
今回の改善は、保存量・依存共有・無効化範囲・結果だけの読み込みを主な利点とし、cold の速度改善を保証するものではない。

## 実装の検証

workspaceのCLI以外は40 suite・567テストを通過した。
その後の共有グラフ保持量の改善はelaborationとsemaの408テストで確認した。
最終の保存失敗理由の追加はartifactの11テスト、module結果へのfallback修正はsemaの79テストで確認した。
CLIの最終release版は単体5件・統合47件がすべて通過した。
統合テストにはlibrary・manifolds-de-rham・topological-k-theoryの利用例、別プロセスでの再利用、推移的依存の編集、worker中断、`--no-cache`での保存先保持を含む。
大きい利用例は実データ検証で生成した同じrelease版のcacheを複製して使用し、他のfixtureは各テストの保存先とオプションを使った。
LSP・docs・playgroundを含むworkspaceのnativeビルドと、semaの`wasm32-unknown-unknown`ビルドも通過した。
`cargo fmt --all -- --check`、差分の空白検査、計測スクリプトの構文検査も通過した。

結果objectは有効でもpackage manifestが揃わない場合、従来の実装途中版では無変更検査で依存環境をimportしていた。
現在はpackageの完全・部分成果物を確認した後、不足するmodule結果を現在のmodule keyとpathで照合し、結果が揃う場合は環境をimportしない。
回帰テストはmanifest欠損、部分manifestとの組合せ、`--full-check-local`に相当する強制検査を確認する。

`differential_forms` の最終実装の専用cache検査はcold 731.461秒・3,056,700 KiB、warm 69.515秒・327,672 KiBで成功した。
保存量は261,945,362 bytesだった。
coldではresolver artifactが16,777,216要素の上限に達し、環境保存を1件省略した。
検査結果は独立して保存され、warmでは`checked_modules`、`environment_read_bytes`、`environment_imports`、`save_failures`がすべて0だった。
修正前のwarmは127.952秒・1,271,232 KiBで、266,570,831 bytesの環境読み込みと150回のimportがあった。
修正前の記録は[cache-artifacts-before-result-fallback-fix.json](cache-artifacts-before-result-fallback-fix.json)、最終実装は[cache-artifacts-after-real-projects.json](cache-artifacts-after-real-projects.json)にある。
実ライブラリの上限は仮想メモリ3072 MiB、ケース3600秒、cache 8192 MiBとし、小ケースの計測条件とは区別する。

`computations`もcold 1812.939秒・3,105,932 KiB、warm 74.509秒・260,456 KiBで成功した。
保存量は1,048,028,398 bytesで、coldの環境保存省略は1件だった。
warmの再検査数・環境読込量・import回数・保存失敗はすべて0だった。
両実ライブラリのcoldではworker分割による処理の重複があり、`checked_modules`は全workerの検査回数の合計として読む。
旧実装の同じ実ライブラリには完走した比較値がないため、coldの速度改善率は算出しない。

## workspace との統合

workspace の共通保存先と独立成果物を接続した後の小さい fixture の記録は [cache-artifacts-workspace.json](cache-artifacts-workspace.json) にある。
dev profile のバイナリで、chain の深さ4、仮想メモリ512 MiB、各ケース60秒、cache32 MiBを上限として逐次実行した。
別の利用側は依存10 moduleを再利用し、自身の2 moduleだけを検査した。
chain と diamond の無変更検査、中断から再開した後の無変更検査は、再検査数・環境読込量・import 回数がすべて0だった。
中断時には checkpoint を確認して worker を終了し、その checkpoint からの再開に成功した。
CLI の workspace テストは、依存 package の単体検査後に訪問順と検査範囲の異なる利用側へ成果物を読み込めることを確認する。
workspace の621テスト、Clippy、sema の WebAssembly 向けビルドが通過した。
この fixture の記録は、上記の release profile による実ライブラリの性能比較とは実行条件が異なる。
