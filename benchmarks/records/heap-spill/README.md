# ヒープ全体の自動退避

2026-11-14、Linux / WSL2で、式本文に加えてfrontendと索引もファイルで裏付けるallocatorを確認した。
バイナリのSHA-256、生成条件、終了状態、検査ステップ数と資源観測値は [summary.json](summary.json) に記録した。

```sh
cargo build -p cli --release --locked
python3 benchmarks/heap_spill.py --groups 128 --width 128 --memory-mib 32
```

128個のmoduleに、それぞれ128組のinductive・型別名・恒等写像・値を置き、最後のmoduleから先頭側の型別名を再参照した。
新規検査、保存済み結果の再利用、`--full-check-local` による復元と再検査、単独ファイルの `--no-cache` 検査が成功した。
最後に異なるinductiveの値を混ぜると、型エラーとして拒否された。
packageの各実行はworker一つで、復旧は0回、保存失敗も0回だった。
32 MiBは退避開始の目安であり、新規検査の最大RSSは356,584 KiB、復元と再検査では404,436 KiBだった。
ヒープのページ回収要求は各検査で発生した。

実ライブラリは `libs/topology/examples/finite_models` と依存先を合わせた計41 package、5,180 moduleを、空のcacheから既定の3072 MiB設定で検査した。
確認用の900秒制限により `time-limit` で終了し、完了した検査ステップは53,348、保存済みcheckpointは53,046だった。
workerは一つ、復旧は0回、保存失敗は0回、最大RSSは3,441,800 KiB、最大仮想メモリは10,054,760 KiBだった。
仮想メモリが3072 MiBを超えても継続したが、全体検査の完走は未確認である。
この実行は検査キャッシュの回収要求を5秒間隔に調整する前のバイナリであり、途中でビルドと小規模検証も併走したため、速度比較には使えない。
時間制限で終了したworkerは最終レポートを書けず、ヒープのページ回収要求量も未取得である。

最終版で `cargo test -p cli --locked` の12件、`scripts/test_check_all.py` の10件、`benchmarks/tests.py` の6件が成功した。
CLIを対象とした `cargo clippy -p cli --no-deps --all-targets --locked -- -D warnings` とformat確認も成功した。
