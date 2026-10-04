# 検査環境キャッシュのメモリ増加と WSL 停止の調査

## 2026-10-04 の観測

検査環境の永続化を実装中に、`cargo run --locked --offline -p sema --example incremental -- libs/std libs/std/src/Alg/Alg.ref` を実行した。
その後、WSL が応答しなくなり、21:03:29 JST に再起動した。
再起動後の WSL のメモリは約 7.37 GiB、swap は 2 GiB だった。

直前の boot `2fc4709383374b48803dec30932b9019` の journal には、次の記録が残っている。

- 20:59:52 JST: `systemd-resolved` が `Under memory pressure, flushing caches.` を記録した。
- 21:02:57 JST: kernel が `page allocation failure: order:7` を記録した。
- 再起動後: journald が、前回の journal を破損または正常終了していないファイルとして退避した。

前回 boot に OOM killer の実行記録は見つからなかった。
メモリ逼迫は確認できるが、WSL 全体の停止を起こした Windows 側の直接の原因までは、この journal だけでは確定できない。

再起動後は、既存の `target/debug/examples/incremental` に仮想メモリ上限 768 MiB、実行時間上限 30 秒、core dump 上限 0 を設定して同じ入力を実行した。
初回検査の完了表示に到達する前に、16 MiB の追加確保が失敗して SIGABRT で終了した。
子プロセスの最大 RSS は 683,156 KiB だった。
この再現はプロセスに設定した上限で停止した。

## 実装上の増幅要因

`Checker::check_range` はモジュールの区切りごとに `postcard::to_allocvec(workspace)` を呼び、それまでに構築した環境全体を直列化していた。
`Database::query` はそれらを `saved: Vec<_>` に蓄積し、検査成功後にすべてを `Database::environments` へ移していた。
一つの checkpoint の大きさを \(S_i\) とすると、保持量は \(\sum_i S_i\) となる。
環境がモジュール数に比例して増える場合、全 checkpoint の保持量は二次的に増える。
保持量や単一 checkpoint の直列化に上限がなく、検査途中から大きなメモリを確保できる状態だった。

`Rc<DeclarationRemapping>` と `Arc<SourceFile>` には、メモリ上で共有している大きな値が含まれる。
通常の serde の `rc` 対応では共有先を参照の出現ごとに保存するため、共有されている remapping と source text が複製される。
復元時にも同じ内容を別々に確保する。
共有 arena 自体は一度だけ保存していたが、これらの共有値が保存量と復元時の保持量を増幅していた。

`incremental` example の全再構築比較は、編集前後の checkpoint を保持した database が生存する間に別の database を作る。
このため、初回を通過しても、編集後と全再構築の段階で保持量がさらに増える。
各要因の寄与率は個別には測定していない。

## 対策と検証

次の対策を実装した。

1. 単一 checkpoint の圧縮前後のサイズを 16 MiB に制限した。
   直列化途中のバッファ増加と展開サイズにも上限を適用し、上限超過時は `environment_skips` に計上して検査を続ける。
2. remapping を共有テーブルに集約して ID で参照し、source text は現在の snapshot から再接続する形にした。
   raw と kernel は同じ arena を使って復元し、保存バイナリは DEFLATE で圧縮する。
3. 暫定 checkpoint と database の memory cache をそれぞれ 64 MiB、合わせて最大 128 MiB の payload に制限した。
   保存時点の近い候補を間引いて先頭側の依存先の環境も保持し、成功時の移動には `Arc` を使う。
   batch の検査成功後に checkpoint を公開する。
4. 一度の batch で直列化する候補を最大 32 箇所に分散させ、保存処理そのものの時間と一時確保を抑えた。
   `--no-cache` および disk cache を使わない統計取得では環境保存を省く。
5. 部分編集、別プロセスからの復元、破損時の再検査、エラー時の独立した module の検査をテストした。
   検査順の途中を省略した場合は、完全な prefix として保存できる位置までに checkpoint を限定する。
6. ビルドとテストは並列ジョブ数 1、仮想メモリ上限 3 GiB で実行した。
   標準ライブラリの比較は仮想メモリ上限 1.5 GiB、時間上限 45 秒で完了した。

容量制限は checkpoint の payload と直列化・展開バッファに対するもので、通常の型検査環境を含むプロセス全体のメモリ上限ではない。

## 修正後の測定

2026-10-04 に dev profile（最適化あり）の `incremental` example を 1 回実行した。
`libs/std/src/Alg/Alg.ref` に宣言を追加した snapshot を作り、初回・未編集の再問い合わせ・編集後・別 database による全再構築を同じプロセスで比較した。
編集後と全再構築の semantic result の一致も example 内で確認した。

| 条件 | 経過時間 | 検査 module 数 | 復元 module 数 |
| --- | --- | --- | --- |
| 初回 | 3.228 秒 | 194 | 0 |
| 未編集の再問い合わせ | 48.4 ms | 0 | 0 |
| 宣言追加後 | 1.462 秒 | 52 | 126 |
| 編集後の全再構築 | 2.920 秒 | 194 | 0 |

初回の checkpoint 保持量は 17,438,401 bytes（約 16.6 MiB）で、編集後も同じだった。
編集後の `environment_hits` は 1、全段階の `environment_skips` は 0 だった。
比較処理全体の最大 RSS は 694,148 KiB（約 678 MiB）だった。
この RSS には比較用の二つの database と通常の型検査環境も含まれる。
修正前の再現は低いメモリ上限で途中終了したため、修正前後の RSS から削減率を算出することはできない。

実行時の上限は次のコマンドで再現できる。

```sh
cargo build --locked --offline -j 1 -p sema --example incremental
prlimit --as=1610612736 --core=0 -- timeout 45s target/debug/examples/incremental libs/std libs/std/src/Alg/Alg.ref
```

workspace 全体のテストと、全 target に対する `cargo clippy -- -D warnings` が成功した。
最終調整後にも sema の単体テスト 1 件と semantic テスト 29 件が成功し、実際の標準ライブラリ編集で保存環境の復元と全再検査との一致を確認した。
CLI の別プロセス間での再利用テスト 2 件も成功した。
