# singular_cohomology の全体検査

変更前の `c09a3cc7` で、`singular_cohomology` の全検査から `chain_complexes` を処理する際の `expect("frontend atom")` を再現した。
実際の停止位置は依存先の `module_theory.Module.Over` にある module 引数の検査だった。

先行 package で intern された名前が、その package の保存対象から外れる場合がある。
後続 package がその名前を初めて保存対象にした際にも、生成済みという理由でメタデータが除かれていた。
保存する式から到達する atom を生成時期にかかわらず保持し、復元時にも式とメタデータの対応を検証するよう修正した。
独立した3つの小さい module を使う Rust テストでも変更前の panic を再現し、修正後の保存・復元と、メタデータを欠落させた成果物の検出を確認した。

その先では `Relative.Equivalence.Over.On.With` の宣言検査が3072 MiBの仮想メモリ上限に達した。
import の展開で約400万の遅延宣言を予約し、うち約200万を新しい特殊化として保持していた。
局所変数を含む特殊化も、呼び出し元と論理・Program の検査文脈が一致する範囲で共有し、同じ宣言と引数を持つ namespace の再展開を抑えるよう修正した。
失敗していた宣言検査は、修正後に同じ上限で受理され、最大RSSは2084704 KiBだった。

過去の分割構成を直ちに適用すると、キャッシュが揃っていても多数の worker を起動して通常検査に40.085秒かかっていた。
分割前にキャッシュだけで回答できるかを確認し、未検査のステップがあれば実際の検査を始める前に分割構成へ戻すよう修正した。

全2361モジュールの `--full-check` が成功した。
所要時間は28分21秒、最大RSSは2883540 KiBで、資源上限に応じた自動分割を含む。
全体検査の最終判定は [full-check.json](full-check.json)、保存済みの結果を使う通常検査3回は [warm.json](warm.json) に記録した。
通常検査は、全体の結果を初めて集約した回が5.027秒、その後は0.648秒と0.608秒で、3回とも検証結果を再利用した。
WSL2 Linux x86_64、dev profile（opt-level 2）、各 worker の仮想メモリ上限3072 MiBで実行した。
Rust workspace の376テストと受け入れテスト400件、fmt と clippy の検査も成功した。
CLI の分割済みキャッシュについて、未検査の入力、無変更の再実行、型エラーを加えた編集、全再検査の各経路も確認した。

```sh
cargo build -p cli --locked
target/debug/cli --full-check --report-json benchmarks/runs/cohomology-panic/full-final.json libs/topology/singular_cohomology
python3 benchmarks/bench.py run libs/topology/singular_cohomology --binary target/debug/cli --cache-mode shared --cache-dir libs/refcache --runs 3 --output benchmarks/runs/cohomology-panic/warm.json
```
