# 点に依存する商の型の利用例

点ごとの商と有限引数列を含む関数型を、直接の型・型値の定義・局所 module で表し、lambda の注釈と外延性を検査する。
CLI の `pointwise_quotient_representations_succeed` は全5 project をキャッシュなしで検査する。

```sh
cargo test -p cli --test ref_files pointwise_quotient_representations_succeed --locked
```
