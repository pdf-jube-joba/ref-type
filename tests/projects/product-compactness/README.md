# 積のコンパクト性定理の具体化

集合を parameter に持つ module から、`topology.Product.Compactness` の `productCompact` と `productCompactIn` を同じ命題へ適用する。
CLI の `product_compactness_specialization_succeeds` で検査する。

```sh
target/debug/cli tests/projects/product-compactness --module product_compactness_examples --full-check-local --diagnostics compact
```
