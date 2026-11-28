# Checkpoint choice under memory pressure

Build both revisions with the same Rust toolchain and profile. Run on Linux with Python 3.11 or newer. The output directory must be new. Keep it outside Git.

```sh
cargo build --locked -p cli
python3 benchmarks/checkpoint-choice/run.py --binary target/debug/cli --output /tmp/checkpoint-choice-results
```

Repeat `--binary` to compare builds on the same source paths. The checker keys caches by build, so each binary creates its own seed. The ordinary workspace CLI is interrupted with SIGINT after the Heavy module's checkpoint. The fixture checks that the witness module has not started. All measured runs use independent copies of that binary's seed and pass the entire workspace once. Each accepted run must check the witness module, print its inferred type, and verify all six modules.

The fixture makes a large shared macro visible under many aliases, so expanding a saved environment into memory costs substantially more than the serialized size suggests. It includes 64 ordinary definitions before the interruption and a typed use of one of them in the final module. Each repetition runs with the inherited limits and with an explicit per-process address-space limit (80 MiB by default, adjust with `--as-mib`). Linux enforces RLIMIT_AS on the CLI and each worker. The checker report records peak worker RSS separately. Candidate decoded bytes sum the envelope and referenced graph payload lengths and measure serialized volume. Wall time covers the whole CLI and excludes preparing cache copies. The pressure control may legitimately report memory-limit. A successful pressure run must show a smaller prefix hit. See the JSON reports and logs beside summary.json for the individual observations.
