# Shared macro checkpoint

This synthetic Linux benchmark runs the ordinary workspace CLI. One package builds 32 macro templates with 32 repeated captures each and imports the template scope 72 times. Checking this package first publishes a deterministic completed dependency checkpoint. A second invocation checks the full two-package workspace, restores that checkpoint and checks two new definitions. The second definition expands a restored alias. A third invocation verifies warm result reuse.

Build each revision with the same toolchain and profile. Pass both binaries the same workspace path and a new result directory per invocation. Each binary seeds its own cache under its production revision identity.

```sh
cargo build --locked -p cli
python3 benchmarks/checkpoint-macros/run.py target/debug/cli /tmp/macro-input /tmp/macro-control-1
```

The summary gives the worker's Linux VmRSS and signed change across the scope macro reconnect loop, that loop's elapsed time, and peak worker RSS across the entire second invocation (including consumer checks and saves). The first new declaration is the only declaration in consumer.First. Its successful module completion timestamp is elapsed time from CLI progress initialization as observed by the supervisor, which polls worker events at up to 50 ms intervals. The workspace root and consumer package header add no source declarations before it.

Compare the source digest, seed checkpoint position, new declaration, and source step count. Raw reports, logs and caches stay in the specified result directory. Use fresh result directories for repeats and compare median measurements.
