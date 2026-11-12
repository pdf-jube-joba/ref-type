# Cover-preserving maps

Full package verification accepted the sources in `inputs.json`.
Command: `target/release/cli libs/topology/cohomology_thom --module cohomology_thom --memory-mib 12288 --diagnostics compact --report-json work/c03/covermap-whole.json`.

The kernel-lift construction produces a cochain map from the middle and right maps of actual short exact sequences. Cover-preserving pair maps induce maps on the relative small cochain sequences, with connecting naturality. The ordinary comparison, global Thom construction and final aggregate checks remain in progress.
