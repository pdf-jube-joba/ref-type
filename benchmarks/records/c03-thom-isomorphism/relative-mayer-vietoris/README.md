# Relative Mayer–Vietoris checkpoint

The focused `cohomology_thom.RelativeMayerVietoris` check accepted the sources recorded in `inputs.json` with the standard cache enabled.
Command: `target/release/cli libs/topology/cohomology_thom --module cohomology_thom.RelativeMayerVietoris --memory-mib 12288 --diagnostics compact --report-json work/c03/mvcohomology.json`.

This verifies the free complement bases, small relative chain complex, split short exact chain sequence, arbitrary coefficient cochain sequence, and long exact sequence transported to ordinary relative cohomology and the direct sum of the open pieces.
This is incremental verification, not completion of C03 or an aggregate repository check.
