# Bundle chart calculations

Full package verification accepted the fixed sources in `inputs.json`.
Command: `target/release/cli libs/topology/cohomology_thom --module cohomology_thom --memory-mib 12288 --diagnostics compact --report-json work/c03/bundle-charts-whole.json`.

Actual bundle charts yield norm gauges and radial pair homeomorphisms to standard disk pairs. The induced local Thom map is cup product with the transported normalized class. The restricted disk bundle is explicitly homeomorphic to the chart preimage in the original disk bundle; the cup-product isomorphism and preceding-degree vanishing are transported to that open pair. Global finite-CW classes and final aggregate checks remain in progress.
