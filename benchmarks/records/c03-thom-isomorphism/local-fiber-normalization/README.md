# Local fiber normalization

Full package verification accepted the fixed sources in `inputs.json`.
Command: `target/release/cli libs/topology/cohomology_thom --module cohomology_thom --memory-mib 12288 --diagnostics compact --report-json work/c03/fiber-normalization-whole2.json`.

Relative cup product with the unit is proved with explicit degree transport. The top-degree local isomorphism sends the degree-zero unit to the normalized class and commutes with base pullbacks. Point disk classes are free generators. Actual fiber restrictions compute the degree-zero evaluation coordinate and jointly detect local classes; the normalized local class is uniquely characterized by these fiber generators. Relative pair homeomorphisms also induce coefficient-ring-linear isomorphisms. Global finite-CW classes and final aggregate checks remain in progress.
