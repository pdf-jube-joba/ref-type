# Local cup-product Thom isomorphism

The full package check accepted the mathematical sources recorded in `inputs.json`.
Command: `target/release/cli libs/topology/cohomology_thom --module cohomology_thom --memory-mib 12288 --diagnostics compact --report-json work/c03/localcup-whole.json`.

`LocalDisk.On.Ring.canonical` constructs normalized classes by suspension.
`thomIsomorphism` proves that cup product with these classes, after pullback from the base, is an isomorphism over every commutative coefficient ring and in every rank.
The proof constructs the rank-zero inverse and inducts using the signed disk-step comparison and sign involution.
The positive-rank global construction and final aggregate verification remain in progress.
