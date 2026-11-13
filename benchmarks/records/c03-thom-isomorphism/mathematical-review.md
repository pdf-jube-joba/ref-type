# Mathematical review of the direct-sum construction

Reviewed source checkpoint: `3e6f2c5cf` (scoped checking remains in progress).

An independent review of `Models`, `Modeled`, the actual transported local models and fibers, paired rank transport, and the integral/mod-2 global product orientations found no missing mathematical input.
The local model proof supplies a cup isomorphism for every refinement; actual fiber homeomorphisms supply generators, and finite Mayer–Vietoris gluing then constructs the global class.
The normalization of the resulting class by its actual fiber restrictions does not replace those local generator proofs.
The optional signed-orientation comparison assumes equality of the two fiber orientations, then proves equality of classes and Thom maps.

A separate independent review of the standard closed-face product induction, its identification with the actual shell product, the integral sign, coefficient change and mod-2 reduction found the map directions and signs consistent.
The successor comparison uses the actual suspension connecting formula with sign \( (-1)^n \).
The degree-zero step uses the unit class and integer linearity.
The final sign follows from the existing classification of integer automorphisms, after the product is proved to induce an isomorphism.
Closed faces are kept as separate family members until the comparison with the open-shell family; no open-cover theorem is applied directly to a closed-face union.

This mathematical review does not establish checker acceptance of the unverified scopes or completion of C03.

A follow-up review of the zero-dimensional repair confirms that the native and forgotten integer actions are connected by a proved identity-on-additive-groups isomorphism.
The unit follows the actual additive empty-pair comparison, the ordinary unit cocycle and the singleton calculation.
Its dedicated scope accepted in 44.07 seconds.

Supplementary independent reviews at source checkpoint `fea453097` confirm that all four geometric callers use the same normalized disk-product map and boundary order.
The chart reindex transports the whole frame family and chart laws with explicit castRefl and ChartData eta, preserving the domain and literal normalized rank.
The refined Subdomain interface still quantifies over every open included subdomain and forwards both proof conditions at each constructor.
The normalized disk and chart helper scopes accepted separately.
The actual integral product identification and sign scope subsequently accepted in 743.12 seconds; its detailed report was lost during the environment reset and the observation is distinguished from retained direct reports.

A read-only post-recovery review at `8bb9c8b6b` found no concrete API mismatch in standard product coefficient change, mod-2 reduction, or the point example.
It checked carrier/rank order, native integer versus coefficient-ring maps, the actual coefficient-change and sign chain, explicit cycle endpoints, and the point normalization/Gysin exports.
These checks supplement the pending formal scope and final package/aggregate checks.

A separate read-only review found an ambient/subtype equality mismatch in both local standard-model fiber inverses.
The repair uses the existing C02 `CWType.ListRefinement.ext` to lift equality of underlying base points before applying product extensionality.
This source repair remains pending its local/full formal check.

After the selected package check exposed rank lookup errors, a follow-up actual-API review confirmed `Family.Of[bundle].rankFrame` has direction `rank x = n`, and all direct-sum rank references now use that module.
The follow-up also checked canonical comparison directions, mod-2 coefficient squares, chart rank transports, and zero-section import scopes against their definitions; no further concrete mismatch was found by reading.
Formal direct-sum checking remains necessary and is in progress.

Final substantive plan-coverage review at `e95106ec0` found concrete implementations and public APIs for every C03 requirement.
The review checked fiber normalization, actual finite Mayer–Vietoris gluing and cup isomorphisms, arbitrary commutative unital coefficient changes, pullback/direct-sum/orientation/zero-section comparisons, and the Euler-identified Gysin sequence of the actual sphere bundle.
The point example covers every rank and exposes normalization, reduction, reversal, Thom isomorphisms and Gysin sequences; package and dependent-plan documentation identify the actual APIs.
Direct-sum orientation comparison assumes equality of fiber orientations and proves global class equality, so it does not assume the requested global theorem.
No missing mathematical implementation or API blocker was found; the active and remaining direct-sum scopes plus final package/aggregate validation were still pending at review time.

The final read-only operational review at `954119fc1` approved the bounded-scope routing and selective package splitting.
Every eager partition retains the parent declarations and all immediate child subtrees; acceptance still requires CLI coverage of every requested scope and equality with the complete enumerated target set.
All scoped commands use the same immutable source files and aliases, and final validation compares the source JSON, exact target list and checker binary.
The reviewer confirmed no `.ref` or `.toml` changes since `c80d328`, and the Rust tree matches integrated main `c51c1971`.
No checker was started or interrupted for this review; final aggregate acceptance remained pending.

An independent read-only review of exact-input continuation approved `--resume-report`.
It requires equal checker digest, source digest and saved source content, and exact ordered target list.
Only accepted saved CLI scopes with exit zero and no save failures contribute; their coverage is reconstructed and must equal the donor's verified set.
The interrupted scope contributes nothing, and the resumed driver still checks the remaining targets and validates complete coverage plus final source/checker identity.
All eleven driver end-to-end checks passed, including partial-prefix continuation, forged aggregate coverage rejection and changed-source rejection.
At this point the integrated aggregate has accepted 12,846 of 15,306 targets; final acceptance is still pending.

A read-only review of the resumed scope's silent finalization found no concrete loop, deadlock or resource failure.
The elaborator calls `lower_all` after the final module event without per-declaration progress there; retirement follows only after lowering returns.
Lowering traverses finite declaration collections, with registered-item skips and active-cycle rejection in the pending definition worklist.
This justifies continuing the active worker, but supplies no time bound and does not establish acceptance.

Two subsequent short stack samples located the active finalization in `ArtifactStore.collect` / `store_bytes`, called by result publication in `save_covered_results`.
Thus the earlier source-only suggestion of silent lowering did not identify this observed running phase.
Measured shared cache usage was 13,490,205,238 bytes, above the 12 GiB budget; publication calls collection whenever accounting remains above the budget, including when retained data is pinned.
A resource-only continuation raises the cache budget to 20 GiB while retaining the 512 MiB graph residency and 16 GiB process ceiling.
The interrupted comparison-degree scope remains unaccepted; the fixed-input aggregate must complete it normally.
