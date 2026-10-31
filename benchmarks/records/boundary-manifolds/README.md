# G03 boundary and corner manifolds: verification

Base main: `7650fb3593d6a6cc6960055670db15dfed73b000`.
Checked source commit: `e600b538f41ad20d8639dac0791949f417fecdbb`.
Branch: `feat/g03-boundary-manifolds`.
The following evidence commit changes checking records only; the checked sources are identical.

The package constructs finite-dimensional quadrant charts, extendible smooth maps, chart-independent tangent spaces and differentials, inward/outward cones, neat embeddings, embedded coordinate faces, product boundary faces, ordinary interior/boundary manifolds and boundary tangent bundles.
Regular nonnegative domains and disks use the actual G02 submersion coordinates.
Examples cover the interval, disk, manifold times interval, nonlinear half-line map, quadrant face and dimension zero.
The general ordinary boundary construction takes a half-space chart cover of the boundary; faces of corner models retain their remaining quadrant constraints.
No Rust sources or foundational axioms were added or changed.

## Final verification

The normal release build and all listed checks returned exit code 0.
The focused `--full-check-local` check rechecked all 189 package modules and 2129 source steps.
Existing caches were preserved and used through normal source-backed validation.

| Check | Verified | Newly checked | Reused | Save failures | Corrupt reads |
| --- | ---: | ---: | ---: | ---: | ---: |
| boundary_manifolds (full local) | 1081 | 189 | 892 | 0 | 0 |
| inverse_implicit | 793 | 0 | 793 | 0 | 0 |
| manifolds | 628 | 0 | 628 | 0 | 0 |
| tangent_bundles | 712 | 0 | 712 | 0 | 0 |
| calculus | 537 | 0 | 537 | 0 | 0 |
| whole repository | 11188 | 10626 | 562 | 0 | 0 |

Checker SHA-256: `bd494ef8d7a16aa854a3cc9a9af4fd49c91afd4002baa0bf7895f304cd367118`.
Driver SHA-256: `b0b7159aa8440dd12d090fdb29cc61df4d7db29c8e58b11c335e8126b7e9ef9f`.
Whole source snapshot SHA-256 (identical start/end): `43a209c680a122790adbf5a2bcff7884746145d9b91875651d067ff53ba44bef`.
Focused source snapshot SHA-256 (identical start/end): `6b063f4ad53e7b523895f7c619345f15458f40e5eff21762a12bf95c4b41f7b2`.
The whole driver confirmed identical ordered target sets, complete coverage and an unchanged binary.
[whole-targets.txt.gz](whole-targets.txt.gz) records the exact ordered target set; decompressed SHA-256: `68b237744880773439edd3508be6993b2ef748b1a882223ac19371f12e29ba9f`.

Whole elapsed time: 2754.880 seconds.
Peak RSS: 10369208 KiB; peak virtual memory: 12424536 KiB.
Worker recoveries: 1; driver `checking.checkpoint_hits` aggregate: 0.
The final `compact_support_k` worker reached its 12 GiB virtual-memory ceiling while requesting 285,212,688 bytes.
The CLI automatically restarted from source checkpoint 36359 and reused source-validated saved results; the invocation returned exit code 0 with all 2,724 modules in its dependency closure verified.
Its execution report records 2 workers, 1 recovery, 4,858 source steps, `lost_steps=3202`, no duplicate or replayed source steps, and storage `checkpoint_resumes=1`.
The driver checkpoint-hit aggregate and storage checkpoint-resume counter measure different events; both actual values are preserved in `checks.json`.
Final whole coverage was 11,188/11,188 with matching source snapshots and checker identity.
The container memory ceiling was 16 GiB; the initial and maximum worker ceilings were both 12,288 MiB.

Commands, per-attempt exit codes, actual cache counters, target identities and snapshot correspondences are in [checks.json](checks.json).
Raw whole-check logs and snapshots remain in `/workspace/ref-type/work/g03-final-check/20261031T171740.620012Z`.
Focused/regression logs and snapshots remain at the `/tmp/g03-*` paths recorded in that JSON.

## Preliminary runs

The first normal G02 baseline on the rebuilt checker accepted 793 modules, with 793 newly checked, 0 reused and 0 save failures.
It preceded the new package registration and is not evidence for the final G03 sources.
Intermediate package checks caught elaboration errors during implementation; those were corrected before the source commit above.
All 97 top-level CLI invocations returned exit code 0; the single internal bounded-worker allocation failure and automatic recovery are recorded above.
A separate endpoint-enumeration command initially combined `--module` and `--list-modules`, which the CLI rejected with exit code 2 before checking; removing `--module` succeeded with exit code 0 and produced the matching focused endpoint snapshot.
No cache speedup is inferred from the environment name.
