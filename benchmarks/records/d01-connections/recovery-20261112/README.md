# D01 verification recovery after runtime reset

Restored code: `fb2b41072ca46e07df27da4c40907fa203d56a10`, including main `fa5ced0f`.
The original clean `work` branch was preserved; recovery uses `math/d01-verification-recovery` in the existing environment.
D01's source tree is `a455cebf64748ecca2c01f50ca821375f473d2d5` and its manifest blob is `085b853133a8e004e720cb649a9d271d21ed950a`, identical to the durable checkpoint and independent review inputs.

The prior process, reports and snapshots were absent after reconnection, which returned a clean checkout at `d2232bb8`. Its last observed aggregate coverage was 10,891/14,486 and is not an aggregate pass. The prior observed focused successes are distinguished from the new durable reports here.

Each accepted stage retains its exact original report, worker reports, source hashes, loader aliases and comparison against both its recorded Git commit and current checkout. Progress checkpoints explicitly retain their original incomplete outcome. Only an accepted full driver report with complete target coverage establishes aggregate acceptance. `collect.py` checks these conditions; it does not create verification results.

Verification uses normal source-matched cache under `libs/refcache`, without deleting cache or using `--full-check`. Focused scopes use conservative memory bounds; the known K11 resource-limiting case uses the documented 15 GiB bound and 120-second checkpoint cadence before the aggregate run.

The first recovery aggregate used a 12 GiB initial bound and a 15 GiB ceiling. Existing `compact_support_k` repeatedly exhausted the initial bound, resuming at checkpoints 38564, 38567, 38587 and 38591. The supervisor retries while checkpoints advance. That attempt was deliberately stopped with exit 130 after 13,364/14,486 accepted target paths; it is not aggregate acceptance. `full-progress` preserves its exact interrupted report and worker log. The subsequent aggregate adopts A08's validated 15 GiB initial and maximum bounds, retaining the same compatible cache, mathematical source and checker. Source and checker identities are reconciled at completion.

[Cache observations](cache-observations.md) distinguish measured reuse, source/checker identities, lost reports and unknown storage persistence.

## Accepted fixed-source verification

The accepted aggregate checked commit `c6b9025427ce7d57d943614357f9d4ed3a2b711c`.
Its loader snapshot SHA-256 is `b4fa18a3f49ebda8492c937aa621f2cbb9d927c15e2f59bc4205e086434e3198` and checker SHA-256 is `5a9b8819402305b8004985f9ef6367f6e502293b90a11a9c0e9e80889d219b32`.
The final evidence commits change verification records only.

| Scope | Accepted targets | Newly checked | Reused |
| --- | ---: | ---: | ---: |
| D01 package and dependencies | 4,022 | 4,022 | 0 |
| B07 regression | 3,524 | 0 | 3,524 |
| Whole repository, 15 GiB profile | 14,486 | 280 | 14,206 |

The selected K11 resource case separately accepted 3,312 modules, including 2,524 source-checked modules, with no lost steps, worker recovery, save failure or corrupt read.
The release build succeeded and the checkpoint test filter passed all 13 tests.
Their exact logs, original reports and source inventories are retained in `build`, `target`, `regression`, `critical` and `full`.

The accepted whole run exited 0 and completed all 107 CLI scopes successfully in 1,213.663 seconds.
It reported one checkpoint resume, zero worker recoveries, zero save failures and zero corrupt cache reads.
Peak RSS was 11,684,868 KiB and peak virtual memory was 14,836,948 KiB.
All 13,179 loader input files match the immutable snapshot, checked Git commit and reconciled checkout.
The 184 checker input files match the successful release build.
[Source reconciliation](source-reconciliation.json) also verifies unchanged library/checker Git trees and equality of the D01 package with the independently reviewed mathematical commit `d80c1ac5ac08d5553f2f00adab75754c047e4b03`.

The `full` directory contains the accepted aggregate and exact original worker reports.
The `full-progress` and `full-15g-progress` directories retain historical incomplete observations; they do not establish aggregate acceptance.
The [independent review](../preintegration/independent-review.md) found no material findings.

The focused and aggregate commands were:

```sh
python3 scripts/check_all.py libs/geometry/bundle_connections --initial-memory-mib 6144 --memory-mib 12288 --cache-budget-mib 16384 --cache-dir libs/refcache --state-dir work/d01-recovery/target
python3 scripts/check_all.py libs/geometry/smooth_bundles --initial-memory-mib 6144 --memory-mib 12288 --cache-budget-mib 16384 --cache-dir libs/refcache --state-dir work/d01-recovery/regression
REF_TYPE_GRAPH_SPILL_DIR=/tmp python3 scripts/check_all.py --initial-memory-mib 15360 --memory-mib 15360 --cache-budget-mib 16384 --cache-dir libs/refcache --state-dir work/d01-recovery/full-15g
```

The selected K11 case used its saved source snapshot:

```sh
target/release/cli libs/topology/k_theory_thom --parse-only --save-source-snapshot work/d01-recovery/critical-source.json --no-progress
REF_TYPE_GRAPH_SPILL_DIR=/tmp target/release/cli libs/topology/k_theory_thom --source-snapshot work/d01-recovery/critical-source.json --module k_theory_thom.Thom.Complexification.Compact.Isomorphism --memory-mib 15360 --checkpoint-seconds 120 --cache-budget-mib 16384 --cache-dir libs/refcache --report-json work/d01-recovery/critical.json --no-progress --diagnostics compact
```
