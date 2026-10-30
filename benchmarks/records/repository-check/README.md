# Repository-wide normal checking

Base main: `778ba03340cbc9547195aea47ef351f3d7d0a20b`.
Implementation: `8be7168f6` (CLI reporting, bounded driver, prefix selection, import identity fix in `672404eeb`).
The mathematical library sources are unchanged.

## Environment and baseline

Linux x86_64, Rust 1.95.0 release, cgroup memory limit 16 GiB, CPU quota 4 cores, disk about 32 GB; inherited virtual-memory limit unlimited.
The managed shell initially has no Cargo on PATH. Both measured command invocations source the saved toolchain setup in the same shell before building and checking:

```sh
source /workspace/ref-type-env.sh && cargo build -p cli --release --locked && python3 scripts/check_all.py
```

The setup file belongs to this execution environment; on a usual development machine, use the README command from a shell with Cargo on PATH.
Workers initially use 4608 MiB virtual memory. Checkpoint recovery and scope splitting precede any larger retry; an indivisible scope may retry up to the explicit 6144 MiB hard ceiling.
The initial single-worker baseline used 3072 MiB.
The original single-worker whole-workspace query failed at a 3072 MiB virtual-memory limit after 921.48 s, with one checkpoint recovery, peak RSS 2,926,984 KiB and virtual memory 3,140,384 KiB.
There were no cache save failures or cgroup OOM events.
This run overlapped compilation and is diagnostic evidence, not an isolated wall-time comparison.
See [baseline.json](baseline.json).

The baseline parsed the whole workspace (about 1.2 GiB RSS before restoring checking state).
The bounded driver instead loads each package's dependency closure from one fixed repository snapshot, then releases the process between scopes.
A diagnostic run reached 4,526 verified targets but homological_algebra still hit its virtual-memory ceiling after checkpoint recovery.
Even narrower scopes restored 1,043 irrelevant modules alongside 994 wanted modules.
The prefix selector now ranks net useful coverage and rejects a prefix when irrelevant coverage exceeds useful coverage.
This changes cache compatibility, so old caches are preserved but not trusted by the new checker.
The exploratory before/after module data in [homological-diagnostic.json](homological-diagnostic.json) used different cache histories and is not an isolated timing comparison.

## Isolated prefix comparison

Both binaries check identical sources: the repository's std library and a tiny consumer of its conjunction projection.
Each binary first checks all of std into a separate empty cache; three independent copies of that seed are then used for the consumer.
No other compiler or checker workload ran concurrently.
All seed and consumer runs succeeded using normal checking.
The before binary contains the new reporting code but the original prefix-selection logic.

| Consumer measurement | Before | After |
| --- | ---: | ---: |
| Median seconds, 3 runs | 1.050 | 0.529 |
| Maximum sampled RSS, KiB | 162,508 | 84,116 |

This workload measures prefix restoration; it does not estimate the speedup for every mathematical package.
Raw timings, binary hashes, checker statistics and source digest are in [prefix-comparison.json](prefix-comparison.json).
Reproduce from the repository root with release binaries and a new work directory:

```sh
python3 benchmarks/repository_prefix.py --before /path/to/before-cli --after target/release/cli --work-dir work/prefix-comparison
```

## Isolated scope comparison

Both binaries normally check the same `std` sources with three independent empty caches and a 3072 MiB worker limit.
The main binary loads the whole workspace to select `std`; the final binary loads the `std` package, as the new driver does.
No other compiler or checker workload ran concurrently.
All six checks succeeded.

| Measurement | Main workspace query | Final package query |
| --- | ---: | ---: |
| Median seconds, 3 runs | 26.743 | 6.690 |
| Maximum sampled RSS, KiB | 1,376,932 | 277,580 |

This isolates the cost of loading unrelated packages; it is not a claimed whole-library speedup.
See [scope-comparison.json](scope-comparison.json).
Reproduce with `python3 benchmarks/repository_scopes.py --before /path/to/main-cli --work-dir work/scope-comparison`.

## Import identity during recovery

An exploratory whole run verified 7,196 targets, then rejected `singular_cap.Integral.Pair.CochainConnecting.PositiveZeroClasses` at the `NaturalCochain` import.
The subspace cochain complex was incorrectly given a differential for the whole space.
The same sources passed a normal cold singleton check and an uninterrupted normal whole-package check.
Replaying the saved checkpoint reproduced the rejection after 15 checking steps, even with 6 GiB virtual memory.

The later temporary imports carried composed maps containing an earlier `SubTheory` alias.
Registering those maps overwrote its established typed image with another argument telescope.
The fix preserves established images for inherited aliases while registering the explicit current import target.
The original failure path passed after the fix; the diagnostic continued beyond position 19,500 and was deliberately stopped before running the standard driver.
This diagnostic is not counted as full validation.
See [checkpoint-fix.json](checkpoint-fix.json).

## Failure and recovery verification

`scripts/test_check_all.py` covers cold and warm normal checks, dependency invalidation, corrupt-object recovery, source mutation during a run, interrupted-driver resume, unusable checkpoint storage, insufficient disk reserve, and finite failure under an impossible memory budget.
The explicit no-progress case starts one worker and performs zero recoveries when no new checkpoint was saved.
`benchmarks/bench.py cache --depth 8 --checkpoint` also exercises checkpoint interruption, worker-kill recovery, and a distinct storage-failure outcome.
Rust workspace tests, clippy with warnings denied, and the 401 language test cases passed.

## Indivisible dependency environment

The first run with the import identity fix newly verified 7,962 of 9,799 targets in 6,262.35 s, then stopped at `singular_finite_algebra.Integer.Product.Factors.Signed.At`.
All cache saves succeeded.
Its selected dependency environment alone exceeded the 3 GiB virtual-memory budget; reducing the requested scope further was impossible.
A repeated normal singleton check reproduced that failure.
With the same sources, binary and dependency cache, a 6144 MiB ceiling allowed normal completion: actual peak RSS 2,986,504 KiB, virtual memory 3,697,160 KiB, 982 newly checked steps, and no recovery or save failure.
This establishes a required resource envelope, not a speed comparison.
See [three-gib-full.json](three-gib-full.json) and [indivisible-scope.json](indivisible-scope.json).

The driver first introduced 3072 MiB initial workers and smaller scopes, then strictly increasing retries for indivisible scopes bounded by `--memory-mib`.
The nine end-to-end driver tests include recovery from a deliberately small initial worker within a fixed hard maximum.
Obsolete Cargo incremental directories and older test executables generated during this task were removed in five recorded batches to recover disk headroom.
Normal checking caches and diagnostic evidence were retained.
The removed-path inventories are saved locally in `work/full-check/removed-build-intermediates*.json` and `removed-old-test-executables.json`.

## Large shared cache leases

The subsequent run was deliberately interrupted after 8,160 verified targets to address a recovery bottleneck in `singular_cellular`.
A resumed worker remained in the cache phase with low RSS and high system CPU (sample: 82.96 s user, 315.01 s system); its live protection file was displayed as 17 MiB.
The old reader parsed JSON directly from `File`, issuing tiny reads, and applied the 16 MiB single-manifest limit to a lease covering many manifests.
The writer did not enforce that limit, so a published lease could become unreadable on recovery; independent cache lookups could repeat the failed read.

Leases now use compact fingerprint encoding and bulk reads, retain compatibility with live legacy JSON leases, and apply the same 64 MiB bound on publication, recovery and collection.
A large-lease regression test restores all 180,000 protection entries from both encodings, verifies a protected object survives collection, and verifies a corrupt live lease is reported and prevents collection.
Type-checking results and environment integrity validation remain unchanged; the implementation fingerprint conservatively invalidates previous verification receipts.

A standalone comparison decodes the same 8,000 fingerprints three times per method and compares every resulting protection set with the original.
Median decoding time: unbuffered JSON 0.257681 s, bulk JSON 0.005318 s, compact encoding 0.001102 s.
Payload size: 930,201 to 256,005 bytes.
This is a decoder comparison, not a claimed whole-library speedup.
See [lease-comparison.json](lease-comparison.json); reproduce with `python3 benchmarks/repository_leases.py --work-dir work/lease-comparison` after a release build with the same Rust toolchain.

## Measured initial worker budget

The compact-lease binary with 3072 MiB initial workers newly verified 9,224 targets before a deliberate interruption (exit 130), with no save failure.
Forty initial memory-limit attempts consumed 3,952.68 s; seventeen accepted retries under the 6144 MiB ceiling used at most 4,221,476 KiB (about 4.03 GiB) virtual memory.
The standard driver therefore starts at 4608 MiB, keeping the 6144 MiB hard ceiling and smaller-scope recovery.
This avoids repeatedly trying a measured insufficient budget. The interpreter and mathematical sources are unchanged, so compatible normal-checking receipts remain reusable.
The interrupted run is diagnostic evidence, not a full success or a controlled before/after wall-time comparison; see [three-gib-compact-partial.json](three-gib-compact-partial.json).
The driver tests passed again (9 tests, 27.134 s).

## Full validation

The standard command completed with exit 0 at implementation commit `8be7168f66c5cd51e5e7b340ec231dc5805c99ed`.
Its release binary SHA256 is `1705b9673bcc10f77ab46d9f4f6875b53ad5615b44706343bb45aa1dc4dc24e3`.
The final target set exactly equals the 9,799 enumerated targets, and the final source snapshot equals the starting snapshot.
No mathematical source, definition, theorem or proof was changed.

| Measurement | Successful full command | Exact repeat |
| --- | ---: | ---: |
| Targets verified | 9,799 / 9,799 | 9,799 / 9,799 |
| Newly checked / reused | 1,527 / 8,272 | 4,577 / 5,222 |
| Checking seconds | 9,490.979 | 2,778.871 |
| Command seconds including build | 9,642 | 2,915 |
| Peak single-process RSS, KiB | 5,412,832 | 4,462,412 |
| Peak single-process virtual memory, KiB | 6,259,460 | 4,710,624 |
| Cache logical bytes at completion | 12,868,509,884 | 12,806,779,660 |
| Cache allocated bytes at completion | 13,706,301,440 | 13,706,067,968 |
| Disk free bytes at completion | 2,367,328,256 | 2,193,227,776 |
| Worker recoveries | 20 | 4 |
| Cache save failures | 0 | 0 |
| Peak sampled descendant RSS sum, KiB | 6,000,708 | 4,638,832 |
| Peak sampled cache allocated bytes | 14,009,835,520 | 14,128,414,720 |
| Minimum sampled disk free bytes | 1,532,633,088 | 1,748,209,664 |

See [full-normal.json](full-normal.json) and [repeat-cache.json](repeat-cache.json) for per-attempt timings, outcomes, source and target digests, and raw evidence paths.
The cache contained compatible normal results from the preceding diagnostic run; this was not an empty-cache measurement.
Across that interrupted run and the successful invocation, all 9,799 distinct targets were newly normally checked with exactly the same source snapshot and interpreter binary.
The overlap was 952 targets (9,224 + 1,527 - 952 = 9,799); see [normal-coverage.json](normal-coverage.json).
The successful invocation independently validated coverage of every target.

The worker's virtual-memory ceiling and the 16 GiB container limit are distinct.
Sampled container usage approached 16 GiB with substantial filesystem cache and reclaimable slab; the container recorded memory-limit reclaim events but zero OOM or OOM-kill events.
Process and cache peaks are measured independently and should not be added as if simultaneous.
The cache budget is a collection target for logical data; filesystem allocation, temporary publications and live protection may use additional disk space.
The heaviest successful individual scope used nearly the 6 GiB virtual-memory ceiling.
Cache collection/publication near the disk budget remains a performance cost: `clutching_linearization` took 1,064.56 seconds but completed with no save failure.
No whole-repository before/after speedup is claimed because earlier failed or interrupted runs had different cache histories.

The exact same build/check command then completed again with exit 0 in 48 minutes 35 seconds, including the build (checking: 46 minutes 18.871 seconds).
Its source snapshot, target list and binary hash match the successful full invocation exactly.
The initial whole-workspace cache-validation attempt reached its memory limit, and the driver automatically fell back to bounded package and submodule checks.
All 9,799 targets were verified again: 4,577 newly checked and 5,222 reused, with no cache save failures or corrupt reads.
Cache collection and subsequent dependency checks can require normal rechecking, so this is a measured mixed reuse run, not a claim that every result remained resident.
The following documentation/measurement commit does not change the tested driver, interpreter or mathematical sources.
See [validation.json](validation.json) for the completed test and whole-repository validation summary.
