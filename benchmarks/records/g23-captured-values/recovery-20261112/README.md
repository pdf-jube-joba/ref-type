# G23 capture inference: recovered integration verification

The restored PR source was `3b1c4086a3784f0773f56ba97a53ba7121962347`.
Main `d9da7c0ace28ecab2cc83e8dcfef9258ee0235b4`, including merged D01, is integrated in `b52aa8afca2d251c845cd6580f32a15093dd088e`.
The integration has the same `src` tree as the previously reviewed G23 checker: `06c6742985407363110054c7266a6a85131e5805`.
Its tests, scripts and Cargo inputs are unchanged from that reviewed source.
Its `libs` tree equals main: `fda10f6db37f287d0de47458b4f76d34eb34603f`.

## Change and independent review

Captures containing implicit holes now share constraints on the entire inferred value.
Comparing copies of a lambda under its binders avoids the original per-hole identity scheme's incompatible local symbol identities.
Assignment wrappers preserve expected judgements and Program application-head classification.
The unifier also rolls back speculative application-congruence assignments when a comparison is blocked, before reducing a beta-redex whose application spine may differ.
The previously failing Gram equality chain and its smaller beta-unification reproduction are covered by source regressions.
Mathematical proofs were unchanged by G23.

The [independent review](independent-review.md) records the three discovered issues, their fixes, the exact reviewed source, previous observed execution results and the post-recovery static confirmation.
It found no remaining concrete blocking issue in the integrated checker.
The reviewer did not rerun an aggregate during recovery.

## Runtime recovery

After reconnection, the actual root checkout was clean at `d2232bb8ec5ff43feb2323477c8815b10ee309a8`.
The previous G23 worker processes, shared worktrees, local reports, snapshots and uncommitted records were absent.
The existing `/workspace/ref-type/libs/refcache` directory remained present with about 6.9 GiB of logical data.
It was preserved and is passed to the normal validating cache loader.
Its presence alone does not identify which artifacts survived or establish compatibility with this checker.
`cache-before-checks.json` records the observed initial state and available build revisions before mathematical checks.
Measured accepted-report cache hits and misses will establish actual reuse.

[Earlier transcript observations](observations-before-reset.json) distinguish observed historical results from unavailable original reports.
The old 8 GiB aggregate had accepted 12,924 of 14,111 targets before a virtual-memory limit in periodic K theory.
The unchanged checker accepted the limiting dependency closure at 12 GiB, peaking at 10,510,948 KiB virtual memory.
The subsequent 12 GiB aggregate was last observed running at 12,859 of 14,111 targets before the environment reset.
Neither historical aggregate establishes full acceptance.

## Recovery build and verification

The release build uses Rust `1.99.1 (58cf8f9c3 2026-10-13)` and locked offline dependencies.
The recovered checker SHA-256 is `cc0578470d23ba582931b065f1f1a68e9afe64068bf4e24e0a050f73eeb1845c`.
`checker-source-sha256.json.gz` retains hashes for all 198 checker and Cargo input files at the integrated source commit.
The immutable executable and working logs are under `/workspace/shared/g23-recovery`.
Fresh source tests passed all 412 cases and aggregate-driver fixtures passed all 9 cases.
Fresh Rust workspace tests passed 384 cases with no failed or ignored test.
Clippy with warnings denied and workspace formatting also passed.
`checks-summary.json` and `test-logs.json.gz` preserve the exact recovery results.
The final aggregate result is recorded with its exact reports when complete.

The full check adopts the already accepted A08/D01 15 GiB profile, including graph spill, from the current main's [D01 recovery record](../../d01-connections/recovery-20261112/README.md).
It retains normal validated caches and checks all 14,486 current library targets.

```sh
REF_TYPE_GRAPH_SPILL_DIR=/tmp python3 scripts/check_all.py --binary /workspace/shared/g23-recovery/checker-final --state-dir /workspace/shared/g23-recovery/full --cache-dir /workspace/ref-type/libs/refcache --initial-memory-mib 15360 --memory-mib 15360 --cache-budget-mib 16384
```

Only an accepted final driver report with complete target coverage and unchanged source/checker identities establishes full verification.

## Current-main resource recovery

The first recovered aggregate accepted 13,854 of 14,486 targets before the indivisible `k_theory_thom.Thom.Complexification.Compact.Isomorphism` scope reached its 15 GiB virtual-memory ceiling.
Its exact failed report and worker reports remain in `full-progress`; this is incomplete verification, not a type error or an aggregate pass.
The same checker and immutable scope snapshot accepted that dependency closure at 16 GiB with a 120-second checkpoint interval, preserving the existing cache.
The accepted critical report covers 3,312 modules and records 448 source steps, one worker recovery at checkpoint 49,519, 39 lost steps, zero duplicate/replayed source steps, zero save failures and zero corrupt reads.
The fresh process elapsed 770.356 seconds; peak RSS was 14,707,988 KiB and peak virtual memory 16,700,836 KiB.
The final aggregate resumes through the normal validating cache with a 16 GiB worker ceiling; only its successful full report establishes complete coverage.

The final driver was configured with a 16 GiB address-space ceiling.
After repeated bounded checkpoint-allocation failures, the running `Complexification` worker PID 29517 was adjusted through Linux `prlimit` to a 17 GiB soft address-space limit at `2026-11-13T00:10:09.919859Z`, without restarting the worker.
The physical cgroup ceiling remained 16 GiB, and the checker and immutable source snapshot were unchanged.
`address-space-adjustment.json` preserves the original and effective limits, exact worker request and process status.
The original driver report retains the configured 16 GiB value; it must be interpreted together with this recorded per-worker adjustment.
