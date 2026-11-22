# Normal library verification

The baseline checkout and fetched `origin/main` both pointed to `269f97c3cac78ecd6c94fab02f71f9c50aee50e7`.
`cargo +1.100.0 build --locked --release -p cli` produced SHA-256 `49569d26de5581c34705abde75587256b7c26353bae4a953154fc5cff067d430`.
Running that executable on `libs/std --module std.Data.Nat --cache-dir libs/refcache --cache-stats --no-progress` verified 101 modules through 101 disk result hits, with zero new checks, corrupt objects or save failures.
The checker revision was `65cf880e493c8a420023d5ab5d710ec38bf6f1738e91f617f71e696f5e6c4a61`.

## Representative checks

Both release executables use the same native checker revision. The candidate CLI SHA-256 is `f893943378efadafd648dd6fb72817f85206b654e028ec79cbc1d00135d661fe`.
The driver SHA-256 is `66c471c3e6afcc059fbd89f49226e6c8e8c029a34984f23774d90ca6d3ce64e4` for both runs.

The driver checked a fixed-path copy of `libs/algebra/characteristic_series` and its dependencies in the `std`, `algebra`, `characteristic_series` scope order.
One normal baseline run prepared the native module cache. Each timed invocation received a separate copy of that cache and an empty state directory.
The edit appended `\definition quadraticAgain: Plane.SymmetricPolynomial := quadratic;` to `src/Examples.ref` in the fixture.
The resource and split arguments were those of the full run below. Each cell is one wall-clock measurement on the same 4-CPU, 16-GiB cgroup.

| Input | Verified | Newly checked / reused | Source steps | Baseline s | Candidate s | Baseline / candidate peak RSS MiB |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Unchanged | 426 | 0 / 426 | 0 | 6.556 | 5.430 | 209 / 218 |
| One added definition | 426 | 28 / 398 | 14,573 | 41.918 | 38.114 | 741 / 745 |

In both comparisons the baseline query parsed 242, 304 and 332 files across the three scopes after the supervisor had already parsed them.
The candidate query reused those same parses from the required selection preflight. An out-of-scope syntax error in a second module still made both executables exit 1.

A baseline probe of `cohomology_thom.LocalDisk.On.Projection` stopped at its 100 s worker limit with 3,933 completed source steps, zero duplicate steps, 208 disk result hits, 100.1 MB of environment reads and 13.8 s of relocation. Cost profiling and a concurrent build affected its duration. This diagnostic run contributed no accepted targets.
The two largest #87 workers peaked at 12.68 and 13.05 GiB RSS on their own, so the measured runs kept scopes sequential.

## Full command

```sh
export REF_TYPE_GRAPH_RESIDENT_MIB=2048
python3 scripts/check_all.py libs --binary "$CLI" --state-dir "$FRESH_STATE" --cache-dir "$CACHE" \
  --memory-mib 0 --cache-budget-mib 16384 --checkpoint-seconds 1800 \
  --min-free-mib 1024 --max-scope-targets 1024 \
  --split-package cohomology_thom --split-package k_theory_thom \
  --split-package relative_k_theory --split-package clutching_linearization \
  --split-package compact_support_k --split-package periodic_k_theory \
  --split-package topological_k_theory --split-package bott_product
```

The new invocation had an empty state directory and used a private copy of `libs/refcache` after startup probes. The supplied store measured about 15 GiB before first use. After normal CLI store maintenance, its copy occupied 3,914,137,600 allocated bytes at full-run startup.
The cache contents at the beginning of #87 are unavailable. The full source snapshot SHA-256 matched #87 exactly (`c0109ba4b1624908b91f48006447c5c482a19c23f7d2022ce15127e0307d6202`).

## Full run stopped during the final scope

The driver recorded `interrupted` at 22,165.842 s after a requested SIGTERM. It accepted 111 scopes covering 14,900 of 15,750 targets, with 11,393 newly checked and 3,507 reused. The remaining 850 targets were in `k_theory_thom`. The final source validation was still pending. #87 completed 112 scopes in 18,745.503 s with 11,085 newly checked and 4,665 reused. The source snapshot and ordered targets matched, but the starting cache contents differed. Whole-library speedup is unproven and the interrupted run exceeded the 4,686 s goal.

| Worker scope | #87 s | Candidate s | #87 / candidate checked modules | #87 / candidate source steps |
| --- | ---: | ---: | ---: | ---: |
| cohomology_thom | 5,905.1 | 11,269.7 | 285 / 1,638 | 3,651 / 21,085 |
| periodic_k_theory | 1,482.7 | 2,030.8 | 198 / 196 | 3,081 / 3,058 |
| compact_support_k | 1,617.0 | 2,029.7 | 415 / 412 | 4,858 / 4,841 |
| k_theory_thom | 5,470.0 | interrupted | 1,090 / incomplete | 15,061 / incomplete |

Across the accepted scopes, workers used 19,481.5 CPU s for 20,135.1 worker wall s. They reported 267,916 source steps with zero within-worker duplicates, but 20,604 module checks for 11,393 distinct modules. Environment reads totaled 11.31 GB, relocation 396.6 s and graph page loads 25.53 GB. The driver recorded zero recoveries, corrupt reads or save failures for the accepted scopes.

The process tree reached 12.98 GiB RSS and the cgroup, including filesystem cache, reached 16.00 GiB. Free disk space fell by up to 25.49 GiB from startup and remained at least 28.46 GiB. These peaks were sampled every two seconds through interruption. The final cache occupied 12.11 GiB on disk.

In `cohomology_thom`, the worker attributed 1,302 s to `ModTwoProduct.At.Refine` and 923 s to `IntegralProduct.At.Refine`. Both also occurred in the #87 checked-module list. Its last started module was `cohomology_thom.FamilySuspension.Slice.With.At` and its last saved checkpoint was 35,421 steps. A live event read confirmed declaration position 35,067 succeeded. The temporary event stream had already been removed when the final declaration was requested, and the retained report does not identify that declaration.

At the stop request, the `k_theory_thom` event stream showed `k_theory_thom.Thom.Isomorphism.ExternalLine` started, declaration position 43,220 succeeded and the latest saved checkpoint was 39,136 steps. Its 528 check events and 2,621 skip events are excluded from the accepted totals.

### Saved run

The Cloud workspace retains the CLI, cache, driver state, scope logs and a copy of the final scope's events outside Git in `/workspace/ref-type-perf88/`. The run's original paths remain under `/tmp/refperf/`. For continuation in this environment, the full command above uses `CLI=/workspace/ref-type-perf88/cli`, `FRESH_STATE=/tmp/refperf/validation`, and `CACHE=/tmp/refperf/final-cache`. Append `--resume-report /tmp/refperf/validation/20261122T030405.608249Z/report.json` to reuse the 111 accepted reports from this exact binary and snapshot. If temporary storage is restored separately, restore the saved `validation` and `final-cache` directories at those original paths first. A resumed run has inherited coverage and is a separate measurement.
