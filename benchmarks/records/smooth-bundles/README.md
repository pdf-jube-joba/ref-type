# B07 smooth bundles: normal checking

Base main: `ed1af945bfdfdc1849bf1919317e3ce422b1ac1f`.
Mathematical source commit: `d7eb138f7991559a350164ed1b844b8ebec4aed6`.
Package tree: `961dd9d5d908ef3fedfaa0f060afd67a2a3a5100`.
Branch: `codex/b07-smooth-bundles`.
The subsequent record commit changes evidence only.

## Implementation

The new `smooth_bundles` package constructs real and complex smooth vector bundles, their total manifolds, smooth sections and fiberwise linear smooth maps, continuous forgetful bundles and complex realification.
It constructs dual, direct sum, tensor, alternating, exterior and column bundles, proves smooth positive definite metric existence using smooth partitions, builds frame manifolds as open subsets of column bundles and glues associated bundles through smooth representations.
The general linear groups have continuous and smooth matrix operations.
Frame bundles have actual local diffeomorphisms onto base-coordinate and GL products, a smooth action map on the product manifold, smooth projections and pairing, and proved action/transition correspondence and group-action laws.
Tangent and normal bundles are transferred to the general API, with the existing tangent comparison, normal direct sum splitting and stabilization diffeomorphisms.
Hermitian forms are conjugate linear in the first variable and linear in the second.
Examples exercise real and complex zero-rank bundles over a zero-dimensional base and the standard representations.
There are 185 source modules and 3903 source lines.
No Rust sources or foundational axioms were added or changed.
The only shared registration change is the package's own entry in `libs/ref.toml`.

## Checker and fixed inputs

```sh
source /workspace/.ref-type-tools/activate.sh && cargo build -p cli --release --locked --offline
python3 scripts/check_all.py libs/geometry/smooth_bundles --initial-memory-mib 10240 --memory-mib 10240 --cache-budget-mib 16384 --state-dir work/b07-target
python3 scripts/check_all.py libs/geometry/normal_bundles --initial-memory-mib 10240 --memory-mib 10240 --cache-budget-mib 16384 --state-dir work/b07-regression
python3 scripts/check_all.py --initial-memory-mib 12288 --memory-mib 12288 --cache-budget-mib 16384 --state-dir work/b07-full
```

The release build returned exit code 0 and reported 1m 10s.
The checker binary SHA256 is `e522fa32bb5fd5c74b077ec43108c80e7049694872d2373cc34bc50fe342d4d2`.
The Rust source matches the base main commit.
The environment has a 16 GiB cgroup memory limit and 4 CPUs; normal checks use one concurrent worker and a 16384 MiB cache budget.
The package and regression scopes use a 10240 MiB virtual-memory ceiling; the final whole-repository scope uses 12288 MiB.
All final checks ran with the same checker and mathematical source commit.
The driver saved the full source and dependency snapshot, enumerated every target, used normal cache verification, and confirmed source, target-list and checker identity again at completion.
Source snapshots differ between the package, regression and whole-repository scopes because their dependency closures differ; their exact SHA256 values and source-file counts are recorded separately.

## Accepted results

| Check | Verified | Newly checked | Reused | Exit | Save failures | Corrupt reads | Worker recoveries |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Package and dependencies | 3524 | 0 | 3524 | 0 | 0 | 0 | 0 |
| Normal-bundle regression | 1685 | 0 | 1685 | 0 | 0 | 0 | 0 |
| Whole repository | 11892 | 503 | 11389 | 0 | 0 | 0 | 1 |

All final driver runs returned exit code 0.
Every final CLI attempt was accepted and returned exit code 0.
The distinct target counts above include dependencies.
Per-attempt counts in the JSON records can overlap because individual package checks load their dependencies.

| Check | Elapsed seconds | Peak RSS (KiB) | Peak virtual memory (KiB) | Lost steps |
| --- | ---: | ---: | ---: | ---: |
| Package and dependencies | 50.378 | 614764 | 1069160 | 0 |
| Normal-bundle regression | 9.130 | 470156 | 1069060 | 0 |
| Whole repository | 1218.505 | 10413660 | 12424604 | 3202 |

[checker-build.json](checker-build.json) records the build and binary identity.
[target-normal.json](target-normal.json), [regression-normal.json](regression-normal.json) and [full-normal.json](full-normal.json) retain the exact source/checker/target-list/report hashes, target coverage counts, CLI exit codes, source-step counters and storage/recovery counters.
The repository's `libs/refcache` was retained throughout; no cache clear, unsafe verification mode or `--full-check` was used.
Normal verification checks cached results against their source and dependencies and checks any misses before accepting a scope.

## Development recovery

The complete package had passed a normal check before the final driver runs; the final package scope therefore reused its matching verified results.
During earlier Hermitian-form development, an omitted direct `dedekind_reals` dependency caused resolution to search unrelated dependency namespaces before reporting the missing package.
Two exploratory runs were interrupted with exit code 130 and two hit explicit time limits with exit code 2; another completed with a dependency-resolution rejection and exit code 1.
The manifest was corrected, the shared cache was kept, and the focused checks were rerun successfully.
Those exploratory attempts are not successful final verification evidence.
[development-recovery.json](development-recovery.json) preserves their exact outcomes, volatile-step losses, save failures and recovery counters.
The fixed final-source checks above independently validated all target results.

A first whole-repository run on the final source used a 10240 MiB virtual-memory ceiling.
The periodic K-theory worker failed a 536870912-byte allocation twice and resumed from checkpoints 32537 and 32552, with limited progress between restarts.
The driver was stopped with exit code 130, retaining 11490 verified targets and its caches, then rerun on identical source with one worker bounded to 12288 MiB inside the unchanged 16 GiB cgroup.
[resource-adjustment.json](resource-adjustment.json) records both automatic recoveries, the interrupted active worker, its exact replay/loss counters and the unchanged source/checker hashes.
The final accepted run separately revalidates all retained results and completes every target.

Within that final 12288 MiB run, the compact-support K-theory worker failed a 285212688-byte allocation and automatically resumed once from checkpoint 35573.
The replacement worker completed successfully; both its CLI attempt and the whole driver returned exit code 0, with no save failures or corrupt cache reads.
[bounded-recovery.json](bounded-recovery.json) preserves this final run's one recovery, 3202 lost volatile steps, exact allocation size, checkpoint, memory ceiling and raw-report/log hashes.
These counters are included in the accepted whole-repository totals above.

The previous whole-repository run on source commit `8994b6c37d501bc4831fa06da767aa7ea5524b95` was deliberately interrupted to add the native frame action and local-diffeomorphism bridge.
It verified 11340 of 11859 targets before interruption and returned exit code 130; it is not reported as successful whole-repository validation.
[interrupted-review.json](interrupted-review.json) records its exact source/checker hashes, accepted coverage, active worker and its 880 volatile steps lost on interruption.
The cache was retained and the final-source run above validated the retained results and completed the remaining coverage.

Raw fixed-source snapshots, target lists, individual CLI reports and logs remain in the execution environment at:

- `work/b07-target/20261104T170730.971872Z` (Package and dependencies).
- `work/b07-regression/20261104T170907.124648Z` (Normal-bundle regression).
- `work/b07-full/20261104T173159.190352Z` (Whole repository).
