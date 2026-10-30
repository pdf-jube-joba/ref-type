# G01 smooth partitions: normal checking

Base main: `5d213f86a635f17f309f058d929002e2840f393b`.
Checked mathematical source commit: `51799530317db36f73adc63a2d9b2aa743378414`.
Branch: `feat/g01-smooth-partitions`.
The subsequent record commit changes documentation and evidence only.

## Implementation

The new `smooth_partitions` package constructs the exponential from existing smooth ODE local solutions, flat functions and compactly supported Euclidean cutoffs.
It constructs countable smooth partitions subordinate to arbitrary open covers of second-countable Hausdorff manifolds, proves local finiteness of their supports and exposes open refinements and compact finite versions.
It also supplies zero extension for scalar functions and sections described by zero-preserving local fibre coordinates, smooth locally finite sums and all-order derivative vanishing off support.
Examples cover the real line, the zero-dimensional compact manifold and a section of its real line bundle.
No Rust sources or foundational axioms were added or changed.

## Commands and outcomes

The environment has a 16 GiB cgroup limit; workers use an initial and maximum virtual-memory limit of 10240 MiB.

```sh
source /workspace/ref-type-env.sh && cargo build -p cli --release --locked
python3 scripts/check_all.py libs/geometry/smooth_partitions --initial-memory-mib 10240 --memory-mib 10240 --state-dir work/g01-target-check
source /workspace/ref-type-env.sh && cargo build -p cli --release --locked && python3 scripts/check_all.py --initial-memory-mib 10240 --memory-mib 10240
```

| Check | Targets verified | Newly checked | Reused | Save failures | Corrupt reads |
| --- | ---: | ---: | ---: | ---: | ---: |
| Package and all dependencies | 1883 | 0 | 1883 | 0 | 0 |
| Whole repository | 10233 | 9538 | 695 | 0 | 0 |

Both runs were accepted by the normal-check driver.
Every CLI attempt in the whole-repository run returned exit code 0, and the accepted driver branch returns 0.
The driver confirmed source, target-list and checker identity at completion.
No cache deletion, unsafe cache mode or checking bypass was used.
Whole-repository elapsed time: 2347.567 seconds.
Peak reported RSS: 9129944 KiB; peak reported virtual memory: 10319144 KiB.
Checkpoint-cache resumes: 0; worker recoveries: 1.
The final `periodic_k_theory` worker reached its configured virtual-memory ceiling and failed a 285212688-byte allocation.
The CLI resumed from checkpoint 32644 and accepted the complete scope; the supervisor returned 0.
The volatile-step loss and recovery counters are preserved in [bounded-recovery.json](bounded-recovery.json).
All targets were subsequently verified, with zero save failures and corrupt reads.

Scope-specific checker/source hashes and exact counters are in [target-normal.json](target-normal.json) and [full-normal.json](full-normal.json).
Raw whole-repository evidence remains at `work/repository-check/20261030T230355.181413Z` in the execution environment, including the fixed source snapshot, target list and individual logs/reports.

## Language limitation

A no-cache minimal example of implicit eta expansion of a specialized module function rejects with a type mismatch; the explicit-lambda example succeeds with exit code 0.
Both examples are recorded in the final section of [gaps.md](../../../gaps.md).
The library uses a fixed-parameter helper module for this case and retains the same mathematical statements.

## Publication state

Implementation, proofs, documentation, examples, commits and normal checking are complete locally.
Push, GitHub PR creation, merge and environment republication have not been attempted; they remain pending the parent thread's authorization.
