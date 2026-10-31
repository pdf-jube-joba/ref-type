# G02 inverse and implicit function checking

Base main: `2799faf1f838aea89b6b78b9553a7e79918e52f4`.
Checked source commit: `a50deeea445cac703f5ad8f98a9c86e88bbf1827`.
Branch: `feat/g02-inverse-implicit`.
The subsequent evidence commit changes documentation and checking records only.

## Scope

The new package proves local inverse existence for smooth finite-dimensional maps by a contraction argument, the parameter-dependent implicit function theorem, constant rank normal form, local regular-fiber coordinates, and manifold regular-value submanifolds with tangent spaces identified with differential kernels.
Concrete checked examples include nonlinear shear, a quadratic implicit equation, a nonlinear map of rank one, the parabola regular fiber and its tangent kernel, and dimension zero.
The public input is the existing `calculus.Maps` smooth-map API; this record does not assert a separate API for maps with only one continuous derivative.
No Rust implementation or foundational axioms were added or changed.

## Commands

```sh
source /workspace/ref-type-env.sh
cargo build -p cli --release --locked
target/release/cli libs/geometry/inverse_implicit --module inverse_implicit --full-check-local --memory-mib 8192 --cache-stats --report-json /tmp/g02-target-final.json --diagnostics compact
target/release/cli libs/analysis/calculus --module calculus --memory-mib 8192 --cache-stats --report-json /tmp/g02-regression-calculus.json --diagnostics compact
target/release/cli libs/algebra/matrix_invariants --module matrix_invariants --memory-mib 8192 --cache-stats --report-json /tmp/g02-regression-matrix_invariants.json --diagnostics compact
target/release/cli libs/geometry/manifolds --module manifolds --memory-mib 8192 --cache-stats --report-json /tmp/g02-regression-manifolds.json --diagnostics compact
python3 scripts/check_all.py --initial-memory-mib 12288 --memory-mib 12288 --cache-budget-mib 12288 --min-free-mib 512 --state-dir /tmp/g02-full --cache-dir libs/refcache
```

The release build and each listed check returned exit code 0.
The full local target check rechecked all 89 new package modules and their 1,233 source steps.

| Check | Verified | Newly checked | Reused | Save failures | Corrupt reads |
| --- | ---: | ---: | ---: | ---: | ---: |
| inverse_implicit (full local) | 793 | 89 | 704 | 0 | 0 |
| calculus | 537 | 0 | 537 | 0 | 0 |
| matrix_invariants | 537 | 0 | 537 | 0 | 0 |
| manifolds | 628 | 0 | 628 | 0 | 0 |
| whole repository | 10493 | 128 | 10365 | 0 | 0 |

The whole-repository driver confirmed identical initial and final source snapshots, an unchanged checker binary and complete target coverage.
Source snapshot SHA-256: `ea7cbeeaf48125d355a5e482da1ab1076dddbb950f7a6b0c8ad3cefabb02313b`.
Checker SHA-256: `9085d59db69b0bd0eb01c85fbd8dc1a5c1eecd2320c842b08acbfe52ab92e6fe`.
Whole-repository elapsed time: 753.518 seconds.
Peak RSS: 9738188 KiB; peak virtual memory: 11559784 KiB.
Worker recoveries: 0; checkpoint resumes: 1.

The environment exposed about 18,007 MiB of total memory and 17,060 MiB available at startup; the hard worker ceiling was 12,288 MiB.
Existing cache contents were retained and checked through the normal validation path.

An initial run used `--initial-memory-mib 8192 --memory-mib 12288` and verified 10363 targets before the final `periodic_k_theory` worker repeatedly reached its 8 GiB ceiling.
Its failed allocation sizes were [67108864, 67108864] bytes and automatic checkpoint resumptions were [32688, 32702].
The run was deliberately interrupted with SIGINT (exit code 130), preserving caches, then restarted with an initial and maximum worker ceiling of 12 GiB.
The accepted run above revalidated every target through the normal cache path and confirmed the same source and checker identity.
The interrupted run remains at `/tmp/g02-full/20261031T072731.303861Z` and is recorded separately in `checks.json`.

[checks.json](checks.json) preserves counters, checker and source identity, execution details and per-attempt outcomes.
Raw source snapshots, exact targets and logs remain in `/tmp/g02-full/20261031T083323.437147Z` in the execution environment.

## Language workaround

The concrete structure-signature example documented in [gaps.md](../../../gaps.md) fails with exit code 1 when a parent module's dimension alias remains unspecialized.
The equivalent signature with the dimension expression written explicitly passes with exit code 0.
Both exact documentation snippets were checked with the normal CLI in a temporary package.
The mathematical assumptions and conclusions are unchanged by this syntactic workaround.
