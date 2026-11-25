# Checker benchmarks

This directory contains fixed inputs for end-to-end CLI measurements.
[cases.toml](cases.toml) defines case names, descriptions, and default time limits using input paths relative to this directory.

The measured CLI loads the input, resolves names, checks declarations, and writes its public JSON report.

| Case | Workload |
| --- | --- |
| [shared-bodies](shared-bodies.ref) | Nested functions taking structures, measuring sharing of definition bodies and arguments |
| [type-conversion](type-conversion.ref) | Independently defined type families, measuring definition unfolding, beta reduction, and type conversion |
| [type-inference](type-inference.ref) | Nested polymorphic applications with omitted types, measuring contextual inference and constraint solving |

Run from the repository root:

```sh
cargo build -p cli --release --locked
python3 benchmarks/bench.py case shared-bodies --binary target/release/cli --runs 3
python3 benchmarks/bench.py case type-conversion --binary target/release/cli --runs 3
python3 benchmarks/bench.py case type-inference --binary target/release/cli --runs 3
```

Named checker cases default to disabled caching.
Use `--cache-mode cold` to include persistence with an empty cache per run, or `--cache-mode shared` to reuse a cache between repetitions.
See the [shared options](../README.md) for resource limits, profiling, and reports.

## Type conversion

`Direct0 A` is the function type `A -> A`.
`ViaBeta0 A` defines the same type through a lambda application.
Each successive level composes its previous type constructor with itself, doubling composition depth.
The input contains levels 0 through 8 and checks conversions in both directions at levels 4 and 8.
All annotations and arguments are explicit, so this case exercises conversion without inference holes.

```sh
python3 benchmarks/bench.py case type-conversion --binary target/release/cli \
  --profile-costs kernel.erased_convertible,kernel.conversion-pair,kernel.beta-head
```

## Type inference

`select24` accepts 24 distinct types and one value of each type, returning the first value.
Its lambda binder annotations are inferred from the declared type.
Nested `keepLeft` and `identity` applications omit their polymorphic type arguments, requiring fresh holes to be solved in the local context.
The distinct types prevent the workload from reducing to inference of a single shared carrier.

```sh
python3 benchmarks/bench.py case type-inference --binary target/release/cli \
  --profile-costs kernel.meta
```

Inspect call counts and exclusive times when profiling these cases.
Inclusive totals for recursive scopes contain overlapping nested work and can exceed total elapsed time.
Profiling adds overhead; run ordinary timing repetitions separately.
