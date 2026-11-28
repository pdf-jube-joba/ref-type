# Standalone checker workloads

From a checker checkout, build the CLI and run all eight families with the quick preset. The runner generates every source and manifest in a fresh temporary directory using Python's standard library. It uses the ordinary checker CLI and its public JSON report. An empty checker checkout's cache is sufficient.

```sh
cargo build --release --locked -p cli
python3 benchmarks/bench.py workloads --binary target/release/cli
python3 benchmarks/bench.py workloads --preset stress --binary target/release/cli --runs 3
python3 benchmarks/bench.py workloads --families witnesses transport --sizes 8 16 32 \
  --binary target/release/cli --profile-costs
```

Quick runs sizes 8 and 32 once, for 20 invocations. Stress uses the larger sizes below. Override either preset with `--sizes`. Every repetition starts with fresh sources and its own cache conditions. The seven term families use one package with one source file and pass `--no-cache`. They measure the complete check, including startup, parsing, resolution, elaboration and the kernel. The last family uses one package spread across files.

## What to scale and observe

| Family | Size and measured operation | Stress sizes |
| --- | --- | --- |
| `transport` | Length of an equality path. A single proof nests identity eliminations, carrying one value through a type family over distinct endpoints. Measures checking under a growing dependent context. | 96, 160 |
| `constructor-equations` | Number of constructors. A case function rotates the tags. One reflexivity proof per tag requires conversion to reduce the application on that constructor. | 128, 256 |
| `program-binds` | Length of a single Program computation. Each bind forces a function and passes its result to the next bind. Exercises the Program bridge and checking of computation/value boundaries. | 96, 160 |
| `refinement` | Number of nested subset types. Each layer introduces a subset, constructs a member, and extracts its membership proof. A final coercion checks an inhabitant against the original carrier. Measures lowering and expression graph memory as depth and declarations grow together. | 48, 96 |
| `witnesses` | Number of existential eliminations in one proof block. Each witness supplies the argument for the next existence proof. The last witness is repackaged. Measures scope growth and kernel instantiation. | 48, 96 |
| `recursive-notation` | Number of operands in one variadic call. Token matching consumes the tail while accumulating a typed binary application. Measures source-time expansion in one file, with the resulting term checked. | 48, 96 |
| `step-motive` | Number of predicate/proof pairs. Each uses the built-in continue/finish eliminator with a result type that depends on the step. Measures motive checking across declarations. | 128, 256 |
| `focused-files` | Number of unselected external sibling files. The selected leaf and its root stay fixed. Measures source discovery and selection with different amounts of checking and persistent result I/O. | 128, 256 |

The focused sequence checks `--module sample.Focus --module-only` three times. **Cold** starts with an empty temporary checker cache. **Warm** repeats the identical command with the cache from cold. **Edit** changes the selected leaf's definition body, then runs the same command with that cache. Each phase launches a new process. The operating system's file cache is uncontrolled.

Each row requires an accepted version-2 report with exactly the generated root and target in `verified_modules`. Source and cold runs require both modules newly checked. An edit requires the edited leaf newly checked. Both kinds require positive source progress. A warm run requires verified reuse and zero newly checked modules. A failed prerequisite stops its focused sequence and fails the suite. Coverage failures are excluded from the timing summary.

Read `seconds`, user/system CPU time and process peak RSS in the harness report. For very short rows the supervisor's roughly 20 ms polling interval limits wall-time resolution. The CLI report also provides worker resource use, graph peak resident bytes and verification coverage. For cache runs, `cache_bytes` sums apparent file lengths **after** each invocation. For transient allocated disk usage use the existing checkpoint-disk axis. Profile separately from timing repetitions.

## Observations behind the fixtures

The research checkout used awase `bfe490287f85`, checker main `b2a1191c660f` and library revision `cef39a0a116c`. A source inventory across 14,186 library `.ref` files and bounded checks of individual modules informed the selection. For example, the text survey found 4,191 occurrences of `\idelim`, 6,647 of `\into`, 5,297 of `\takefrom` and 622 of `\bind`. These are spelling counts including comments. Only the measurements below used the library, during development.

The real profiles used the release CLI through `bench.py run PACKAGE --module NAME --seconds 20 --profile-costs --extra --module-only`. The cache was off except for the paired focused-file observation, which shared a new scratch cache for two repetitions. Every cited module was verified. Real counts include the target's prerequisites. Synthetic observations below compare one profiled quick run at 8 and 32. Call counts and timings describe this revision and are recorded for interpretation only.

| Family | Real module and characteristic | Evidence in the generated fixture (8 → 32) |
| --- | --- | --- |
| Transport | `std.Logic.Equality.Transport` contains dependent cast composition and naturality proofs. Its 13 source steps incurred 59,547 `kernel.infer_open` calls. | 447 → 3,207 inference calls with three source steps at both sizes. This isolates increasing term work inside one proof. |
| Constructor equations | `std.Data.Option.Prop` proves equations for functions on known constructors by reflexivity. Its check recorded 103 `kernel.eliminate` calls. | 8 → 32 elimination calls, one per generated constructor equation. The library uses small datatypes. Wide datatype scaling was measured only on generated inputs. |
| Program binds | `std.Data.Nat.Parity.Program` chains three and four binds in its two parity computations. Its check recorded 1,131 `bridge.program` calls. | 21 → 69 Program bridge calls with four source steps at both sizes. |
| Refinement | `std.Set.FiniteSubset.Family` refines an already refined finite-subset carrier and recovers its predicate with `\bysub`. The check reached 2,050,496 graph-resident bytes. | Graph peak rose from 172,960 to 249,760 bytes, and source steps from 36 to 132. The share of real-module memory attributable to refinement depth was not isolated. |
| Witnesses | The successor proof in `std.Set.Countability.FinitePowers` extracts head, rest and code witnesses. Its check recorded 47,442 `kernel.instantiate` calls. | 36 → 528 instantiations with three source steps at both sizes. The generated chain exercises context growth. The real proof also contains induction and equality reasoning, so its witness-specific scaling is unverified. |
| Recursive notation | `category.Functor` uses recursive equality reasoning and congruence notation inside composition laws. The focused check spent 2,367 µs in `resolve.macro-expansion`. | Expansion took 275 → 2,344 µs across five measured scopes at each size. The accumulating macro stays local, and both generated terms verified. These single-sample times illustrate where to profile. |
| Step motive | `std.Logic.Termination` defines readiness over run steps and maps a proof into the corresponding result for each branch. Its check recorded nine `kernel.motive_type` calls. | 16 → 64 motive checks with zero `kernel.eliminate` calls in both runs, separating this operation from constructor-equation reduction. |
| Focused files | Cold and warm `std.Logic.Equality.Prop` both parsed 242 files and verified four modules. Source steps fell from 10 to zero with a package hit on the repeat. | Both cold and warm parsed 10 → 34 files and verified the same two modules. Cold and edit took three source steps at each size, warm took zero. The real module was left unedited, so only synthetic edit behavior was verified. |

The profiles establish shared operations and a few useful differences in cost. Real-library scaling curves and whole-library peak memory were not measured. No library timing or internal counter is a pass/fail threshold.
