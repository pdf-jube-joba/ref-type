# Checkpoint choice under memory pressure

Build both revisions with the same Rust toolchain and profile. Run on Linux with Python 3.11 or newer. The output directory must be new. Keep it outside Git.

```sh
cargo build --locked -p cli
python3 benchmarks/checkpoint-choice/run.py --binary target/debug/cli --output /tmp/checkpoint-choice-results
```

Repeat `--binary` to compare builds on the same source paths. The checker keys caches by build, so each binary creates its own seed. The ordinary workspace CLI is interrupted with SIGINT after the Heavy module's checkpoint. The fixture checks that the witness module has not started. All measured runs use independent copies of that binary's seed and pass the entire workspace once. Each accepted run must check the witness module, print its inferred type, and verify all six modules.

The fixture makes a large shared macro visible under many aliases, so expanding a saved environment into memory costs substantially more than the serialized size suggests. It includes 64 ordinary definitions before the interruption and a typed use of one of them in the final module. Each repetition runs with the inherited limits and with an explicit per-process address-space limit (80 MiB by default, adjust with `--as-mib`). Linux enforces RLIMIT_AS on the CLI and each worker. The checker report records peak worker RSS separately. Candidate decoded bytes sum the envelope and referenced graph payload lengths and measure serialized volume. Wall time covers the whole CLI and excludes preparing cache copies. The pressure control may legitimately report memory-limit. A successful pressure run must show a smaller prefix hit. See the JSON reports and logs beside summary.json for the individual observations.

## Recovery policy

On Linux the supervisor tracks the disk checkpoint object while the worker reads and validates its envelope and graph, deserializes the checker and reconnects sources. When the worker exits during that interval with the existing memory-limit classification (allocation abort or external SIGKILL), the supervisor omits that digest from later restores in this invocation and retries the original request. A candidate must still pass the usual checks. The normal ordering chooses the next eligible candidate, or the checker rebuilds from source. A cancelled or timed-out worker ends the invocation. Other invocations start with an empty exclusion set.

## Synthetic observations

Seven runs per cell, on Linux x86-64 with rustc 1.100.0, the repository dev profile and CARGO_PROFILE_DEV_DEBUG=0. Both binaries used the same generated workspace and interrupted position 70. The control is the benchmark-only commit ab6861939. Times and peak worker RSS are medians. Source steps and hits were identical across repetitions of each cell.

| Build and RLIMIT_AS | Accepted | Wall (s) | Worker RSS (MiB) | Source steps | Successful request / prefix restores |
| --- | ---: | ---: | ---: | ---: | ---: |
| Control, 80 MiB | 0/7 | 0.064 | 70.9 | 0 | 0 / 0 |
| Recovery, 80 MiB | 7/7 | 0.356 | 71.0 | 1,574 | 0 / 1 |
| Control, inherited | 7/7 | 0.548 | 251.6 | 1,507 | 1 / 0 |
| Recovery, inherited | 7/7 | 0.483 | 251.7 | 1,507 | 1 / 0 |

Under pressure, the first worker's allocator failed while restoring the request. The replacement restored the 2,852-byte prefix after the 954,571-byte request failed, performed 67 additional source steps relative to an exact resume and checked the fresh declaration app.Witness.newValue. Both byte counts include the envelope and the referenced graph payloads. Each ample-memory trial used one worker. The timing variation at ample memory does not establish a speedup.

## Matched real-data comparison on awase

Build the benchmark-only revision and the implementation with the same toolchain and profile. Before timing, use the prior awase log to choose one workspace member and its actual dependency closure containing a costly restore and a small compatible dependency prefix. Use a temporary workspace manifest with just that member. Freeze the manifest, source paths, libs revision, flags and checkpoint boundary for both builds. Select a named declaration in the next module that the seed has never started.

1. Budget 10 minutes per build to produce an interrupted seed at that boundary with the ordinary CLI. Confirm its last saved position and module. Make independent copies for each trial. Build fingerprints can differ, so reusing a seed requires an actual compatible build. Preserve the original awase cache.
2. Give each pressured run 12 minutes and use the same cgroup memory.max and swap setting for both. Use distinct cgroups with the same settings, record memory.peak and the memory.events deltas, and keep the supervisor alive when the worker is killed. Pass the same workspace to one CLI invocation with --report-json, --time-limit-seconds 720 and REF_TYPE_PROFILE_ENVIRONMENTS=1 and REF_TYPE_PROFILE_PROGRESS=1. Record attempted digests, accepted and rechecked steps, whole-command elapsed time, worker peak RSS, and whether the selected module finished from source. A worker SIGKILL alone does not establish a cgroup OOM.
3. Use up to five minutes per build for a second pair at ample memory. Stop a trial once the selected fresh module completes if full acceptance will exceed its budget. Record the stop as interrupted and retain the progress evidence. The four runs and two seed preparations have a combined 54-minute budget after compilation. Enforce a 55-minute outer deadline. If the seed misses the boundary or the imposed cap does not distinguish the routes, record the comparison as inconclusive.
