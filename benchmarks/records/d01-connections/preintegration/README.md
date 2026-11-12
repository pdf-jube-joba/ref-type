# D01 pre-integration verification and resource recovery

Mathematical source: `d80c1ac5ac08d5553f2f00adab75754c047e4b03`, based on main `60c8e1551`.

The release build succeeded. The package/dependency scope accepted all 4,022 targets; the B07 regression accepted all 3,524 targets. The full 14,169-target scope was interrupted with exit 130 after repeated memory limits in existing K11 code under a 12 GiB ceiling. It is not an aggregate pass. `full-normal.json` summarizes partial coverage, retries, lost steps and interruption data; `full-details.json.gz` preserves its exact original detailed report. The other normal summaries have corresponding exact compressed details too, identified by SHA-256.

The merged A08 record documents the same 12 GiB limitation in `k_theory_thom.Thom.Complexification.Compact.Isomorphism` and successful recovery with the checkpoint-cadence correction and a 15 GiB ceiling. This attempt was preserved before integrating that checker change and adopting its validated resource profile.

The compressed driver reports, per-attempt details and mathematical source hashes identify the checked scopes. The independent review found no material findings in D01. Subsequent runtime recovery and fixed-source verification are recorded in [the recovery directory](../recovery-20261112/README.md).
