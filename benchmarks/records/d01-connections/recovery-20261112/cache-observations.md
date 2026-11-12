# Cache recovery observations

The configured proof cache is `/workspace/ref-type/libs/refcache`.
Recovery has not deleted that directory or used `--full-check`.
The original process, temporary reports and source snapshots were absent when the environment reconnected with clean branch `work` at `d2232bb8`.
The cache directory was not inventoried before the first recovery check, so whether its previous contents survived, reset or were partly retained is unknown.
The saved environment name alone does not establish persistent runtime storage.
An installed toolchain or prebuilt executable does not establish a compatible proof-cache baseline.

## Identities

- Restored implementation checkpoint: `fb2b41072ca46e07df27da4c40907fa203d56a10`, including main `fa5ced0f3cbfa8d39244035a0578e768c9c34dba`.
- Unchanged D01 source tree: `a455cebf64748ecca2c01f50ca821375f473d2d5`; manifest blob: `085b853133a8e004e720cb649a9d271d21ed950a`.
- Preintegration dependency snapshot SHA-256: `d49b8d741fc4ad95282d79a16b9f3a84c9f3b8a1712a8239de1d6e4ba93e572a`.
- Recovery target dependency snapshot SHA-256: `b87b5e069d0170fa7dab2d3b9b8c74b2e82889f6d513c8fb1012f1c644d67911`.
- Preintegration binary SHA-256: `0453660b63f512331fe449591f06fce96363311c149441c4eaaedb1e1090623b`.
- Previous main-integrated binary SHA-256, observed before the lost runtime: `2ee485fe5317655b5f7710d0d2b4c6d3758fed32860c7530e68f73dcaff1e5e0`.
- Recovery binary SHA-256: `5a9b8819402305b8004985f9ef6367f6e502293b90a11a9c0e9e80889d219b32`.
- Recovery `REF_SEMA_REVISION`, read from the existing release build output: `51b6375fd57db2a1d95189a0d7dc0399e259c39bb38aee441b754fc0a6b3ba4b`.

The main integration changed checker source in `src/elaboration/src/package.rs` as well as the workspace dependency graph.
`src/sema/build.rs` derives the cache revision from normalized runtime Rust source, Cargo inputs, compiler identity and compilation settings.
`src/sema/src/package_inputs.rs` combines this revision with configuration, package instance, manifest and source content digests, and dependency fingerprints.
Binary SHA inequality alone does not establish cache-key inequality, and the lost runtime's cache revision was not retained for direct comparison.
Consequently, the cause of the recovery target's cache misses cannot be distinguished between absent artifacts and incompatible inputs from the available records.

## Observed reuse

| Run | Accepted modules | Newly checked | Reused | Evidence |
| --- | ---: | ---: | ---: | --- |
| Preintegration D01 | 4,022 | 278 | 3,744 | `../preintegration/target-normal.json` |
| Preintegration B07 | 3,524 | 0 | 3,524 | `../preintegration/regression-normal.json` |
| Previous main-integrated D01 | 4,022 | 4,022 | 0 | Transcript observation; local reports lost |
| Previous main-integrated B07 | 3,524 | 0 | 3,524 | Transcript observation; local reports lost |
| Recovery D01 | 4,022 | 4,022 | 0 | `target/summary.json` and compressed original reports |
| Recovery B07 | 3,524 | 0 | 3,524 | `regression/summary.json` and compressed original reports |

The B07 recovery counters demonstrate reuse of compatible cache in this runtime.
They do not identify whether those artifacts came from an initial environment seed or the immediately preceding D01 dependency check.
The earlier partial whole-repository coverage, including the last observation of 10,891/14,486 before disconnection, is not aggregate acceptance.
The missing fixed-source verification is rerun through the normal driver, which validates cache inputs and checks misses.
No additional checker run was launched to answer the cache-reuse question.
