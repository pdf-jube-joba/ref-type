# A08 verification checkpoint — aggregate pending

Mathematical sources are fixed at `d31bbdcca2f80142bd4f6f4635a85f5ffa829d0d`.
This evidence-only checkpoint does not change those sources.

The release build passed. The final focused check accepted all 121 new modules and a 1,611-module dependency closure; Lp, change-of-variables and smooth-partition regressions passed. Their full reports and the build log are retained here.

The initial aggregate accepted 13,283 of 13,915 targets before the 12 GiB virtual-memory limit stopped existing `k_theory_thom.Thom.Complexification.Compact.Isomorphism`. It had zero save failures. Its full driver report, target list, source hashes and aliases are retained. This is **not** aggregate acceptance.

A normal cached targeted retry at 14 GiB is ongoing and has advanced through saved checkpoints. The final aggregate result and complete evidence will replace this provisional record when verification finishes. Draft PR #78 remains unmerged.
