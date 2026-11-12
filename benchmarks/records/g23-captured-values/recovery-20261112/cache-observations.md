# Measured cache reuse after recovery

The existing `/workspace/ref-type/libs/refcache` directory was retained.
The normal loader validates checker revision, configuration, package manifests, source contents and dependency fingerprints.
No cache directory was deleted and no `--full-check` was used.

The reconnected environment had a clean initial checkout at `d2232bb8` and about 6.9 GiB of logical cache data.
The previous G23 worker, working reports and checkpoint inventories were absent.
Available initial debug build outputs recorded revisions `0d0dc195c07adda521c6381775b17e9c3f526044c3131b538ae639bd09454234` and `b6c65c4b66f98e531dfa31b30c81748f5da54d5421a60fd8b7db6ed1e4318c39`.
The recovered release build records `REF_SEMA_REVISION=2a498ffc965f28c34daf5ee1c8a7a7c6ded79dcf4e1c3d2683337be2640374db`.
Build outputs alone do not identify the revision or origin of every cache artifact.
The lost runtime's cache revision was not observed, so binary SHA inequality alone does not establish whether those old cache keys matched.

At the first saved prefix, the driver had verified 1,171 targets, all newly checked and zero reused targets.
At the 4,506-target prefix, all 4,506 target paths had been newly checked at least once.
Across the 41 completed CLI scopes at that point, storage reported 12,840 result hits, 5,242 missing operations, zero input mismatches, zero format misses, zero corrupt reads and zero save failures.
The exact original worker reports for this observation are preserved by commit `d927b5a65` in `full-progress/workers.raw.json.gz`.
These storage-operation counts demonstrate reuse of validated dependencies within the surviving run; they are distinct from the driver's sets of newly checked and reused target paths.
They do not identify whether a hit originated in the initial seed or an earlier scope of this run.
The aggregate itself supplies these observations; an extra checker run was not started to measure cache behavior.
