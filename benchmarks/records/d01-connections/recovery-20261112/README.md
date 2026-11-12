# D01 verification recovery after runtime reset

Restored code: `fb2b41072ca46e07df27da4c40907fa203d56a10`, including main `fa5ced0f`.
The original clean `work` branch was preserved; recovery uses `math/d01-verification-recovery` in the existing environment.
D01's source tree is `a455cebf64748ecca2c01f50ca821375f473d2d5` and its manifest blob is `085b853133a8e004e720cb649a9d271d21ed950a`, identical to the durable checkpoint and independent review inputs.

The prior process, reports and snapshots were absent after reconnection, which returned a clean checkout at `d2232bb8`. Its last observed aggregate coverage was 10,891/14,486 and is not an aggregate pass. The prior observed focused successes are distinguished from the new durable reports here.

Each accepted stage retains its exact original report, worker reports, source hashes, loader aliases and comparison against both its recorded Git commit and current checkout. Progress checkpoints explicitly retain their original incomplete outcome. Only an accepted full driver report with complete target coverage establishes aggregate acceptance. `collect.py` checks these conditions; it does not create verification results.

Verification uses normal source-matched cache under `libs/refcache`, without deleting cache or using `--full-check`. Ordinary scopes use conservative memory bounds; the known K11 resource-limiting case uses the documented 15 GiB bound and 120-second checkpoint cadence before the aggregate run. The standard driver may increase bounded leaf scopes when required. Source and checker identities are reconciled at completion.

[Cache observations](cache-observations.md) distinguish measured reuse, source/checker identities, lost reports and unknown storage persistence.
