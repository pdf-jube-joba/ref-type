# C03 checkpoint 34815 recovery records

This additive directory preserves the latest checkpoint manifest and disk-stop records.
The earlier 418-file archive remains unchanged in the parent evidence commit.
It supplies accepted scope reports and the byte-identical fixed source snapshot.
Original path mappings, SHA256 identities, targets and the normal resume command are recorded here.
No checker was started to produce these records.

The manifest and the reference inventory are not a complete runnable checkpoint backup.
Referenced object payloads and the exact verified checker binary remain only in the original workspace.
The inventory audits stored bytes, headers and SHA256 values without restoring or deserializing the checkpoint.
No mathematical verification or environment-loss restore was performed.

For recovery, restore the earlier archive into a new empty directory, verify its manifest,
and place the new records at the original paths from resume-info.json only in an empty recovery workspace.
Place a source.json from the earlier archive, verified by fingerprints.json, beside the restored latest report.
All accepted scope report paths referenced by that report are present in the earlier archive.
Restore the exact referenced cache objects and exact checked binary before asserting checkpoint continuity.
Without the objects, compact_support_k must rebuild its checkpoint work.
Without an exact binary/source/target match, the normal driver rejects accepted-prefix resumption.

The command in resume-info.json is informational; capacity and identity prerequisites must be met first.
This commit does not complete the pending aggregate verification or change PR #76.
