# Persistent identities and relocation

This crate provides identity mappings shared by the resolver, raw layer, and kernel, together with deterministic serialization for persistent storage.
It separates language-level package identities from allocation indices in the current arena.

An `Identity` consists of a table name and either an integer or an arena/integer pair used by that table.
`Relocation` maps old identities to new ones.
`Relocation::collecting()` collects reachable identities using the same traversal.
Unreserved references, mappings between different tables, and conflicting reservations are errors.

The `Relocate` derive traverses fields to be persisted.
Fields marked `serde(skip)` or `relocate(skip)` are treated as working data to be reconstructed.
Bound-variable indices and declaration positions remain ordinary integers; only global references have explicit identity implementations.
Identities embedded in generated names use the same mapping.

Traversal of `Arc` and `Rc` tracks sharing by type and original address.
The mapping retains both original and relocated values, preventing confusion from address reuse and processing each node of a shared DAG only once.
Relocation operates on export or import working data without modifying the active environment.

`canonical::to_vec` produces a postcard-compatible binary representation, sorting map keys by their encoded bytes.
Output size and structural depth are bounded.
Use `canonical::serialize_set` for sets; arrays with meaningful ordering retain their order.
Shared arrays and namespace composition tables use dedicated table formats in elaboration.

The [sema artifact store](../sema/src/artifact_store.rs) persists checking sessions.
A manifest's `graph` lists immutable kernel pages and chunked session metadata objects, linking them to a checkpoint containing the completion ledger and resolver/raw indices.
Pages already stored in the same store are referenced by subsequent manifests without being encoded again.
Page checksums and inputs are checked before restoration, and kernel identities remain valid within the same session after loading.
These references participate in the existing lease, store-lock, and GC mechanisms, protecting pages and checkpoints in use.

Session metadata is chunked by content, allowing common suffixes to remain shared when information is prepended.
Transfers to the publication destination process each object digest once and share immutable objects through hard links on the same filesystem.
Across filesystems, compressed contents are copied into a temporary file and published atomically.
Length and digest are checked before transfer; manifest publication and object pinning use a shared store lock.
Objects under construction are registered in an append-only lease journal, protecting them from GC even before manifest publication.
