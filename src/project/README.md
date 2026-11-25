# Project and source loading

`project` loads source snapshots, external modules, packages, workspaces, and path dependencies, building the `syntax` AST.

## Source snapshot

`SourceSnapshot::read` freezes the contents and identities of reachable sources and manifests.
`with_file` / `without_file` create edited versions; `new` / `insert` construct sources in memory.
`source` returns the text; `identity` returns the file identity after resolving aliases.

`SourceCache` checks contents on every read and shares matching text and SHA-256 digests.
By default, it retains up to 64 MiB and 16,384 files from the two most recent read generations.
`read_with_source_cache` uses a caller-owned source cache while loading every reachable dependency; `content_digest` returns a snapshot's content digest.
Snapshots retained by callers remain valid after cache collection.

## Module and package loading

`SourceProvider` allows source loading and parsing to be replaced.
`DiskSource` reads from disk; [sema](../sema/README.md) uses snapshots and a parse cache.
The loader visits shared dependencies once and joins package-name imports to module paths from the root.

`PackageGraph` holds the dependency graph and AST; `entry_packages` holds the checking entry points.
`PackageInfo` contains a `PackageInstanceId` based on the normalized root, named direct dependencies, the manifest, and source identities.
The same root yields the same instance; different roots yield different instances.

A workspace input loads all members and their dependencies; a member input loads its dependency closure.
Both retain the workspace manifest and shared storage location.
`workspace::default_cache_directory` discovers membership from ancestor manifests; `SourceSnapshot::default_cache_directory` uses retained membership to return the storage location.
See [Usage](../USAGE.md) for manifest examples and commands.
