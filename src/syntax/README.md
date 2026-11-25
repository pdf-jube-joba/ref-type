# Source syntax

`syntax` handles lexing, parsing, and the AST.
`SourceFile`, `SourceSpan`, and `SourceLocation` connect syntax to its original source.

`parse_root` parses a root file; `parse_items` parses declarations in an external module.
Parse errors carry messages and spans for callers to display.
`Module` retains declarations and their spans.
`LocalAccess` and associated accesses retain spans for name references.

The AST represents names, bindings, macro tokens, proof blocks, and Program syntax classified by type.
`resolve` converts the AST into HIR with binding IDs and source spans.
`project` handles loading external modules and packages, as well as source snapshots.
