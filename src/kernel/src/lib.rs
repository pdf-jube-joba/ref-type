// stable identities for symbols and environment-owned entities
pub mod ids;
// pure type system sorts and their relations
pub mod sort;
// expression language and lightweight judgement results
pub mod exp;
// CBPV syntax and Program-only typing judgements
pub mod program;
// human-readable rendering of kernel expressions
pub mod printing;
// crate, module, declaration, and materialization state
pub mod environment;
// macros, and compose/decompose expressions
pub mod utils;
// inductive types and constructors
pub mod inductive;
// CBPV value datatypes and their reflected Set counterparts
pub mod program_inductive;
// alpha conversion, substitution, free variables
pub mod calculus;
// substitution and evaluation for the disjoint Program syntax
pub mod program_calculus;
// structural, meta-level CBPV-to-Set reflection
pub mod reflection;
// type check, type inference, sort inference
pub mod derivation;
// Program formation and typing judgements
pub mod program_derivation;
#[cfg(test)]
mod tests;
