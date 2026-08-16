// stable identities for symbols and environment-owned entities
pub mod ids;
// pure type system sorts and their relations
pub mod sort;
// expression language and lightweight judgement results
pub mod exp;
// crate, module, declaration, and materialization state
pub mod environment;
// macros, and compose/decompose expressions
pub mod utils;
// inductive types and constructors
pub mod inductive;
// alpha conversion, substitution, free variables
pub mod calculus;
// type check, type inference, sort inference
pub mod derivation;
#[cfg(test)]
mod tests;
