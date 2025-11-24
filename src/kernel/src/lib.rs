// expression language, includes Derivation (tree structure of derivation)
pub mod exp;
// for serialize
pub mod serialize;
// macros, and compose/decompose expressions
pub mod utils;
// inductive types and constructors
pub mod inductive;
// alpha conversion, substitution, free variables
pub mod calculus;
// builder for derivation tree
pub mod builder;
// type check, type inference, sort inference
pub mod derivation;
// pretty printing
pub mod printing;
#[cfg(test)]
mod tests;
