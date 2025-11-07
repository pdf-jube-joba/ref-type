// expression language, includes Derivation (tree structure of derivation)
pub mod exp;
// macros, and compose/decompose expressions
pub mod utils;
// inductive types and constructors
pub mod inductive;
// alpha conversion, substitution, free variables
pub mod calculus;
// type check, type inference, sort inference
pub mod derivation;
pub mod derivation_strict;
// pretty printing
pub mod printing;
#[cfg(test)]
mod tests;
