// expression language and lightweight judgement results
pub mod exp;
// for serialize and Debug implementations
pub mod serialize;
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
