//! Unclassified elaboration syntax and raw evaluation. Never a kernel certificate.
pub mod calculus;
pub mod derivation;
pub mod environment;
pub mod exp;
pub mod ids;
pub mod inductive;
pub(crate) mod namespaces;
pub mod printing;
pub mod program;
pub mod program_calculus;
pub mod program_definitions;
pub mod program_derivation;
pub mod program_inductive;
pub mod reflection;
pub mod sort;
#[cfg(test)]
mod tests;
pub(crate) mod traversal;
pub mod utils;
