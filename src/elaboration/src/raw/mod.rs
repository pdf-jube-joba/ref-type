//! Source views, module environments, and declaration provenance over kernel terms.
pub mod derivation;
pub mod environment;
pub mod exp;
pub mod ids;
pub mod inductive;
pub(crate) mod namespaces;
pub mod printing;
pub mod program;
pub mod program_derivation;
pub mod program_inductive;
pub mod reflection;
pub(crate) mod remapping;
pub mod sort;
#[cfg(test)]
mod tests;
pub(crate) mod traversal;
pub mod utils;
