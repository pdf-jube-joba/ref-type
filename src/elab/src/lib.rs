//! HIR elaboration, temporary terms, constraint solving, and the kernel bridge.
pub mod calculus;
pub mod dependencies;
pub mod derivation;
pub mod environment;
pub mod exp;
pub mod ids;
pub mod inductive;
pub mod lowering;
pub mod metavariables;
pub mod namespaces;
pub mod output;
pub mod printing;
pub mod profiling;
pub mod program;
pub mod program_calculus;
pub mod program_definitions;
pub mod program_derivation;
pub mod program_inductive;
pub mod program_term_elaborator;
pub mod reflection;
pub mod resolver;
pub mod sort;
pub mod term_elaborator;
#[cfg(test)]
mod term_tests;
pub mod traversal;
pub mod utils;
