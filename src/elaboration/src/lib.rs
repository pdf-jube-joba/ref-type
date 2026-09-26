//! Type inference and kernel verification of resolved, untyped HIR.
//!
//! ```
//! let ast = syntax::parse::str_parse_modules(
//!     r"\module M { \definition P: \Prop := \forall (A: \Prop) -> A -> A; }"
//! ).unwrap();
//! let hir = resolve::resolve(&ast).unwrap();
//! let mut checker = elaboration::Checker::default();
//! checker.check(&hir).unwrap();
//! assert!(checker.statistics().kernel_declaration_nodes > 0);
//! ```
//!
//! Inference handles stay inside the checker:
//! ```compile_fail
//! use elaboration::raw::exp::Exp;
//! ```
mod elaborator;
pub(crate) use resolve::hir;
mod items;
mod lowering;
mod metavariables;
mod output;
mod raw;
#[cfg(test)]
mod tests;

pub use elaborator::analysis;

mod api;
pub use api::{Checker, Diagnostic, Goal, Statistics};
