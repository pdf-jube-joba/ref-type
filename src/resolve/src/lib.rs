//! Type-independent binding resolution and hygienic macro expansion.
mod bindings;
pub mod hir;
mod lower;
mod macros;

mod program;
mod resolver;
pub use resolver::{Binding, Diagnostic, Import, Project, Reference, resolve};

/// Structural traversal shared by downstream HIR consumers.
pub mod visit {
    pub use crate::macros::{walk_sexp_control, walk_sexp_mut};
}
