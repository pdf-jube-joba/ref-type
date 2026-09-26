//! Elaboration workspace and the boundary to kernel verification.
pub mod elaborator;
mod lowering;
mod macros;
pub mod metavariables;
pub mod output;
pub mod raw;
pub mod resolved;
pub use ::syntax::{module_loader, package_loader, parse};
pub mod syntax {
    pub use crate::resolved::*;
    pub use ::syntax::syntax::*;
}
#[cfg(test)]
mod tests;

pub use elaborator::analysis;
