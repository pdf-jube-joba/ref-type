//! Elaboration, macro expansion, and the checked kernel bridge.
pub mod elaborator;
mod lowering;
mod macros;
pub mod metavariables;
pub mod output;
pub use raw;
pub use syntax::{self, parse};
#[cfg(test)]
mod tests;
