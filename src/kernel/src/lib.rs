//! Sort-indexed Set/Prop and CBPV kernel.
//!
//! Unclassified syntax and metavariable solving belong to the `front` crate.
//! Kernel declarations are accepted only after formation and typing checks.
#![doc = include_str!("../README.md")]
pub mod calculus;
pub mod check;
pub mod construction;
pub mod control;
pub mod environment;
pub mod ids;
pub mod printing;
pub mod reflection;
pub mod sharing;
pub mod sort;
mod structure;
pub mod syntax;
mod templates;
pub mod transfer;

#[cfg(test)]
mod tests;

pub use syntax as exp;
pub use syntax as program;
