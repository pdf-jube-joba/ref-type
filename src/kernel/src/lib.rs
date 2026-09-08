//! Sort-indexed Set/Prop and CBPV kernel.
//!
//! Unclassified syntax and metavariable solving belong to the `front` crate.
//! Kernel declarations are accepted only after formation and typing checks.
#![doc = include_str!("../README.md")]
pub mod ids;
pub mod stratified;
pub use stratified::{calculus, check, environment, printing, reflection, sort, syntax};
pub use syntax as exp;
pub use syntax as program;
