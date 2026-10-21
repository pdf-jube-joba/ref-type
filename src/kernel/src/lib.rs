//! A shared PTS expression arena, checked declarations, and contextual unification.
#![doc = include_str!("../README.md")]
pub mod calculus;
pub mod check;
pub mod environment;
pub mod error;
pub mod exports;
pub mod graph_store;
pub mod ids;
pub mod metavariables;
mod node_store;
pub mod reduction;
pub mod reflection;
pub mod resources;
pub mod sharing;
pub mod sort;
pub mod syntax;
pub use node_store::StoreStats;
pub mod termination;
#[cfg(test)]
mod tests;
