//! A shared PTS expression arena, checked declarations, and contextual unification.
#![doc = include_str!("../README.md")]
pub mod calculus;
pub mod check;
pub mod environment;
pub mod error;
pub mod ids;
pub mod metavariables;
pub mod reduction;
pub mod reflection;
pub mod sharing;
pub mod sort;
pub mod syntax;
pub mod termination;
#[cfg(test)]
mod tests;
