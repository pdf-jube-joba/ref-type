//! The sort-indexed kernel calculus described in stratification4.md.
pub mod sort;
pub mod syntax;

pub mod calculus;
pub mod check;
pub mod environment;
pub mod reflection;

#[cfg(test)]
mod tests;

pub mod printing;
