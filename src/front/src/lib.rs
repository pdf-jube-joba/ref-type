// surface syntax
// Kernel handles contain a memoized analysis Cell that is excluded from their
// equality and hash implementations.
#![allow(clippy::mutable_key_type)]
mod macros;
pub mod metavariables;
pub mod output;
pub mod syntax;
// string -> surface
pub mod module_loader;
pub mod parse;
// surface -> core
pub mod elaborator;
#[cfg(test)]
mod tests;

#[doc(hidden)]
pub mod raw;

mod lowering;
