//! Snapshot based semantic queries and incremental checking.
pub use ::project::{SourceSnapshot, module_loader, package_loader};
pub use ::syntax::{parse, syntax};

mod model;
pub use model::*;

mod cache;
mod database;
mod graph;
mod parsing;
pub use database::{CheckOptions, Database};
pub use parsing::{ParseKind, ParseResult, ParsedSyntax};
