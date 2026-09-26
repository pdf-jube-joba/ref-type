//! Snapshot based semantic queries and incremental checking.
pub use ::syntax::{module_loader, package_loader, parse, syntax};

mod model;
mod snapshot;
pub use model::*;
pub use snapshot::SourceSnapshot;

mod cache;
mod database;
mod graph;
mod parsing;
pub use database::{CheckOptions, Database};
pub use parsing::{ParseKind, ParseResult, ParsedSyntax};
