//! Snapshot based semantic queries and incremental checking.
pub use ::project::workspace::{default_cache_directory, source_entry};
pub use ::project::{SourceSnapshot, module_loader, package_loader};
pub use ::syntax::{parse, syntax};
pub use elaboration::SessionStatistics;

mod memory;
pub use memory::MemoryCacheStats;
mod model;
pub use model::*;

pub mod artifact_store;
mod cache;
mod database;
mod graph;
mod package_inputs;
mod parsing;
mod progress;
pub use database::{CheckOptions, Database};
pub use parsing::{ParseKind, ParseResult, ParsedSyntax};
pub use progress::{
    ModuleProgress, ProgressAction, ProgressEvent, ProgressModule, ProgressPhase, ProgressPlan,
};

mod environment;

pub use elaboration::DiagnosticMode;

pub use timing;

pub mod error;

pub use elaboration::{request_collection, set_allocator_collection};
