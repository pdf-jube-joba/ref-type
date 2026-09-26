//! Source snapshots, external modules, and package loading.
pub mod module_loader;
pub mod package_loader;
mod snapshot;
pub use snapshot::{SourceSnapshot, absolute};
