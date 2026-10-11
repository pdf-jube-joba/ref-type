//! Source snapshots, external modules, and package loading.
pub mod module_loader;
pub mod package_loader;
mod snapshot;
pub use snapshot::{SourceCache, SourceSnapshot, absolute};

pub mod error;
pub use error::Error;
