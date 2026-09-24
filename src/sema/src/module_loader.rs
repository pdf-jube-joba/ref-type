//! Compatibility entry point for loading a complete source snapshot.
use crate::{AnalysisHost, syntax::Module};
use std::path::Path;

/// Load the complete module tree starting at an anonymous root source file.
/// `\\module child;` in logical module `parent` reads `parent/child.ref`.
pub fn load_modules_from_root(root_file: &Path) -> Result<Vec<Module>, String> {
    let mut host = AnalysisHost::new(root_file).map_err(|error| error.to_string())?;
    host.refresh_disk();
    let snapshot = host.snapshot();
    snapshot.modules().map_err(|report| {
        report
            .diagnostics
            .iter()
            .map(|diagnostic| snapshot.render_diagnostic(diagnostic))
            .collect::<Vec<_>>()
            .join("\n\n")
    })
}
