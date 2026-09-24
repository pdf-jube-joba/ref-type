use super::{Location, RevisionId};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceOrigin {
    pub id: syntax::AstId,
    pub origin: Option<syntax::DerivedOrigin>,
    pub location: Option<Location>,
    pub written: Option<Location>,
}

impl super::AnalysisSnapshot {
    pub(super) fn source_trace(
        &self,
        map: &syntax::SourceMap,
        origin: Option<syntax::AstId>,
    ) -> Vec<SourceOrigin> {
        let locate = |location: &syntax::SourceLocation| {
            self.sources()
                .file_id(&location.source.id.0)
                .and_then(|id| self.sources().file(id))
                .map(|file| file.location(location.span))
        };
        origin
            .into_iter()
            .flat_map(|id| map.trace(id))
            .map(|(id, origin)| SourceOrigin {
                id,
                origin,
                location: map.location(id).and_then(locate),
                written: map.written_location(id).and_then(locate),
            })
            .collect()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
    Information,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub code: &'static str,
    pub severity: Severity,
    pub message: String,
    pub primary: Option<Location>,
    pub secondary: Vec<(Location, String)>,
    pub notes: Vec<String>,
    pub provenance: Vec<SourceOrigin>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiagnosticReport {
    pub revision: RevisionId,
    pub diagnostics: Vec<Diagnostic>,
}

impl Diagnostic {
    pub(super) fn error(code: &'static str, message: String, primary: Option<Location>) -> Self {
        Self {
            code,
            severity: Severity::Error,
            message,
            primary,
            secondary: Vec::new(),
            notes: Vec::new(),
            provenance: Vec::new(),
        }
    }
}
