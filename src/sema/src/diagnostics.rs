use super::{Location, RevisionId};

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
        }
    }
}
