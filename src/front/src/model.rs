use crate::SourceSnapshot;
use serde::{Deserialize, Serialize};
use std::{
    ops::Range,
    path::{Path, PathBuf},
};

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Location {
    pub file: PathBuf,
    pub range: Range<usize>,
}
impl Location {
    pub fn contains(&self, file: &Path, offset: usize) -> bool {
        self.file == file && self.range.contains(&offset)
    }
    pub fn render(&self, snapshot: &SourceSnapshot) -> String {
        snapshot.source(&self.file).map_or_else(
            || self.file.display().to_string(),
            |source| {
                front_syntax::syntax::SourceLocation {
                    source: source.clone(),
                    span: front_syntax::syntax::SourceSpan {
                        start: self.range.start,
                        end: self.range.end,
                    },
                }
                .render()
            },
        )
    }
}
impl From<&front_syntax::syntax::SourceLocation> for Location {
    fn from(location: &front_syntax::syntax::SourceLocation) -> Self {
        Self {
            file: location.source.id.0.clone(),
            range: location.span.start..location.span.end,
        }
    }
}

/// Source identities are independent of arena allocation and query order.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct DeclarationId {
    pub module: Vec<String>,
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Declaration {
    pub id: DeclarationId,
    pub kind: String,
    pub location: Location,
    /// The elaborated type, rendered before the elaboration workspace is freed.
    pub ty: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Reference {
    pub location: Location,
    pub target: DeclarationId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Goal {
    pub name: String,
    pub location: Location,
    pub context: String,
    pub judgement: Option<String>,
    pub constraints: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Diagnostic {
    pub message: String,
    pub location: Option<Location>,
    pub goals: Vec<Goal>,
}
impl Diagnostic {
    pub fn render(&self, snapshot: &SourceSnapshot) -> String {
        match &self.location {
            Some(location) => format!("{}\n{}", self.message, location.render(snapshot)),
            None => self.message.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QueryOutput {
    pub location: Location,
    pub text: String,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum ModuleStatus {
    Verified,
    #[default]
    Incomplete,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModuleResult {
    pub path: Vec<String>,
    pub dependencies: Vec<Vec<String>>,
    pub status: ModuleStatus,
    pub declarations: Vec<Declaration>,
    pub references: Vec<Reference>,
    pub outputs: Vec<QueryOutput>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticResult {
    pub modules: Vec<ModuleResult>,
    pub diagnostics: Vec<Diagnostic>,
}
impl SemanticResult {
    pub fn is_success(&self) -> bool {
        self.diagnostics.is_empty()
            && self
                .modules
                .iter()
                .all(|module| module.status == ModuleStatus::Verified)
    }
    pub fn declarations(&self) -> impl Iterator<Item = &Declaration> {
        self.modules.iter().flat_map(|module| &module.declarations)
    }
    pub fn declaration(&self, id: &DeclarationId) -> Option<&Declaration> {
        self.declarations()
            .find(|declaration| &declaration.id == id)
    }
    pub fn definition_at(&self, file: impl AsRef<Path>, offset: usize) -> Option<&Declaration> {
        let file = crate::snapshot::absolute(file.as_ref());
        let reference = self
            .modules
            .iter()
            .flat_map(|module| &module.references)
            .filter(|reference| reference.location.contains(&file, offset))
            .min_by_key(|reference| reference.location.range.len())?;
        self.declaration(&reference.target)
    }
    pub fn type_at(&self, file: impl AsRef<Path>, offset: usize) -> Option<&str> {
        let file = crate::snapshot::absolute(file.as_ref());
        self.definition_at(&file, offset)
            .or_else(|| {
                self.declarations()
                    .filter(|declaration| declaration.location.contains(&file, offset))
                    .min_by_key(|declaration| declaration.location.range.len())
            })
            .and_then(|declaration| declaration.ty.as_deref())
    }

    pub fn references_to<'a>(
        &'a self,
        id: &'a DeclarationId,
    ) -> impl Iterator<Item = &'a Reference> {
        self.modules
            .iter()
            .flat_map(|module| &module.references)
            .filter(move |reference| &reference.target == id)
    }
    pub fn goals(&self) -> impl Iterator<Item = &Goal> {
        self.all_diagnostics()
            .flat_map(|diagnostic| &diagnostic.goals)
    }
    pub fn all_diagnostics(&self) -> impl Iterator<Item = &Diagnostic> {
        self.diagnostics.iter()
    }
    pub fn outputs(&self) -> impl Iterator<Item = &QueryOutput> {
        self.modules.iter().flat_map(|module| &module.outputs)
    }
}

#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct QueryStats {
    pub parsed_files: usize,
    pub reused_parses: usize,
    pub checked_modules: usize,
    pub reused_modules: usize,
    pub disk_hits: usize,
    pub disk_writes: usize,
    pub cache_write_failures: usize,
}
