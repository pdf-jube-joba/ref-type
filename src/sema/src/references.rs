use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SemanticRef {
    Item(ItemId),
    Local(Location),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Occurrence {
    pub location: Location,
    pub target: SemanticRef,
    pub ty: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReferenceResult {
    pub revision: RevisionId,
    pub locations: Vec<Location>,
    pub complete: bool,
}

impl AnalysisSnapshot {
    pub fn definition_at(&self, file: FileId, position: usize) -> Option<Location> {
        let occurrence = self.check().occurrences.iter().find(|occurrence| {
            occurrence.location.file == file
                && occurrence.location.range.start <= position
                && position < occurrence.location.range.end
        })?;
        let target = match occurrence.target {
            SemanticRef::Item(target) => target,
            SemanticRef::Local(location) => return Some(location),
        };
        let item = self.outline().iter().find(|item| item.id == target)?;
        item.name_location.or(Some(item.location))
    }

    pub fn type_at(&self, file: FileId, position: usize) -> Option<&str> {
        self.check()
            .occurrences
            .iter()
            .find(|occurrence| {
                occurrence.location.file == file
                    && occurrence.location.range.start <= position
                    && position < occurrence.location.range.end
            })?
            .ty
            .as_deref()
    }

    pub fn references(&self, item: ItemId) -> ReferenceResult {
        ReferenceResult {
            revision: self.revision(),
            // Macro expansion origins and Program local binders are still
            // being migrated into the occurrence index.
            complete: false,
            locations: self
                .check()
                .occurrences
                .iter()
                .filter(|occurrence| occurrence.target == SemanticRef::Item(item))
                .map(|occurrence| occurrence.location)
                .collect(),
        }
    }

    pub(super) fn capture_references(&self, global: &GlobalEnvironment) -> Vec<Occurrence> {
        use raw::{environment::DefinedConstant, printing};
        let mut result = Vec::new();
        let mut seen = std::collections::HashSet::new();
        for occurrence in global.occurrences().iter() {
            let Some(file) = self
                .sources()
                .file_id(&occurrence.location.source.id.0)
                .and_then(|id| self.sources().file(id))
            else {
                continue;
            };
            let target = if let Some(binder) = occurrence.local {
                SemanticRef::Local(file.location(binder))
            } else if let Some(target) = self.outline().iter().find(|item| {
                let package = occurrence
                    .module
                    .first()
                    .and_then(|name| super::PackageId::from_module_name(name));
                let module = if package.is_some() {
                    &occurrence.module[1..]
                } else {
                    &occurrence.module[..]
                };
                item.key.package == package
                    && item.key.module == module
                    && item.key.name == occurrence.name
            }) {
                SemanticRef::Item(target.id)
            } else {
                continue;
            };
            if !seen.insert((
                file.id,
                occurrence.location.span.start,
                occurrence.location.span.end,
                target,
            )) {
                continue;
            }
            let ty = occurrence
                .definition
                .map(|id| match global.crate_env().definition(id) {
                    DefinedConstant::Pts { ty, .. } => {
                        printing::format_exp(global.crate_env(), *ty)
                    }
                    DefinedConstant::ProgramValue { ty, .. } => {
                        printing::format_value_type(global.crate_env(), *ty)
                    }
                    DefinedConstant::ProgramComputation { ty, .. } => {
                        printing::format_computation_type(global.crate_env(), *ty)
                    }
                });
            let occurrence = Occurrence {
                location: file.location(occurrence.location.span),
                target,
                ty,
            };
            result.push(occurrence);
        }
        result
    }
}
