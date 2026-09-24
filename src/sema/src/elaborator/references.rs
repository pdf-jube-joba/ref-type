//! Record the references actually selected by elaboration, including Program names.
use super::*;

#[derive(Debug, Clone)]
pub struct ResolvedOccurrence {
    pub origin: Option<AstId>,
    pub local: Option<SourceLocation>,
    pub location: SourceLocation,
    pub module: Vec<String>,
    pub name: String,
    pub definition: Option<DefId>,
}

impl GlobalEnvironment {
    pub(crate) fn lookup_access(&self, access: &LocalAccess) -> Option<ItemAccessResult> {
        let (module, item) =
            module_manager::resolve_access(&self.crate_env, self.module_manager.current(), access)?;
        let identifier = match access {
            LocalAccess::Current { access } => access,
            LocalAccess::Named { child, .. } => child,
            LocalAccess::Resolved { access, .. } => access,
        };
        let definition = match &item {
            ItemAccessResult::Definition(item) | ItemAccessResult::ReflectedDefinition(item) => {
                Some(item.definition)
            }
            _ => None,
        };
        self.record_reference(
            identifier,
            module,
            identifier.as_str().trim_end_matches('^').to_owned(),
            definition,
        );
        Some(item)
    }

    pub(crate) fn record_reference(
        &self,
        identifier: &Identifier,
        module: ModuleId,
        name: String,
        definition: Option<DefId>,
    ) {
        let Some(location) = identifier
            .origin()
            .and_then(|id| self.crate_env.sources.written_location(id))
            .cloned()
        else {
            return;
        };
        let mut module = self
            .crate_env
            .namespace_binding_id(module)
            .map(|id| self.crate_env.binding(id).source)
            .unwrap_or(module);
        let mut path = Vec::new();
        while let Some(parent) = self.crate_env.module(module).parent() {
            path.push(self.crate_env.module(module).name().to_owned());
            module = parent;
        }
        path.reverse();
        self.occurrences.borrow_mut().push(ResolvedOccurrence {
            origin: identifier.origin(),
            local: None,
            location,
            module: path,
            name,
            definition,
        });
    }

    pub fn occurrences(&self) -> std::cell::Ref<'_, Vec<ResolvedOccurrence>> {
        self.occurrences.borrow()
    }

    pub(crate) fn record_local_reference(&self, name: &Identifier, binder: AstId) {
        let Some(location) = name
            .origin()
            .and_then(|id| self.crate_env.sources.written_location(id))
            .cloned()
        else {
            return;
        };
        let Some(binder) = self.crate_env.sources.written_location(binder).cloned() else {
            return;
        };
        self.occurrences.borrow_mut().push(ResolvedOccurrence {
            origin: name.origin(),
            local: Some(binder),
            location,
            module: Vec::new(),
            name: name.0.clone(),
            definition: None,
        });
    }
}
