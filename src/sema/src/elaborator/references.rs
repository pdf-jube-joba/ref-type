//! Record the references actually selected by elaboration, including Program names.
use super::*;

#[derive(Debug, Clone)]
pub struct ResolvedOccurrence {
    pub local: Option<SourceSpan>,
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
            // Definition-site macro names do not denote a call-site occurrence.
            LocalAccess::Resolved { .. } => return Some(item),
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
        let Some(span) = identifier.span() else {
            return;
        };
        let Some(owner) = &self.diagnostic_location else {
            return;
        };
        if span.start < owner.span.start || owner.span.end < span.end {
            return;
        }
        let Some(text) = owner.source.text.get(span.start..span.end) else {
            return;
        };
        if text != identifier.as_str().trim_end_matches('^') {
            return;
        }
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
            local: None,
            location: SourceLocation {
                source: owner.source.clone(),
                span,
            },
            module: path,
            name,
            definition,
        });
    }

    pub fn occurrences(&self) -> std::cell::Ref<'_, Vec<ResolvedOccurrence>> {
        self.occurrences.borrow()
    }

    pub(crate) fn record_local_reference(&self, name: &Identifier, binder: SourceSpan) {
        let Some(span) = name.span() else {
            return;
        };
        let Some(owner) = &self.diagnostic_location else {
            return;
        };
        if span.start < owner.span.start
            || owner.span.end < span.end
            || binder.start < owner.span.start
            || owner.span.end < binder.end
        {
            return;
        }
        self.occurrences.borrow_mut().push(ResolvedOccurrence {
            local: Some(binder),
            location: SourceLocation {
                source: owner.source.clone(),
                span,
            },
            module: Vec::new(),
            name: name.0.clone(),
            definition: None,
        });
    }
}
