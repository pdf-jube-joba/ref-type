//! Inspect the explicit and inherited environments of a selected import.
use super::*;

impl Resolver {
    pub(super) fn debug_module_arguments(&self, name: &Identifier, calls: &[ModuleCall]) {
        if std::env::var("REF_TYPE_DEBUG_MODULE_ARGUMENTS").is_ok_and(|filter| name.0 == filter) {
            eprintln!(
                "resolved import {} in {}",
                name.0,
                self.path(self.current).join(".")
            );
            for (child, arguments) in calls.iter() {
                for (argument, value) in arguments {
                    let mut pending = vec![value.clone()];
                    let mut visited = FxHashSet::default();
                    let mut parameters = std::collections::BTreeSet::new();
                    let mut namespaces = std::collections::BTreeSet::new();
                    while let Some(mut value) = pending.pop() {
                        macros::walk_sexp_mut(&mut value, &mut |node| {
                            if let SExp::AccessPath { access, .. }
                            | SExp::ProgramValueReference { access } = node
                            {
                                let (reference, module) = match access {
                                    LocalAccess::Current { access, .. } => (Some(access), None),
                                    LocalAccess::Resolved { access, module, .. } => {
                                        (Some(access), Some(*module))
                                    }
                                    _ => (None, None),
                                };
                                if let Some(binding) = reference
                                    .and_then(|name| name.1)
                                    .and_then(|id| self.global_bindings.get(&id))
                                    && binding.parameter.is_some()
                                {
                                    parameters.insert(format!(
                                        "{}.{}",
                                        self.path(binding.module).join("."),
                                        binding.name
                                    ));
                                }
                                if let Some(module) = module {
                                    if visited.insert(module) {
                                        let scope = &self.scopes[module.0 as usize];
                                        let mut source =
                                            self.origins.get(&module).copied().unwrap_or(module);
                                        loop {
                                            for parameter in self
                                                .module_parameters
                                                .get(&source)
                                                .into_iter()
                                                .flatten()
                                                .flat_map(|bind| &bind.vars)
                                            {
                                                if let Some(value) = parameter
                                                    .1
                                                    .and_then(|id| scope.substitutions.get(&id))
                                                {
                                                    pending.push((*value).clone());
                                                } else {
                                                    parameters.insert(format!(
                                                        "{}.{} (unsubstituted)",
                                                        self.path(source).join("."),
                                                        parameter.0
                                                    ));
                                                }
                                            }
                                            let Some(parent) =
                                                self.scopes[source.0 as usize].parent
                                            else {
                                                break;
                                            };
                                            source = parent;
                                        }
                                    }
                                    namespaces.insert(format!(
                                        "{}: {}",
                                        module.0,
                                        self.path(module).join(".")
                                    ));
                                }
                            }
                        });
                    }
                    eprintln!(
                        "argument {}.{} parameters={parameters:?} namespaces={namespaces:?}",
                        child.0, argument.0
                    );
                }
            }
        }
    }
}
