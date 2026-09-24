//! Every raw handle retained across an elaboration unit is rooted here.
use super::*;
use crate::{inductive::CtorBinder, traversal::Term};

impl CrateEnv {
    pub fn declaration_node_counts(&self) -> [usize; 5] {
        self.arena().reachable_node_counts(self.retained_roots())
    }
    pub fn retained_roots(&self) -> Vec<Term> {
        let mut roots = Vec::new();
        for module in &self.modules {
            for parameter in &module.parameters {
                match parameter.kind {
                    ModuleParameterKind::Pts { ty } => roots.push(Term::Logical(ty)),
                    ModuleParameterKind::ProgramType => {}
                    ModuleParameterKind::ProgramValue { ty } => roots.push(Term::ValueType(ty)),
                }
            }
            for definition in module.definitions.iter().filter_map(OnceCell::get) {
                match *definition {
                    DefinedConstant::Pts { ty, body } => {
                        roots.extend([Term::Logical(ty), Term::Logical(body)])
                    }
                    DefinedConstant::ProgramValue { ty, body } => {
                        roots.extend([Term::ValueType(ty), Term::Value(body)])
                    }
                    DefinedConstant::ProgramComputation { ty, body } => {
                        roots.extend([Term::ComputationType(ty), Term::Computation(body)])
                    }
                }
            }
            for spec in module.inductives.iter().filter_map(OnceCell::get) {
                roots.extend(
                    spec.parameters()
                        .iter()
                        .chain(spec.indices())
                        .map(|(_, ty)| Term::Logical(*ty)),
                );
                for constructor in spec.constructors() {
                    roots.extend(constructor.indices.iter().copied().map(Term::Logical));
                    for binder in &constructor.telescope {
                        match binder {
                            CtorBinder::Simple((_, ty)) => roots.push(Term::Logical(*ty)),
                            CtorBinder::StrictPositive {
                                binders,
                                self_indices,
                            } => {
                                roots.extend(binders.iter().map(|(_, ty)| Term::Logical(*ty)));
                                roots.extend(self_indices.iter().copied().map(Term::Logical));
                            }
                        }
                    }
                }
            }
            for spec in module.program_inductives.iter().filter_map(OnceCell::get) {
                for constructor in spec.constructors() {
                    roots.extend(
                        constructor
                            .fields()
                            .iter()
                            .map(|(_, ty)| Term::ValueType(*ty)),
                    );
                }
            }
        }
        for context in self.checking_contexts.values() {
            roots.extend(context.iter().map(|binding| Term::Logical(binding.ty)));
        }
        let argument = |argument: &ModuleArgument| match *argument {
            ModuleArgument::Pts(term) => Term::Logical(term),
            ModuleArgument::ProgramType(term) => Term::ValueType(term),
            ModuleArgument::ProgramValue(term) => Term::Value(term),
        };
        for binding in self.namespace_bindings.values() {
            roots.extend(binding.arguments.iter().map(|(_, term)| argument(term)));
        }
        for lazy in self.lazy_definitions.values() {
            roots.extend(lazy.substitutions.iter().map(|(_, term)| argument(term)));
            roots.extend(
                lazy.reflected_substitutions
                    .iter()
                    .map(|(_, term)| Term::Logical(*term)),
            );
        }
        for lazy in self.lazy_inductives.values() {
            roots.extend(
                lazy.substitutions
                    .iter()
                    .map(|(_, term)| Term::Logical(*term)),
            );
        }
        for lazy in self.lazy_program_inductives.values() {
            roots.extend(lazy.substitutions.iter().map(|(_, term)| argument(term)));
        }
        for arguments in self
            .nominal_definitions
            .values()
            .map(|entry| &entry.arguments)
            .chain(
                self.nominal_inductives
                    .values()
                    .map(|entry| &entry.arguments),
            )
            .chain(
                self.nominal_datatypes
                    .values()
                    .map(|entry| &entry.arguments),
            )
        {
            roots.extend(arguments.iter().map(|(_, term)| argument(term)));
        }
        roots
    }

    pub fn clear_elaboration_caches(&self) {
        *self.inference_cache.borrow_mut() = Default::default();
        *self.contexts.borrow_mut() = ContextInterner::default();
        *self.whnf_cache.borrow_mut() = Default::default();
    }
}
