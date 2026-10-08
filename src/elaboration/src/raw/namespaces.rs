//! Front-only provenance for substitution-specialized nominal declarations.
//!
//! Namespace aliases do not confer identity. Only the original declaration and
//! its arguments do; conversion in the kernel still compares ordinary type IDs.
use super::{environment::*, exp::Exp, ids::*, program::*};

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub(crate) struct Specialization<I> {
    pub source: I,
    pub arguments: Vec<(ModuleParamId, ModuleArgument)>,
}

impl CrateEnv {
    fn namespace_terms_equal(&self, left: Exp, right: Exp) -> bool {
        if left == right {
            return true;
        }
        // These heads are rigid: neither a local variable nor an opaque module
        // parameter reduces to another variable. Avoid registering an entire
        // captured declaration graph merely to reject this comparison.
        use super::exp::ExpNode;
        match (self.arena().get(left), self.arena().get(right)) {
            (ExpNode::Bound(_), ExpNode::Bound(_))
            | (ExpNode::Bound(_), ExpNode::ModuleParam(_))
            | (ExpNode::ModuleParam(_), ExpNode::Bound(_))
            | (ExpNode::ModuleParam(_), ExpNode::ModuleParam(_)) => return false,
            _ => {}
        }
        if let Some(&equal) = self.namespace_conversion_cache.borrow().get(&(left, right)) {
            return equal;
        }
        let Some(equal) = crate::kernel_bridge::resolved_convertible(self, left, right) else {
            return false;
        };
        self.namespace_conversion_cache
            .borrow_mut()
            .insert((left, right), equal);
        self.namespace_conversion_cache
            .borrow_mut()
            .insert((right, left), equal);
        equal
    }

    pub(crate) fn namespace_arguments(
        &self,
        module: ModuleId,
    ) -> Vec<(ModuleParamId, ModuleArgument)> {
        let mut ancestors = Vec::new();
        let mut current = Some(module);
        while let Some(id) = current {
            ancestors.push(id);
            current = self.module(id).parent();
        }
        ancestors.reverse();
        ancestors
            .into_iter()
            .flat_map(|module| {
                self.module(module).parameters().iter().enumerate().map(
                    move |(position, parameter)| {
                        let id = ModuleParamId {
                            module,
                            position: position as u32,
                        };
                        let argument = match parameter.kind {
                            ModuleParameterKind::Pts { .. } => {
                                ModuleArgument::Pts(self.arena().exp_module_param(id))
                            }
                            ModuleParameterKind::ProgramType => ModuleArgument::ProgramType(
                                self.arena().alloc(ValueTypeNode::ModuleParam(id)),
                            ),
                            ModuleParameterKind::ProgramValue { .. } => {
                                ModuleArgument::ProgramValue(
                                    self.arena().alloc(ValueTermNode::ModuleParam(id)),
                                )
                            }
                        };
                        (id, argument)
                    },
                )
            })
            .collect()
    }

    pub(crate) fn substitute_namespace_arguments(
        &self,
        arguments: &[(ModuleParamId, ModuleArgument)],
        substitutions: &[(ModuleParamId, ModuleArgument)],
        reflected: &[(ModuleParamId, Exp)],
        remapping: &DeclarationRemapping,
    ) -> Vec<(ModuleParamId, ModuleArgument)> {
        arguments
            .iter()
            .map(|(id, argument)| {
                // Remap the source graph first. Inserted caller arguments must not
                // themselves be remapped or substituted a second time.
                let argument = match *argument {
                    ModuleArgument::Pts(e) => {
                        ModuleArgument::Pts(crate::raw::remapping::exp_subst_map(
                            self.arena(),
                            crate::raw::remapping::remap_all_global_ids(
                                self.arena(),
                                e,
                                &remapping.definition_ids,
                                &remapping.inductive_ids,
                                &remapping.program_inductive_ids,
                            ),
                            reflected,
                        ))
                    }
                    ModuleArgument::ProgramType(t) => ModuleArgument::ProgramType(
                        crate::raw::remapping::subst_value_type_module_params(
                            self.arena(),
                            crate::raw::remapping::remap_value_type_global_ids(
                                self.arena(),
                                t,
                                &remapping.definition_ids,
                                &remapping.program_inductive_ids,
                            ),
                            substitutions,
                        ),
                    ),
                    ModuleArgument::ProgramValue(v) => ModuleArgument::ProgramValue(
                        crate::raw::remapping::subst_value_module_params(
                            self.arena(),
                            crate::raw::remapping::remap_value_global_ids(
                                self.arena(),
                                v,
                                &remapping.definition_ids,
                                &remapping.program_inductive_ids,
                                &remapping.inductive_ids,
                            ),
                            substitutions,
                            reflected,
                        ),
                    ),
                };
                (*id, argument)
            })
            .collect()
    }

    /// Imports from local telescopes cannot share nominal IDs across scopes.
    pub(crate) fn namespace_arguments_shareable(
        &self,
        arguments: &[(ModuleParamId, ModuleArgument)],
    ) -> bool {
        use super::traversal::Term;
        arguments.iter().all(|(_, arg)| {
            let term = match *arg {
                ModuleArgument::Pts(e) => Term::Logical(e),
                ModuleArgument::ProgramType(t) => Term::ValueType(t),
                ModuleArgument::ProgramValue(v) => Term::Value(v),
            };
            self.arena().max_loose_bound(term).is_none()
        })
    }

    pub(crate) fn namespace_arguments_equal(
        &self,
        left: &[(ModuleParamId, ModuleArgument)],
        right: &[(ModuleParamId, ModuleArgument)],
    ) -> bool {
        left.len() == right.len()
            && left.iter().zip(right).all(|((lp, l), (rp, r))| {
                lp == rp
                    && match (*l, *r) {
                        (ModuleArgument::Pts(l), ModuleArgument::Pts(r)) => {
                            self.namespace_terms_equal(l, r)
                        }
                        (ModuleArgument::ProgramType(l), ModuleArgument::ProgramType(r)) => {
                            crate::kernel_bridge::value_type_is_alpha_eq(self.arena(), l, r)
                        }
                        (ModuleArgument::ProgramValue(l), ModuleArgument::ProgramValue(r)) => {
                            l == r
                                || match (
                                    super::reflection::reflect_program(
                                        self,
                                        ProgramTerm::ValueTerm(l),
                                    ),
                                    super::reflection::reflect_program(
                                        self,
                                        ProgramTerm::ValueTerm(r),
                                    ),
                                ) {
                                    (Ok(l), Ok(r)) => self.namespace_terms_equal(l, r),
                                    _ => false,
                                }
                        }
                        _ => false,
                    }
            })
    }
}

/// Determine identity before reserving another copy of an imported graph.
/// Following declaration provenance is essential: an argument can refer to a
/// definition whose own telescope contains a substituted parameter.
pub(crate) struct NamespaceStability<'a> {
    env: &'a CrateEnv,
    reflected: &'a [(ModuleParamId, Exp)],
    argument_sets: std::collections::HashMap<Vec<(ModuleParamId, ModuleArgument)>, bool>,
    definitions: std::collections::HashMap<DefId, bool>,
    inductives: std::collections::HashMap<InductiveId, bool>,
    datatypes: std::collections::HashMap<ProgramInductiveId, bool>,
}

impl<'a> NamespaceStability<'a> {
    pub(crate) fn new(env: &'a CrateEnv, reflected: &'a [(ModuleParamId, Exp)]) -> Self {
        Self {
            env,
            reflected,
            argument_sets: Default::default(),
            definitions: Default::default(),
            inductives: Default::default(),
            datatypes: Default::default(),
        }
    }

    fn definition(&mut self, id: DefId) -> bool {
        if let Some(&stable) = self.definitions.get(&id) {
            return stable;
        }
        self.definitions.insert(id, false);
        let stable = self.arguments(&self.env.definition_specialization_arguments(id));
        self.definitions.insert(id, stable);
        stable
    }

    fn inductive(&mut self, id: InductiveId) -> bool {
        if let Some(&stable) = self.inductives.get(&id) {
            return stable;
        }
        self.inductives.insert(id, false);
        let stable = self.arguments(&self.env.inductive_specialization_arguments(id));
        self.inductives.insert(id, stable);
        stable
    }

    fn datatype(&mut self, id: ProgramInductiveId) -> bool {
        if let Some(&stable) = self.datatypes.get(&id) {
            return stable;
        }
        self.datatypes.insert(id, false);
        let stable = self.arguments(&self.env.datatype_specialization_arguments(id));
        self.datatypes.insert(id, stable);
        stable
    }

    pub(crate) fn arguments(&mut self, arguments: &[(ModuleParamId, ModuleArgument)]) -> bool {
        use super::traversal::{Memoized, Term};
        if let Some(&stable) = self.argument_sets.get(arguments) {
            return stable;
        }
        if !self.env.namespace_arguments_shareable(arguments) {
            return false;
        }
        self.argument_sets.insert(arguments.to_vec(), false);
        let stable = arguments.iter().all(|(_, argument)| {
            // Program imports retain the existing materialization path.
            let ModuleArgument::Pts(expression) = *argument else {
                return false;
            };
            let arena = self.env.arena();
            let mut stable = true;
            let mut visitor = Memoized::new(|term: Term, _: usize| {
                if let Term::Logical(expression) = term {
                    use super::exp::ExpNode;
                    stable &= match arena.get(expression) {
                        ExpNode::ModuleParam(id) | ExpNode::ReflectedProgramParam(id) => self
                            .reflected
                            .iter()
                            .find(|(p, _)| *p == id)
                            .is_none_or(|(_, value)| *value == expression),
                        ExpNode::DefinedConstant(id)
                        | ExpNode::DefinitionInstance { definition: id, .. } => self.definition(id),
                        ExpNode::IndType { indspec, .. }
                        | ExpNode::IndCtor { indspec, .. }
                        | ExpNode::IndElim { indspec, .. }
                        | ExpNode::IndCase { indspec, .. } => self.inductive(indspec),
                        ExpNode::ReflectedProgramCase { indspec, .. } => self.datatype(indspec),
                        ExpNode::Meta { .. }
                        | ExpNode::BoxType { .. }
                        | ExpNode::BoxProgram { .. }
                        | ExpNode::ForceBox { .. } => false,
                        _ => true,
                    };
                } else {
                    stable = false;
                }
                None
            });
            Term::Logical(expression).walk(arena, 0, &mut visitor);
            stable
        });
        self.argument_sets.insert(arguments.to_vec(), stable);
        stable
    }

    pub(crate) fn item(&mut self, item: &ModuleItem) -> bool {
        match item {
            ModuleItem::Definition { definition, .. } => self.definition(*definition),
            ModuleItem::Inductive {
                inductive,
                associated_definitions,
                ..
            }
            | ModuleItem::Record {
                inductive,
                associated_definitions,
                ..
            } => {
                self.inductive(*inductive)
                    && associated_definitions
                        .iter()
                        .all(|(_, id)| self.definition(*id))
            }
            ModuleItem::ProgramInductive { .. } => false,
        }
    }
}
