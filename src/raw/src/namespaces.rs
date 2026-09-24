//! Front-only provenance for substitution-specialized nominal declarations.
//!
//! Namespace aliases do not confer identity. Only the original declaration and
//! its arguments do; conversion in the kernel still compares ordinary type IDs.
use super::{calculus, environment::*, exp::Exp, ids::*, program::*, program_calculus as pc};

#[derive(Debug, Clone)]
pub struct Specialization<I> {
    pub source: I,
    pub arguments: Vec<(ModuleParamId, ModuleArgument)>,
}

impl CrateEnv {
    pub fn namespace_arguments(&self, module: ModuleId) -> Vec<(ModuleParamId, ModuleArgument)> {
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

    pub fn substitute_namespace_arguments(
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
                    ModuleArgument::Pts(e) => ModuleArgument::Pts(calculus::exp_subst_map(
                        self.arena(),
                        calculus::remap_all_global_ids(
                            self.arena(),
                            e,
                            &remapping.definition_ids,
                            &remapping.inductive_ids,
                            &remapping.program_inductive_ids,
                        ),
                        reflected,
                    )),
                    ModuleArgument::ProgramType(t) => {
                        ModuleArgument::ProgramType(pc::subst_value_type_module_params(
                            self.arena(),
                            pc::remap_value_type_global_ids(
                                self.arena(),
                                t,
                                &remapping.definition_ids,
                                &remapping.program_inductive_ids,
                            ),
                            substitutions,
                        ))
                    }
                    ModuleArgument::ProgramValue(v) => {
                        ModuleArgument::ProgramValue(pc::subst_value_module_params(
                            self.arena(),
                            pc::remap_value_global_ids(
                                self.arena(),
                                v,
                                &remapping.definition_ids,
                                &remapping.program_inductive_ids,
                                &remapping.inductive_ids,
                            ),
                            substitutions,
                            reflected,
                        ))
                    }
                };
                (*id, argument)
            })
            .collect()
    }

    /// Imports from local telescopes cannot share nominal IDs across scopes.
    pub fn namespace_arguments_shareable(
        &self,
        arguments: &[(ModuleParamId, ModuleArgument)],
    ) -> bool {
        use super::traversal::Term;
        let mut closed = true;
        for (_, arg) in arguments {
            let term = match *arg {
                ModuleArgument::Pts(e) => Term::Logical(e),
                ModuleArgument::ProgramType(t) => Term::ValueType(t),
                ModuleArgument::ProgramValue(v) => Term::Value(v),
            };
            term.walk(self.arena(), 0, &mut |term, depth| {
                let index = match term {
                    Term::Logical(e) => match self.arena().get(e) {
                        super::exp::ExpNode::Bound(i) => Some(i),
                        _ => None,
                    },
                    Term::ValueType(t) => match self.arena().get(t) {
                        ValueTypeNode::Bound(i) => Some(i),
                        _ => None,
                    },
                    Term::Value(v) => match self.arena().get(v) {
                        ValueTermNode::Bound(i) => Some(i),
                        _ => None,
                    },
                    _ => None,
                };
                if index.is_some_and(|i| i >= depth) {
                    closed = false;
                }
                None
            });
        }
        closed
    }

    pub fn namespace_arguments_equal(
        &self,
        left: &[(ModuleParamId, ModuleArgument)],
        right: &[(ModuleParamId, ModuleArgument)],
    ) -> bool {
        left.len() == right.len()
            && left.iter().zip(right).all(|((lp, l), (rp, r))| {
                lp == rp
                    && match (*l, *r) {
                        (ModuleArgument::Pts(l), ModuleArgument::Pts(r)) => {
                            calculus::convertible(self, l, r)
                        }
                        (ModuleArgument::ProgramType(l), ModuleArgument::ProgramType(r)) => {
                            pc::value_type_is_alpha_eq(self.arena(), l, r)
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
                                    (Ok(l), Ok(r)) => calculus::convertible(self, l, r),
                                    _ => false,
                                }
                        }
                        _ => false,
                    }
            })
    }
}
