//! Meta-level reflection from Program syntax into Set/Prop syntax.

use crate::{
    environment::{CrateEnv, DefinedConstant},
    exp::{Exp, ExpContext, ExpContextEntry, ExpNode, ReflectedProgramCaseBranch},
    ids::DefId,
    program::*,
};
use std::{collections::HashSet, fmt};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReflectionError {
    UnresolvedMetavariable,
    NotProgramTerm,
    RecursiveDefinition(DefId),
}

impl fmt::Display for ReflectionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnresolvedMetavariable => write!(f, "cannot reflect an unresolved metavariable"),
            Self::NotProgramTerm => write!(f, "syntax is not a Program term"),
            Self::RecursiveDefinition(id) => {
                write!(f, "recursive Program definition during reflection: {id:?}")
            }
        }
    }
}

impl std::error::Error for ReflectionError {}

pub fn reflect_program_type(env: &CrateEnv, ty: ProgramType) -> Result<Exp, ReflectionError> {
    match ty {
        ProgramType::ValueType(ty) => reflect_value_type(env, ty),
        ProgramType::ComputationType(ty) => reflect_computation_type(env, ty),
    }
}

pub fn reflect_value_type(env: &CrateEnv, ty: ValueType) -> Result<Exp, ReflectionError> {
    let arena = env.arena();
    Ok(match arena.get(ty) {
        ValueTypeNode::Bound(index) => arena.exp_bound(index),
        ValueTypeNode::ModuleParam(id) => arena.alloc(ExpNode::ReflectedProgramParam(id)),
        ValueTypeNode::Meta { .. } => return Err(ReflectionError::UnresolvedMetavariable),
        ValueTypeNode::Thunk { computation_ty } => reflect_computation_type(env, computation_ty)?,
        ValueTypeNode::RunStep {
            state_ty,
            result_ty,
        } => arena.alloc(ExpNode::RunStep {
            state_ty: reflect_value_type(env, state_ty)?,
            result_ty: reflect_value_type(env, result_ty)?,
        }),
        ValueTypeNode::Inductive {
            indspec,
            parameters,
        } => {
            let reflected = env.program_inductive(indspec).reflected();
            arena.alloc(ExpNode::IndType {
                indspec: reflected,
                parameters: parameters
                    .into_iter()
                    .map(|p| reflect_value_type(env, p))
                    .collect::<Result<_, _>>()?,
            })
        }
    })
}

pub fn reflect_computation_type(
    env: &CrateEnv,
    ty: ComputationType,
) -> Result<Exp, ReflectionError> {
    let arena = env.arena();
    Ok(match arena.get(ty) {
        ComputationTypeNode::Meta { .. } => return Err(ReflectionError::UnresolvedMetavariable),
        ComputationTypeNode::Return { value_ty } => reflect_value_type(env, value_ty)?,
        ComputationTypeNode::Function { domain, codomain } => {
            let domain = reflect_value_type(env, domain)?;
            let codomain = reflect_computation_type(env, codomain)?;
            arena.alloc(ExpNode::Prod {
                var: crate::ids::SymbolId::ANONYMOUS,
                ty: domain,
                body: crate::calculus::shift_bound_indices(arena, codomain, 1, 0),
            })
        }
    })
}

pub fn reflect_context(
    env: &CrateEnv,
    context: &ProgramContext,
) -> Result<ExpContext, ReflectionError> {
    let mut result = Vec::with_capacity(context.len());
    for entry in context {
        match *entry {
            ProgramContextEntry::ValueType { var } => result.push(ExpContextEntry {
                var,
                ty: env.arena().sort(crate::sort::Sort::Set(0)),
            }),
            ProgramContextEntry::ValueTerm { var, ty } => result.push(ExpContextEntry {
                var,
                ty: reflect_value_type(env, ty)?,
            }),
        }
    }
    Ok(result)
}

/// Structurally reflects a type-checked Program, preserving bound indices.
pub fn reflect_program(env: &CrateEnv, program: ProgramTerm) -> Result<Exp, ReflectionError> {
    match program {
        ProgramTerm::ValueTerm(v) => reflect_value(env, v),
        ProgramTerm::ComputationTerm(c) => reflect_computation(env, c),
    }
}

pub fn reflect_value(env: &CrateEnv, value: ValueTerm) -> Result<Exp, ReflectionError> {
    reflect_value_inner(env, value, &mut HashSet::new())
}

fn reflect_value_inner(
    env: &CrateEnv,
    value: ValueTerm,
    visiting: &mut HashSet<DefId>,
) -> Result<Exp, ReflectionError> {
    let arena = env.arena();
    Ok(match arena.get(value) {
        ValueTermNode::Bound(index) => arena.exp_bound(index),
        ValueTermNode::ModuleParam(id) => arena.alloc(ExpNode::ReflectedProgramParam(id)),
        ValueTermNode::Meta { .. } => return Err(ReflectionError::UnresolvedMetavariable),
        ValueTermNode::DefinitionInstance {
            definition,
            parameters,
        } => {
            if !visiting.insert(definition) {
                return Err(ReflectionError::RecursiveDefinition(definition));
            }
            let result = match env.definition(definition) {
                DefinedConstant::ProgramValue { body, .. } => {
                    let body =
                        crate::program_definitions::instantiate_value(env, *body, &parameters, 0);
                    reflect_value_inner(env, body, visiting)
                }
                _ => Err(ReflectionError::NotProgramTerm),
            };
            visiting.remove(&definition);
            result?
        }
        ValueTermNode::DefinedConstant(id) => {
            if !visiting.insert(id) {
                return Err(ReflectionError::RecursiveDefinition(id));
            }
            let result = match env.definition(id) {
                DefinedConstant::ProgramValue { body, .. } => {
                    reflect_value_inner(env, *body, visiting)
                }
                _ => Err(ReflectionError::NotProgramTerm),
            };
            visiting.remove(&id);
            result?
        }
        ValueTermNode::Thunk { computation } => {
            reflect_computation_inner(env, computation, visiting)?
        }
        ValueTermNode::Continue {
            state_ty,
            result_ty,
            next,
        } => arena.alloc(ExpNode::Continue {
            state_ty: reflect_value_type(env, state_ty)?,
            result_ty: reflect_value_type(env, result_ty)?,
            next: reflect_value_inner(env, next, visiting)?,
        }),
        ValueTermNode::Finish {
            state_ty,
            result_ty,
            output,
        } => arena.alloc(ExpNode::Finish {
            state_ty: reflect_value_type(env, state_ty)?,
            result_ty: reflect_value_type(env, result_ty)?,
            output: reflect_value_inner(env, output, visiting)?,
        }),
        ValueTermNode::InductiveConstructor {
            indspec,
            parameters,
            idx,
            fields,
        } => {
            let reflected = env.program_inductive(indspec).reflected();
            let mut term = arena.alloc(ExpNode::IndCtor {
                indspec: reflected,
                parameters: parameters
                    .into_iter()
                    .map(|p| reflect_value_type(env, p))
                    .collect::<Result<_, _>>()?,
                idx,
            });
            for field in fields {
                term = arena.alloc(ExpNode::App {
                    func: term,
                    arg: reflect_value_inner(env, field, visiting)?,
                });
            }
            term
        }
    })
}

#[tracing::instrument(target = "ref_type::reflection", level = "debug", skip_all,
    fields(term = %crate::printing::format_computation(env, term)), ret, err)]
pub fn reflect_computation(env: &CrateEnv, term: ComputationTerm) -> Result<Exp, ReflectionError> {
    reflect_computation_inner(env, term, &mut HashSet::new())
}

fn reflect_computation_inner(
    env: &CrateEnv,
    term: ComputationTerm,
    visiting: &mut HashSet<DefId>,
) -> Result<Exp, ReflectionError> {
    let arena = env.arena();
    Ok(match arena.get(term) {
        ComputationTermNode::Meta { .. } => return Err(ReflectionError::UnresolvedMetavariable),
        ComputationTermNode::DefinitionInstance {
            definition,
            parameters,
        } => {
            if !visiting.insert(definition) {
                return Err(ReflectionError::RecursiveDefinition(definition));
            }
            let result = match env.definition(definition) {
                DefinedConstant::ProgramComputation { body, .. } => {
                    let body = crate::program_definitions::instantiate_computation(
                        env,
                        *body,
                        &parameters,
                        0,
                    );
                    reflect_computation_inner(env, body, visiting)
                }
                _ => Err(ReflectionError::NotProgramTerm),
            };
            visiting.remove(&definition);
            result?
        }
        ComputationTermNode::DefinedConstant(id) => {
            if !visiting.insert(id) {
                return Err(ReflectionError::RecursiveDefinition(id));
            }
            let result = match env.definition(id) {
                DefinedConstant::ProgramComputation { body, .. } => {
                    reflect_computation_inner(env, *body, visiting)
                }
                _ => Err(ReflectionError::NotProgramTerm),
            };
            visiting.remove(&id);
            result?
        }
        ComputationTermNode::Return { value } | ComputationTermNode::Force { value } => {
            reflect_value_inner(env, value, visiting)?
        }
        ComputationTermNode::Lambda {
            var,
            value_ty,
            body,
        } => {
            let ty = reflect_value_type(env, value_ty)?;
            arena.alloc(ExpNode::Lam {
                var,
                ty,
                body: reflect_computation_inner(env, body, visiting)?,
            })
        }
        ComputationTermNode::Application { computation, value } => arena.alloc(ExpNode::App {
            func: reflect_computation_inner(env, computation, visiting)?,
            arg: reflect_value_inner(env, value, visiting)?,
        }),
        ComputationTermNode::Sequence {
            computation,
            var,
            value_ty,
            body,
        } => {
            let source = reflect_computation_inner(env, computation, visiting)?;
            let ty = reflect_value_type(env, value_ty)?;
            let function = arena.alloc(ExpNode::Lam {
                var,
                ty,
                body: reflect_computation_inner(env, body, visiting)?,
            });
            arena.alloc(ExpNode::App {
                func: function,
                arg: source,
            })
        }
        ComputationTermNode::ValueLet {
            var,
            value_ty,
            value,
            body,
        } => {
            let function = arena.alloc(ExpNode::Lam {
                var,
                ty: reflect_value_type(env, value_ty)?,
                body: reflect_computation_inner(env, body, visiting)?,
            });
            arena.alloc(ExpNode::App {
                func: function,
                arg: reflect_value_inner(env, value, visiting)?,
            })
        }
        ComputationTermNode::Case {
            indspec,
            scrutinee,
            branches,
        } => {
            let reflected_branches = branches
                .into_iter()
                .map(|branch| {
                    Ok(ReflectedProgramCaseBranch {
                        binders: branch.binders,
                        body: reflect_computation_inner(env, branch.body, visiting)?,
                    })
                })
                .collect::<Result<_, ReflectionError>>()?;
            arena.alloc(ExpNode::ReflectedProgramCase {
                indspec,
                scrutinee: reflect_value_inner(env, scrutinee, visiting)?,
                branches: reflected_branches,
            })
        }
        ComputationTermNode::Run {
            state_ty,
            result_ty,
            step,
            initial,
            accessibility,
        } => arena.alloc(ExpNode::SetRun {
            state_ty: reflect_value_type(env, state_ty)?,
            result_ty: reflect_value_type(env, result_ty)?,
            step: reflect_value_inner(env, step, visiting)?,
            initial: reflect_value_inner(env, initial, visiting)?,
            accessibility,
        }),
        ComputationTermNode::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            accessibility,
            transition_equality,
        } => arena.alloc(ExpNode::SetRunCase {
            state_ty: reflect_value_type(env, state_ty)?,
            result_ty: reflect_value_type(env, result_ty)?,
            step: reflect_value_inner(env, step, visiting)?,
            initial: reflect_value_inner(env, initial, visiting)?,
            transition: reflect_computation_inner(env, transition, visiting)?,
            accessibility,
            transition_equality,
        }),
    })
}
