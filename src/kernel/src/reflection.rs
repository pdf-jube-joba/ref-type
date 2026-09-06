//! Meta-level reflection from Program syntax into Set/Prop syntax.

use crate::{
    environment::{CrateEnv, DefinedConstant},
    exp::{Exp, ExpContext, ExpContextEntry, ExpNode, ReflectedProgramCaseBranch},
    ids::DefId,
    program::*,
    program_derivation::ProgramCheckSession,
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
        ProgramType::Value(ty) => reflect_value_type(env, ty),
        ProgramType::Computation(ty) => reflect_computation_type(env, ty),
    }
}

pub fn reflect_value_type(env: &CrateEnv, ty: ValueType) -> Result<Exp, ReflectionError> {
    reflect_value_type_inner(env, ty, &mut HashSet::new())
}

fn reflect_value_type_inner(
    env: &CrateEnv,
    ty: ValueType,
    visiting: &mut HashSet<DefId>,
) -> Result<Exp, ReflectionError> {
    let arena = env.arena();
    Ok(match arena.get(ty) {
        ValueTypeNode::Bound(index) => arena.exp_bound(index),
        ValueTypeNode::ModuleParam(id) => arena.alloc(ExpNode::ReflectedProgramParam(id)),
        ValueTypeNode::Meta { .. } => return Err(ReflectionError::UnresolvedMetavariable),
        ValueTypeNode::Thunk { computation_ty } => {
            reflect_computation_type_inner(env, computation_ty, visiting)?
        }
        ValueTypeNode::RunStep {
            state_ty,
            result_ty,
        } => arena.alloc(ExpNode::RunStep {
            state_ty: reflect_value_type_inner(env, state_ty, visiting)?,
            result_ty: reflect_value_type_inner(env, result_ty, visiting)?,
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
                    .map(|p| reflect_value_type_inner(env, p, visiting))
                    .collect::<Result<_, _>>()?,
            })
        }
    })
}

pub fn reflect_computation_type(
    env: &CrateEnv,
    ty: ComputationType,
) -> Result<Exp, ReflectionError> {
    reflect_computation_type_inner(env, ty, &mut HashSet::new())
}

fn reflect_computation_type_inner(
    env: &CrateEnv,
    ty: ComputationType,
    visiting: &mut HashSet<DefId>,
) -> Result<Exp, ReflectionError> {
    let arena = env.arena();
    Ok(match arena.get(ty) {
        ComputationTypeNode::Meta { .. } => return Err(ReflectionError::UnresolvedMetavariable),
        ComputationTypeNode::Return { value_ty } => {
            reflect_value_type_inner(env, value_ty, visiting)?
        }
        ComputationTypeNode::Function { domain, codomain } => {
            let domain = reflect_value_type_inner(env, domain, visiting)?;
            let codomain = reflect_computation_type_inner(env, codomain, visiting)?;
            arena.alloc(ExpNode::Prod {
                var: crate::ids::SymbolId::ANONYMOUS,
                ty: domain,
                body: codomain,
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
            ProgramContextEntry::Type { var } => result.push(ExpContextEntry {
                var,
                ty: env.arena().sort(crate::sort::Sort::Set(0)),
            }),
            ProgramContextEntry::Value { var, ty } => result.push(ExpContextEntry {
                var,
                ty: reflect_value_type(env, ty)?,
            }),
        }
    }
    Ok(result)
}

pub fn reflect_program(
    env: &CrateEnv,
    context: &ProgramContext,
    program: Program,
) -> Result<Exp, ReflectionError> {
    match program {
        Program::Value(v) => reflect_value(env, context, v),
        Program::Computation(c) => reflect_computation(env, context, c),
    }
}

pub fn reflect_value(
    env: &CrateEnv,
    context: &ProgramContext,
    value: Value,
) -> Result<Exp, ReflectionError> {
    reflect_value_inner(env, context, value, &mut HashSet::new())
}

fn reflect_value_inner(
    env: &CrateEnv,
    context: &ProgramContext,
    value: Value,
    visiting: &mut HashSet<DefId>,
) -> Result<Exp, ReflectionError> {
    let arena = env.arena();
    Ok(match arena.get(value) {
        ValueNode::Bound(index) => arena.exp_bound(index),
        ValueNode::ModuleParam(id) => arena.alloc(ExpNode::ReflectedProgramParam(id)),
        ValueNode::Meta { .. } => return Err(ReflectionError::UnresolvedMetavariable),
        ValueNode::DefinedConstant(id) => {
            if !visiting.insert(id) {
                return Err(ReflectionError::RecursiveDefinition(id));
            }
            let result = match env.definition(id) {
                DefinedConstant::ProgramValue { body, .. } => {
                    reflect_value_inner(env, &Vec::new(), *body, visiting)
                }
                _ => Err(ReflectionError::NotProgramTerm),
            };
            visiting.remove(&id);
            result?
        }
        ValueNode::Thunk { computation } => {
            reflect_computation_inner(env, context, computation, visiting)?
        }
        ValueNode::Continue {
            state_ty,
            result_ty,
            next,
        } => arena.alloc(ExpNode::Continue {
            state_ty: reflect_value_type(env, state_ty)?,
            result_ty: reflect_value_type(env, result_ty)?,
            next: reflect_value_inner(env, context, next, visiting)?,
        }),
        ValueNode::Finish {
            state_ty,
            result_ty,
            output,
        } => arena.alloc(ExpNode::Finish {
            state_ty: reflect_value_type(env, state_ty)?,
            result_ty: reflect_value_type(env, result_ty)?,
            output: reflect_value_inner(env, context, output, visiting)?,
        }),
        ValueNode::InductiveConstructor {
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
                    arg: reflect_value_inner(env, context, field, visiting)?,
                });
            }
            term
        }
    })
}

pub fn reflect_computation(
    env: &CrateEnv,
    context: &ProgramContext,
    term: Computation,
) -> Result<Exp, ReflectionError> {
    reflect_computation_inner(env, context, term, &mut HashSet::new())
}

fn reflect_computation_inner(
    env: &CrateEnv,
    context: &ProgramContext,
    term: Computation,
    visiting: &mut HashSet<DefId>,
) -> Result<Exp, ReflectionError> {
    let arena = env.arena();
    Ok(match arena.get(term) {
        ComputationNode::Meta { .. } => return Err(ReflectionError::UnresolvedMetavariable),
        ComputationNode::DefinedConstant(id) => {
            if !visiting.insert(id) {
                return Err(ReflectionError::RecursiveDefinition(id));
            }
            let result = match env.definition(id) {
                DefinedConstant::ProgramComputation { body, .. } => {
                    reflect_computation_inner(env, &Vec::new(), *body, visiting)
                }
                _ => Err(ReflectionError::NotProgramTerm),
            };
            visiting.remove(&id);
            result?
        }
        ComputationNode::Return { value } | ComputationNode::Force { value } => {
            reflect_value_inner(env, context, value, visiting)?
        }
        ComputationNode::Lambda {
            var,
            value_ty,
            body,
        } => {
            let ty = reflect_value_type(env, value_ty)?;
            let mut nested = context.clone();
            nested.push(ProgramContextEntry::Value { var, ty: value_ty });
            arena.alloc(ExpNode::Lam {
                var,
                ty,
                body: reflect_computation_inner(env, &nested, body, visiting)?,
            })
        }
        ComputationNode::Application { computation, value } => arena.alloc(ExpNode::App {
            func: reflect_computation_inner(env, context, computation, visiting)?,
            arg: reflect_value_inner(env, context, value, visiting)?,
        }),
        ComputationNode::Sequence {
            computation,
            var,
            value_ty,
            body,
        } => {
            let source = reflect_computation_inner(env, context, computation, visiting)?;
            let ty = reflect_value_type(env, value_ty)?;
            let mut nested = context.clone();
            nested.push(ProgramContextEntry::Value { var, ty: value_ty });
            let function = arena.alloc(ExpNode::Lam {
                var,
                ty,
                body: reflect_computation_inner(env, &nested, body, visiting)?,
            });
            arena.alloc(ExpNode::App {
                func: function,
                arg: source,
            })
        }
        ComputationNode::ValueLet { var, value, body } => {
            let mut infer_context = context.clone();
            let value_ty =
                crate::program_derivation::ProgramCheckSession::new(env, &mut infer_context)
                    .infer_value(value)
                    .map_err(|_| ReflectionError::NotProgramTerm)?;
            let mut nested = context.clone();
            nested.push(ProgramContextEntry::Value { var, ty: value_ty });
            let function = arena.alloc(ExpNode::Lam {
                var,
                ty: reflect_value_type(env, value_ty)?,
                body: reflect_computation_inner(env, &nested, body, visiting)?,
            });
            arena.alloc(ExpNode::App {
                func: function,
                arg: reflect_value_inner(env, context, value, visiting)?,
            })
        }
        ComputationNode::Case {
            indspec,
            scrutinee,
            branches,
        } => {
            let mut infer_context = context.clone();
            let scrutinee_ty = ProgramCheckSession::new(env, &mut infer_context)
                .infer_value(scrutinee)
                .map_err(|_| ReflectionError::NotProgramTerm)?;
            let parameters = match arena.get(scrutinee_ty) {
                ValueTypeNode::Inductive {
                    indspec: actual,
                    parameters,
                } if actual == indspec => parameters,
                _ => return Err(ReflectionError::NotProgramTerm),
            };
            let constructors = env.program_inductive(indspec).constructors();
            let mut reflected_branches = Vec::with_capacity(branches.len());
            for (branch, constructor) in branches.into_iter().zip(constructors) {
                let mut nested = context.clone();
                let fields = constructor.instantiated_fields(arena, &parameters);
                for (field_index, (binder, (_, ty))) in
                    branch.binders.iter().copied().zip(fields).enumerate()
                {
                    nested.push(ProgramContextEntry::Value {
                        var: binder,
                        ty: crate::program_calculus::shift_value_type_indices(
                            arena,
                            ty,
                            field_index,
                            0,
                        ),
                    });
                }
                reflected_branches.push(ReflectedProgramCaseBranch {
                    binders: branch.binders,
                    body: reflect_computation_inner(env, &nested, branch.body, visiting)?,
                });
            }
            arena.alloc(ExpNode::ReflectedProgramCase {
                indspec,
                scrutinee: reflect_value_inner(env, context, scrutinee, visiting)?,
                branches: reflected_branches,
            })
        }
        ComputationNode::Run {
            state_ty,
            result_ty,
            step,
            initial,
        } => arena.alloc(ExpNode::SetRun {
            state_ty: reflect_value_type(env, state_ty)?,
            result_ty: reflect_value_type(env, result_ty)?,
            step: reflect_value_inner(env, context, step, visiting)?,
            initial: reflect_value_inner(env, context, initial, visiting)?,
        }),
        ComputationNode::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => arena.alloc(ExpNode::SetRunCase {
            state_ty: reflect_value_type(env, state_ty)?,
            result_ty: reflect_value_type(env, result_ty)?,
            step: reflect_value_inner(env, context, step, visiting)?,
            initial: reflect_value_inner(env, context, initial, visiting)?,
            transition: reflect_computation_inner(env, context, transition, visiting)?,
        }),
    })
}
