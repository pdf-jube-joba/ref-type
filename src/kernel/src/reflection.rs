//! Meta-level reflection from raw CBPV syntax into Set syntax.
//!
//! Reflection is intentionally implemented as a structural Rust function.  It
//! is not a reduction rule and the resulting Set term contains no `RfType` or
//! `RfTerm` node.

use std::collections::HashSet;

use crate::{
    calculus::shift_bound_indices,
    derivation::CheckSession,
    environment::{CrateEnv, DefinitionKind},
    exp::{Context, ContextEntry, ProgramCaseBranch, RawExp, RawNode},
    ids::{DefId, ModuleId, SymbolId},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReflectionError {
    NotProgramType,
    NotProgramTerm,
    MixedContext,
    RecursiveDefinition(DefId),
    IllTypedValueLet,
    InvalidProgramCase,
}

impl std::fmt::Display for ReflectionError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotProgramType => formatter.write_str("expression is not a Program type"),
            Self::NotProgramTerm => formatter.write_str("expression is not a Program term"),
            Self::MixedContext => {
                formatter.write_str("Program reflection received a PTS context entry")
            }
            Self::RecursiveDefinition(definition) => write!(
                formatter,
                "recursive transparent Program definition {:?} cannot be reflected",
                definition
            ),
            Self::IllTypedValueLet => {
                formatter.write_str("cannot infer the value type in reflected value-let")
            }
            Self::InvalidProgramCase => {
                formatter.write_str("invalid Program case cannot be reflected")
            }
        }
    }
}

impl std::error::Error for ReflectionError {}

pub fn reflect_type(env: &CrateEnv, ty: RawExp) -> Result<RawExp, ReflectionError> {
    reflect_type_inner(env, ty, &mut HashSet::new())
}

fn reflect_type_inner(
    env: &CrateEnv,
    ty: RawExp,
    visiting: &mut HashSet<DefId>,
) -> Result<RawExp, ReflectionError> {
    let arena = env.arena();
    Ok(match arena.get(ty) {
        RawNode::ValueType => arena.sort(crate::sort::Sort::Set(0)),
        RawNode::Bound(index) => arena.bound(index),
        RawNode::ModuleParam(parameter) => arena.alloc(RawNode::ReflectedProgramParam(parameter)),
        RawNode::ThunkType { computation_ty } => reflect_type_inner(env, computation_ty, visiting)?,
        RawNode::ReturnType { value_ty } => reflect_type_inner(env, value_ty, visiting)?,
        RawNode::ComputationFunction { domain, codomain } => {
            let domain = reflect_type_inner(env, domain, visiting)?;
            let codomain = reflect_type_inner(env, codomain, visiting)?;
            arena.alloc(RawNode::Prod {
                var: SymbolId::ANONYMOUS,
                ty: domain,
                body: shift_bound_indices(arena, codomain, 1, 0),
            })
        }
        RawNode::RunStep {
            state_ty,
            result_ty,
        } => arena.alloc(RawNode::RunStep {
            state_ty: reflect_type_inner(env, state_ty, visiting)?,
            result_ty: reflect_type_inner(env, result_ty, visiting)?,
        }),
        RawNode::ProgramIndType {
            indspec,
            parameters,
        } => {
            let reflected = env.program_inductive(indspec).reflected();
            let parameters = parameters
                .into_iter()
                .map(|parameter| reflect_type_inner(env, parameter, visiting))
                .collect::<Result<Vec<_>, _>>()?;
            arena.alloc(RawNode::IndType {
                indspec: reflected,
                parameters,
            })
        }
        RawNode::DefinedConstant(definition) => {
            if !visiting.insert(definition) {
                return Err(ReflectionError::RecursiveDefinition(definition));
            }
            let declared = env.definition(definition);
            let reflected = match declared.kind {
                DefinitionKind::ProgramValue | DefinitionKind::ProgramComputation => {
                    reflect_type_inner(env, declared.body, visiting)
                }
                DefinitionKind::Pts => Err(ReflectionError::NotProgramType),
            };
            visiting.remove(&definition);
            reflected?
        }
        _ => return Err(ReflectionError::NotProgramType),
    })
}

pub fn reflect_context(env: &CrateEnv, context: &Context) -> Result<Context, ReflectionError> {
    let mut reflected = Vec::with_capacity(context.len());
    for entry in context {
        match entry {
            ContextEntry::ProgramType { var } => reflected.push(ContextEntry::Pts {
                var: *var,
                ty: env.arena().sort(crate::sort::Sort::Set(0)),
            }),
            ContextEntry::ProgramValue { var, ty } => reflected.push(ContextEntry::Pts {
                var: *var,
                ty: reflect_type(env, *ty)?,
            }),
            ContextEntry::Pts { .. } => return Err(ReflectionError::MixedContext),
        }
    }
    Ok(reflected)
}

pub fn reflect_term(
    env: &CrateEnv,
    current_module: ModuleId,
    context: &Context,
    term: RawExp,
) -> Result<RawExp, ReflectionError> {
    reflect_term_inner(env, current_module, context, term, &mut HashSet::new())
}

fn reflect_term_inner(
    env: &CrateEnv,
    current_module: ModuleId,
    context: &Context,
    term: RawExp,
    visiting: &mut HashSet<DefId>,
) -> Result<RawExp, ReflectionError> {
    let arena = env.arena();
    Ok(match arena.get(term) {
        RawNode::Bound(index) => arena.bound(index),
        RawNode::ModuleParam(parameter) => arena.alloc(RawNode::ReflectedProgramParam(parameter)),
        RawNode::DefinedConstant(definition) => {
            if !visiting.insert(definition) {
                return Err(ReflectionError::RecursiveDefinition(definition));
            }
            let declared = env.definition(definition);
            let reflected = match declared.kind {
                DefinitionKind::ProgramValue | DefinitionKind::ProgramComputation => {
                    reflect_term_inner(env, definition.module, &Vec::new(), declared.body, visiting)
                }
                DefinitionKind::Pts => Err(ReflectionError::NotProgramTerm),
            };
            visiting.remove(&definition);
            reflected?
        }
        RawNode::Thunk { computation } => {
            reflect_term_inner(env, current_module, context, computation, visiting)?
        }
        RawNode::Return { value } | RawNode::Force { value } => {
            reflect_term_inner(env, current_module, context, value, visiting)?
        }
        RawNode::ComputationLam {
            var,
            value_ty,
            body,
        } => {
            let reflected_ty = reflect_type(env, value_ty)?;
            let mut body_context = context.clone();
            body_context.push(ContextEntry::ProgramValue { var, ty: value_ty });
            arena.alloc(RawNode::Lam {
                var,
                ty: reflected_ty,
                body: reflect_term_inner(env, current_module, &body_context, body, visiting)?,
            })
        }
        RawNode::ComputationApp { computation, value } => arena.alloc(RawNode::App {
            func: reflect_term_inner(env, current_module, context, computation, visiting)?,
            arg: reflect_term_inner(env, current_module, context, value, visiting)?,
        }),
        RawNode::Sequence {
            computation,
            var,
            value_ty,
            body,
        } => {
            let reflected_ty = reflect_type(env, value_ty)?;
            let mut body_context = context.clone();
            body_context.push(ContextEntry::ProgramValue { var, ty: value_ty });
            let body = reflect_term_inner(env, current_module, &body_context, body, visiting)?;
            let function = arena.alloc(RawNode::Lam {
                var,
                ty: reflected_ty,
                body,
            });
            arena.alloc(RawNode::App {
                func: function,
                arg: reflect_term_inner(env, current_module, context, computation, visiting)?,
            })
        }
        RawNode::ValueLet { var, value, body } => {
            let mut inference_context = context.clone();
            let value_ty = CheckSession::new(env, current_module, &mut inference_context)
                .infer_value(value)
                .map_err(|_| ReflectionError::IllTypedValueLet)?;
            let reflected_ty = reflect_type(env, value_ty)?;
            let mut body_context = context.clone();
            body_context.push(ContextEntry::ProgramValue { var, ty: value_ty });
            let body = reflect_term_inner(env, current_module, &body_context, body, visiting)?;
            arena.alloc(RawNode::App {
                func: arena.alloc(RawNode::Lam {
                    var,
                    ty: reflected_ty,
                    body,
                }),
                arg: reflect_term_inner(env, current_module, context, value, visiting)?,
            })
        }
        RawNode::Continue {
            state_ty,
            result_ty,
            next,
        } => arena.alloc(RawNode::Continue {
            state_ty: reflect_type(env, state_ty)?,
            result_ty: reflect_type(env, result_ty)?,
            next: reflect_term_inner(env, current_module, context, next, visiting)?,
        }),
        RawNode::Finish {
            state_ty,
            result_ty,
            output,
        } => arena.alloc(RawNode::Finish {
            state_ty: reflect_type(env, state_ty)?,
            result_ty: reflect_type(env, result_ty)?,
            output: reflect_term_inner(env, current_module, context, output, visiting)?,
        }),
        RawNode::ProgramIndCtor {
            indspec,
            parameters,
            idx,
            fields,
        } => {
            let spec = env.program_inductive(indspec);
            let reflected_parameters = parameters
                .into_iter()
                .map(|parameter| reflect_type(env, parameter))
                .collect::<Result<Vec<_>, _>>()?;
            let head = arena.alloc(RawNode::IndCtor {
                indspec: spec.reflected(),
                parameters: reflected_parameters,
                idx,
            });
            fields.into_iter().try_fold(head, |func, field| {
                Ok::<_, ReflectionError>(arena.alloc(RawNode::App {
                    func,
                    arg: reflect_term_inner(env, current_module, context, field, visiting)?,
                }))
            })?
        }
        RawNode::ProgramIndProjection {
            indspec,
            parameters,
            value,
            field,
        } => arena.alloc(RawNode::IndProjection {
            indspec: env.program_inductive(indspec).reflected(),
            parameters: parameters
                .into_iter()
                .map(|parameter| reflect_type(env, parameter))
                .collect::<Result<Vec<_>, _>>()?,
            value: reflect_term_inner(env, current_module, context, value, visiting)?,
            field,
        }),
        RawNode::ProgramCase {
            indspec,
            scrutinee,
            branches,
        } => {
            let spec = env.program_inductive(indspec);
            if branches.len() != spec.constructors().len() {
                return Err(ReflectionError::InvalidProgramCase);
            }
            let branches = branches
                .into_iter()
                .enumerate()
                .map(|(index, branch)| {
                    let fields = spec.constructors()[index].fields();
                    if fields.len() != branch.binders.len() {
                        return Err(ReflectionError::InvalidProgramCase);
                    }
                    let mut branch_context = context.clone();
                    for (binder, (_, ty)) in branch.binders.iter().zip(fields) {
                        branch_context.push(ContextEntry::ProgramValue {
                            var: *binder,
                            ty: *ty,
                        });
                    }
                    Ok(ProgramCaseBranch {
                        binders: branch.binders,
                        body: reflect_term_inner(
                            env,
                            current_module,
                            &branch_context,
                            branch.body,
                            visiting,
                        )?,
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            arena.alloc(RawNode::ReflectedProgramCase {
                indspec,
                scrutinee: reflect_term_inner(env, current_module, context, scrutinee, visiting)?,
                branches,
            })
        }
        RawNode::Run {
            state_ty,
            result_ty,
            step,
            initial,
        } => arena.alloc(RawNode::SetRun {
            state_ty: reflect_type(env, state_ty)?,
            result_ty: reflect_type(env, result_ty)?,
            step: reflect_term_inner(env, current_module, context, step, visiting)?,
            initial: reflect_term_inner(env, current_module, context, initial, visiting)?,
        }),
        RawNode::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => arena.alloc(RawNode::SetRunCase {
            state_ty: reflect_type(env, state_ty)?,
            result_ty: reflect_type(env, result_ty)?,
            step: reflect_term_inner(env, current_module, context, step, visiting)?,
            initial: reflect_term_inner(env, current_module, context, initial, visiting)?,
            transition: reflect_term_inner(env, current_module, context, transition, visiting)?,
        }),
        // Existing Program polymorphism is retained as a surface extension.
        RawNode::Lam { var, ty, body } => {
            let reflected_ty = reflect_type(env, ty)?;
            let mut body_context = context.clone();
            let entry = if matches!(arena.get(ty), RawNode::ValueType) {
                ContextEntry::ProgramType { var }
            } else {
                ContextEntry::ProgramValue { var, ty }
            };
            body_context.push(entry);
            arena.alloc(RawNode::Lam {
                var,
                ty: reflected_ty,
                body: reflect_term_inner(env, current_module, &body_context, body, visiting)?,
            })
        }
        RawNode::App { func, arg } => arena.alloc(RawNode::App {
            func: reflect_term_inner(env, current_module, context, func, visiting)?,
            arg: reflect_term_inner(env, current_module, context, arg, visiting)
                .or_else(|_| reflect_type(env, arg))?,
        }),
        _ => return Err(ReflectionError::NotProgramTerm),
    })
}
