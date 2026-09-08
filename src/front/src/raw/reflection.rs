//! Meta-level reflection from Program syntax into Set/Prop syntax.

use crate::raw::{
    environment::{CrateEnv, DefinedConstant},
    exp::{Exp, ExpContext, ExpContextEntry, ExpNode, ReflectedProgramCaseBranch},
    ids::DefId,
    program::*,
};
use std::{
    collections::{HashMap, HashSet},
    fmt,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReflectionError {
    UnresolvedMetavariable,
    NotProgramTerm,
    RecursiveDefinition(DefId),
    MissingRunCertificate,
}

impl fmt::Display for ReflectionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnresolvedMetavariable => write!(f, "cannot reflect an unresolved metavariable"),
            Self::NotProgramTerm => write!(f, "syntax is not a Program term"),
            Self::RecursiveDefinition(id) => {
                write!(f, "recursive Program definition during reflection: {id:?}")
            }
            Self::MissingRunCertificate => write!(f, "Program run has no certificate"),
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
                var: crate::raw::ids::SymbolId::ANONYMOUS,
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
            ProgramContextEntry::ValueType { var } => result.push(ExpContextEntry {
                var,
                ty: env.arena().sort(crate::raw::sort::Sort::Set(0)),
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

/// Checks that a certificate is the reflection of the supplied runtime
/// Program. Proof fields are checked by the ordinary Set/Prop checker and are
/// deliberately omitted from this structural correspondence check.
pub fn certificate_matches_program(env: &CrateEnv, program: ProgramTerm, certificate: Exp) -> bool {
    // Named definitions already carry their checked reflection. Resolve them
    // before inspecting Run/RunCase, whose certificate exposes the body.
    if reflect_program(env, program)
        .is_ok_and(|term| crate::raw::calculus::exp_is_alpha_eq(env, term, certificate))
    {
        return true;
    }
    let arena = env.arena();
    match (program, arena.get(certificate)) {
        (
            ProgramTerm::ComputationTerm(computation),
            ExpNode::SetRun {
                state_ty,
                result_ty,
                step,
                initial,
                ..
            },
        ) => match arena.get(computation) {
            ComputationTermNode::Run {
                state_ty: p_state_ty,
                result_ty: p_result_ty,
                step: p_step,
                initial: p_initial,
            } => {
                reflect_value_type(env, p_state_ty)
                    .is_ok_and(|e| crate::raw::calculus::exp_is_alpha_eq(env, e, state_ty))
                    && reflect_value_type(env, p_result_ty)
                        .is_ok_and(|e| crate::raw::calculus::exp_is_alpha_eq(env, e, result_ty))
                    && reflect_value(env, p_step)
                        .is_ok_and(|e| crate::raw::calculus::exp_is_alpha_eq(env, e, step))
                    && reflect_value(env, p_initial)
                        .is_ok_and(|e| crate::raw::calculus::exp_is_alpha_eq(env, e, initial))
            }
            _ => false,
        },
        (
            ProgramTerm::ComputationTerm(computation),
            ExpNode::SetRunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                ..
            },
        ) => match arena.get(computation) {
            ComputationTermNode::RunCase {
                state_ty: p_state_ty,
                result_ty: p_result_ty,
                step: p_step,
                initial: p_initial,
                transition: p_transition,
            } => {
                reflect_value_type(env, p_state_ty)
                    .is_ok_and(|e| crate::raw::calculus::exp_is_alpha_eq(env, e, state_ty))
                    && reflect_value_type(env, p_result_ty)
                        .is_ok_and(|e| crate::raw::calculus::exp_is_alpha_eq(env, e, result_ty))
                    && reflect_value(env, p_step)
                        .is_ok_and(|e| crate::raw::calculus::exp_is_alpha_eq(env, e, step))
                    && reflect_value(env, p_initial)
                        .is_ok_and(|e| crate::raw::calculus::exp_is_alpha_eq(env, e, initial))
                    && certificate_matches_program(
                        env,
                        ProgramTerm::ComputationTerm(p_transition),
                        transition,
                    )
            }
            _ => false,
        },
        _ => false,
    }
}

#[tracing::instrument(target = "ref_type::reflection", level = "debug", skip_all,
    fields(term = %crate::raw::printing::format_value(env, value)), ret, err)]
pub fn reflect_value(env: &CrateEnv, value: ValueTerm) -> Result<Exp, ReflectionError> {
    reflect_value_inner(env, value, &HashMap::new(), &mut HashSet::new())
}

fn reflect_value_inner(
    env: &CrateEnv,
    value: ValueTerm,
    certificates: &HashMap<ComputationTerm, Exp>,
    visiting: &mut HashSet<DefId>,
) -> Result<Exp, ReflectionError> {
    let arena = env.arena();
    Ok(match arena.get(value) {
        ValueTermNode::Bound(index) => arena.exp_bound(index),
        ValueTermNode::ModuleParam(id) => arena.alloc(ExpNode::ReflectedProgramParam(id)),
        ValueTermNode::Meta { .. } => return Err(ReflectionError::UnresolvedMetavariable),
        ValueTermNode::DefinedConstant(id) => {
            if !visiting.insert(id) {
                return Err(ReflectionError::RecursiveDefinition(id));
            }
            let result = match env.definition(id) {
                DefinedConstant::ProgramValue {
                    certified_reflection: Some(term),
                    ..
                } => Ok(*term),
                DefinedConstant::ProgramValue { body, .. } => {
                    reflect_value_inner(env, *body, certificates, visiting)
                }
                _ => Err(ReflectionError::NotProgramTerm),
            };
            visiting.remove(&id);
            result?
        }
        ValueTermNode::Thunk { computation } => {
            reflect_computation_inner(env, computation, certificates, visiting)?
        }
        ValueTermNode::Continue {
            state_ty,
            result_ty,
            next,
        } => arena.alloc(ExpNode::Continue {
            state_ty: reflect_value_type(env, state_ty)?,
            result_ty: reflect_value_type(env, result_ty)?,
            next: reflect_value_inner(env, next, certificates, visiting)?,
        }),
        ValueTermNode::Finish {
            state_ty,
            result_ty,
            output,
        } => arena.alloc(ExpNode::Finish {
            state_ty: reflect_value_type(env, state_ty)?,
            result_ty: reflect_value_type(env, result_ty)?,
            output: reflect_value_inner(env, output, certificates, visiting)?,
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
                    arg: reflect_value_inner(env, field, certificates, visiting)?,
                });
            }
            term
        }
    })
}

#[tracing::instrument(target = "ref_type::reflection", level = "debug", skip_all,
    fields(term = %crate::raw::printing::format_computation(env, term)), ret, err)]
pub fn reflect_computation(env: &CrateEnv, term: ComputationTerm) -> Result<Exp, ReflectionError> {
    reflect_computation_inner(env, term, &HashMap::new(), &mut HashSet::new())
}

pub fn reflect_computation_with_certificates(
    env: &CrateEnv,
    term: ComputationTerm,
    certificates: &HashMap<ComputationTerm, Exp>,
) -> Result<Exp, ReflectionError> {
    reflect_computation_inner(env, term, certificates, &mut HashSet::new())
}

pub fn reflect_value_with_certificates(
    env: &CrateEnv,
    value: ValueTerm,
    certificates: &HashMap<ComputationTerm, Exp>,
) -> Result<Exp, ReflectionError> {
    reflect_value_inner(env, value, certificates, &mut HashSet::new())
}

fn reflect_computation_inner(
    env: &CrateEnv,
    term: ComputationTerm,
    certificates: &HashMap<ComputationTerm, Exp>,
    visiting: &mut HashSet<DefId>,
) -> Result<Exp, ReflectionError> {
    if let Some((_, certificate)) = certificates.iter().find(|(candidate, _)| {
        crate::raw::program_calculus::computation_is_alpha_eq(env.arena(), **candidate, term)
    }) {
        return Ok(*certificate);
    }
    let arena = env.arena();
    Ok(match arena.get(term) {
        ComputationTermNode::Meta { .. } => return Err(ReflectionError::UnresolvedMetavariable),
        ComputationTermNode::DefinedConstant(id) => {
            if !visiting.insert(id) {
                return Err(ReflectionError::RecursiveDefinition(id));
            }
            let result = match env.definition(id) {
                DefinedConstant::ProgramComputation {
                    certified_reflection: Some(term),
                    ..
                } => Ok(*term),
                DefinedConstant::ProgramComputation { body, .. } => {
                    reflect_computation_inner(env, *body, certificates, visiting)
                }
                _ => Err(ReflectionError::NotProgramTerm),
            };
            visiting.remove(&id);
            result?
        }
        ComputationTermNode::Return { value } | ComputationTermNode::Force { value } => {
            reflect_value_inner(env, value, certificates, visiting)?
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
                body: reflect_computation_inner(env, body, certificates, visiting)?,
            })
        }
        ComputationTermNode::Application { computation, value } => arena.alloc(ExpNode::App {
            func: reflect_computation_inner(env, computation, certificates, visiting)?,
            arg: reflect_value_inner(env, value, certificates, visiting)?,
        }),
        ComputationTermNode::Sequence {
            computation,
            var,
            value_ty,
            body,
        } => {
            let source = reflect_computation_inner(env, computation, certificates, visiting)?;
            let ty = reflect_value_type(env, value_ty)?;
            let function = arena.alloc(ExpNode::Lam {
                var,
                ty,
                body: reflect_computation_inner(env, body, certificates, visiting)?,
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
                body: reflect_computation_inner(env, body, certificates, visiting)?,
            });
            arena.alloc(ExpNode::App {
                func: function,
                arg: reflect_value_inner(env, value, certificates, visiting)?,
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
                        body: reflect_computation_inner(env, branch.body, certificates, visiting)?,
                    })
                })
                .collect::<Result<_, ReflectionError>>()?;
            arena.alloc(ExpNode::ReflectedProgramCase {
                indspec,
                scrutinee: reflect_value_inner(env, scrutinee, certificates, visiting)?,
                branches: reflected_branches,
            })
        }
        ComputationTermNode::Run { .. } | ComputationTermNode::RunCase { .. } => {
            return Err(ReflectionError::MissingRunCertificate);
        }
    })
}
