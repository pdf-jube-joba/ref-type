//! Formation and typing derivations for the disjoint CBPV Program calculus.

use crate::{
    derivation::JudgementError,
    environment::{CrateEnv, DefinedConstant, ModuleParameterKind},
    exp::Arena,
    ids::{ModuleId, SymbolId},
    program::*,
    program_calculus::{
        computation_type_is_alpha_eq, shift_value_type_indices, value_type_is_alpha_eq,
    },
};
use serde::Serialize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum ProgramTypeClass {
    Value,
    Computation,
}

pub struct ProgramCheckSession<'env, 'context> {
    env: &'env CrateEnv,
    current_module: ModuleId,
    context: &'context mut ProgramContext,
}

impl<'env, 'context> ProgramCheckSession<'env, 'context> {
    pub fn new(
        env: &'env CrateEnv,
        current_module: ModuleId,
        context: &'context mut ProgramContext,
    ) -> Self {
        Self {
            env,
            current_module,
            context,
        }
    }
    pub fn env(&self) -> &'env CrateEnv {
        self.env
    }
    pub fn arena(&self) -> &'env Arena {
        self.env.arena()
    }
    pub fn current_module(&self) -> ModuleId {
        self.current_module
    }
    pub fn context(&self) -> &ProgramContext {
        self.context
    }
    pub fn push_type(&mut self, var: SymbolId) {
        self.context.push(ProgramContextEntry::Type { var });
    }
    pub fn push_value(&mut self, var: SymbolId, ty: ValueType) {
        self.context.push(ProgramContextEntry::Value { var, ty });
    }
    pub fn pop(&mut self) {
        self.context.pop().expect("Program context stack underflow");
    }
    pub fn check_value_type(&mut self, ty: ValueType) -> Result<(), Box<JudgementError>> {
        check_value_type(self, ty)
    }
    pub fn check_computation_type(
        &mut self,
        ty: ComputationType,
    ) -> Result<(), Box<JudgementError>> {
        check_computation_type(self, ty)
    }
    pub fn check_value(&mut self, value: Value, ty: ValueType) -> Result<(), Box<JudgementError>> {
        check_value(self, value, ty)
    }
    pub fn infer_value(&mut self, value: Value) -> Result<ValueType, Box<JudgementError>> {
        infer_value(self, value)
    }
    pub fn check_computation(
        &mut self,
        term: Computation,
        ty: ComputationType,
    ) -> Result<(), Box<JudgementError>> {
        check_computation(self, term, ty)
    }
    pub fn infer_computation(
        &mut self,
        term: Computation,
    ) -> Result<ComputationType, Box<JudgementError>> {
        infer_computation(self, term)
    }
    pub fn infer_judgement(
        &mut self,
        program: Program,
    ) -> Result<ProgramJudgement, Box<JudgementError>> {
        match program {
            Program::Value(value) => Ok(ProgramJudgement::Value {
                value,
                ty: self.infer_value(value)?,
            }),
            Program::Computation(computation) => Ok(ProgramJudgement::Computation {
                computation,
                ty: self.infer_computation(computation)?,
            }),
        }
    }
}

fn failure(rule: &str, phase: &str, cause: &str) -> Box<JudgementError> {
    Box::new(JudgementError::caused(cause).with_frame(rule, phase, "well-typed Program syntax"))
}

fn context_entry(
    session: &ProgramCheckSession<'_, '_>,
    index: usize,
) -> Result<ProgramContextEntry, Box<JudgementError>> {
    session
        .context
        .len()
        .checked_sub(index + 1)
        .and_then(|p| session.context.get(p))
        .cloned()
        .ok_or_else(|| {
            failure(
                "Variable",
                "lookup",
                "bound variable index is outside the Program context",
            )
        })
}

pub fn check_value_type(
    session: &mut ProgramCheckSession<'_, '_>,
    ty: ValueType,
) -> Result<(), Box<JudgementError>> {
    match session.arena().get(ty) {
        ValueTypeNode::Bound(index) => match context_entry(session, index)? {
            ProgramContextEntry::Type { .. } => Ok(()),
            _ => Err(failure(
                "ValueType",
                "formation",
                "bound variable is not a Program type variable",
            )),
        },
        ValueTypeNode::ModuleParam(id) => match session.env.module_parameter_opt(id) {
            Some(p) if matches!(p.kind, ModuleParameterKind::ProgramType) => Ok(()),
            _ => Err(failure(
                "ValueType",
                "formation",
                "module parameter is not a Program type parameter",
            )),
        },
        ValueTypeNode::Meta { .. } => {
            Err(failure("ValueType", "formation", "unresolved metavariable"))
        }
        ValueTypeNode::Thunk { computation_ty } => check_computation_type(session, computation_ty),
        ValueTypeNode::RunStep {
            state_ty,
            result_ty,
        } => {
            check_value_type(session, state_ty)?;
            check_value_type(session, result_ty)
        }
        ValueTypeNode::Inductive {
            indspec,
            parameters,
        } => {
            if parameters.len() != session.env.program_inductive(indspec).parameters().len() {
                return Err(failure(
                    "ValueType",
                    "formation",
                    "Program datatype parameter count mismatch",
                ));
            }
            for parameter in parameters {
                check_value_type(session, parameter)?;
            }
            Ok(())
        }
    }
}

pub fn check_computation_type(
    session: &mut ProgramCheckSession<'_, '_>,
    ty: ComputationType,
) -> Result<(), Box<JudgementError>> {
    match session.arena().get(ty) {
        ComputationTypeNode::Meta { .. } => Err(failure(
            "ComputationType",
            "formation",
            "unresolved metavariable",
        )),
        ComputationTypeNode::Return { value_ty } => check_value_type(session, value_ty),
        ComputationTypeNode::Function { domain, codomain } => {
            check_value_type(session, domain)?;
            check_computation_type(session, codomain)
        }
    }
}

pub fn check_value(
    session: &mut ProgramCheckSession<'_, '_>,
    value: Value,
    expected: ValueType,
) -> Result<(), Box<JudgementError>> {
    check_value_type(session, expected)?;
    let inferred = infer_value(session, value)?;
    if value_type_is_alpha_eq(session.arena(), inferred, expected) {
        Ok(())
    } else {
        Err(failure("Value", "check", "value type mismatch"))
    }
}

pub fn infer_value(
    session: &mut ProgramCheckSession<'_, '_>,
    value: Value,
) -> Result<ValueType, Box<JudgementError>> {
    let arena = session.arena();
    match arena.get(value) {
        ValueNode::Bound(index) => match context_entry(session, index)? {
            ProgramContextEntry::Value { ty, .. } => {
                Ok(shift_value_type_indices(arena, ty, index + 1, 0))
            }
            _ => Err(failure(
                "Value",
                "infer",
                "bound variable is not a Program value",
            )),
        },
        ValueNode::ModuleParam(id) => session
            .env
            .module_parameter_opt(id)
            .and_then(|p| p.value_ty())
            .ok_or_else(|| failure("Value", "infer", "module parameter is not a Program value")),
        ValueNode::Meta { .. } => Err(failure("Value", "infer", "unresolved metavariable")),
        ValueNode::DefinedConstant(id) => match session.env.definition(id) {
            DefinedConstant::ProgramValue { ty, .. } => Ok(*ty),
            _ => Err(failure(
                "Value",
                "infer",
                "definition is not a Program value",
            )),
        },
        ValueNode::Thunk { computation } => Ok(arena.alloc(ValueTypeNode::Thunk {
            computation_ty: infer_computation(session, computation)?,
        })),
        ValueNode::Continue {
            state_ty,
            result_ty,
            next,
        } => {
            check_value_type(session, state_ty)?;
            check_value_type(session, result_ty)?;
            check_value(session, next, state_ty)?;
            Ok(arena.alloc(ValueTypeNode::RunStep {
                state_ty,
                result_ty,
            }))
        }
        ValueNode::Finish {
            state_ty,
            result_ty,
            output,
        } => {
            check_value_type(session, state_ty)?;
            check_value_type(session, result_ty)?;
            check_value(session, output, result_ty)?;
            Ok(arena.alloc(ValueTypeNode::RunStep {
                state_ty,
                result_ty,
            }))
        }
        ValueNode::InductiveConstructor {
            indspec,
            parameters,
            idx,
            fields,
        } => {
            let spec = session.env.program_inductive(indspec);
            if parameters.len() != spec.parameters().len() {
                return Err(failure(
                    "Value",
                    "infer",
                    "Program constructor parameter count mismatch",
                ));
            }
            for ty in &parameters {
                check_value_type(session, *ty)?;
            }
            let expected = spec
                .constructors()
                .get(idx)
                .ok_or_else(|| {
                    failure("Value", "infer", "Program constructor index out of bounds")
                })?
                .instantiated_fields(arena, &parameters);
            if expected.len() != fields.len() {
                return Err(failure(
                    "Value",
                    "infer",
                    "Program constructor field count mismatch",
                ));
            }
            for (field, (_, ty)) in fields.into_iter().zip(expected) {
                check_value(session, field, ty)?;
            }
            Ok(arena.alloc(ValueTypeNode::Inductive {
                indspec,
                parameters,
            }))
        }
        ValueNode::InductiveProjection {
            indspec,
            parameters,
            value,
            field,
        } => {
            let spec = session.env.program_inductive(indspec);
            if spec.constructors().len() != 1 {
                return Err(failure(
                    "Value",
                    "infer",
                    "Program projection requires a one-constructor structure",
                ));
            }
            let structure = arena.alloc(ValueTypeNode::Inductive {
                indspec,
                parameters: parameters.clone(),
            });
            check_value(session, value, structure)?;
            spec.constructors()[0]
                .instantiated_fields(arena, &parameters)
                .get(field)
                .map(|(_, ty)| *ty)
                .ok_or_else(|| failure("Value", "infer", "Program projection field out of bounds"))
        }
    }
}

pub fn check_computation(
    session: &mut ProgramCheckSession<'_, '_>,
    term: Computation,
    expected: ComputationType,
) -> Result<(), Box<JudgementError>> {
    check_computation_type(session, expected)?;
    let inferred = infer_computation(session, term)?;
    if computation_type_is_alpha_eq(session.arena(), inferred, expected) {
        Ok(())
    } else {
        Err(failure("Computation", "check", "computation type mismatch"))
    }
}

pub fn infer_computation(
    session: &mut ProgramCheckSession<'_, '_>,
    term: Computation,
) -> Result<ComputationType, Box<JudgementError>> {
    let arena = session.arena();
    match arena.get(term) {
        ComputationNode::Meta { .. } => {
            Err(failure("Computation", "infer", "unresolved metavariable"))
        }
        ComputationNode::DefinedConstant(id) => match session.env.definition(id) {
            DefinedConstant::ProgramComputation { ty, .. } => Ok(*ty),
            _ => Err(failure(
                "Computation",
                "infer",
                "definition is not a Program computation",
            )),
        },
        ComputationNode::Return { value } => Ok(arena.alloc(ComputationTypeNode::Return {
            value_ty: infer_value(session, value)?,
        })),
        ComputationNode::Force { value } => match arena.get(infer_value(session, value)?) {
            ValueTypeNode::Thunk { computation_ty } => Ok(computation_ty),
            _ => Err(failure(
                "Computation",
                "infer",
                "forced value does not have a thunk type",
            )),
        },
        ComputationNode::Lambda {
            var,
            value_ty,
            body,
        } => {
            check_value_type(session, value_ty)?;
            session.push_value(var, value_ty);
            let body_ty = infer_computation(session, body);
            session.pop();
            Ok(arena.alloc(ComputationTypeNode::Function {
                domain: value_ty,
                codomain: remove_context_entry_from_computation_type(arena, body_ty?, 0)?,
            }))
        }
        ComputationNode::Application { computation, value } => {
            match arena.get(infer_computation(session, computation)?) {
                ComputationTypeNode::Function { domain, codomain } => {
                    check_value(session, value, domain)?;
                    Ok(codomain)
                }
                _ => Err(failure(
                    "Computation",
                    "infer",
                    "application head is not a computation function",
                )),
            }
        }
        ComputationNode::Sequence {
            computation,
            var,
            value_ty,
            body,
        } => {
            check_value_type(session, value_ty)?;
            let source = arena.alloc(ComputationTypeNode::Return { value_ty });
            check_computation(session, computation, source)?;
            session.push_value(var, value_ty);
            let result = infer_computation(session, body);
            session.pop();
            remove_context_entry_from_computation_type(arena, result?, 0)
        }
        ComputationNode::ValueLet { var, value, body } => {
            let ty = infer_value(session, value)?;
            session.push_value(var, ty);
            let result = infer_computation(session, body);
            session.pop();
            remove_context_entry_from_computation_type(arena, result?, 0)
        }
        ComputationNode::Run {
            state_ty,
            result_ty,
            step,
            initial,
        } => {
            check_recursion_signature(session, state_ty, result_ty, step)?;
            check_value(session, initial, state_ty)?;
            Ok(arena.alloc(ComputationTypeNode::Return {
                value_ty: result_ty,
            }))
        }
        ComputationNode::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => {
            check_recursion_signature(session, state_ty, result_ty, step)?;
            check_value(session, initial, state_ty)?;
            let step_ty = arena.alloc(ValueTypeNode::RunStep {
                state_ty,
                result_ty,
            });
            let transition_ty = arena.alloc(ComputationTypeNode::Return { value_ty: step_ty });
            check_computation(session, transition, transition_ty)?;
            Ok(arena.alloc(ComputationTypeNode::Return {
                value_ty: result_ty,
            }))
        }
        ComputationNode::Case {
            indspec,
            scrutinee,
            branches,
        } => {
            let ValueTypeNode::Inductive {
                indspec: actual,
                parameters,
            } = arena.get(infer_value(session, scrutinee)?)
            else {
                return Err(failure(
                    "Computation",
                    "infer",
                    "case scrutinee is not a Program datatype",
                ));
            };
            if actual != indspec {
                return Err(failure(
                    "Computation",
                    "infer",
                    "case datatype annotation mismatch",
                ));
            }
            let constructors = session
                .env
                .program_inductive(indspec)
                .constructors()
                .to_vec();
            if branches.len() != constructors.len() {
                return Err(failure(
                    "Computation",
                    "infer",
                    "case branch count mismatch",
                ));
            }
            let mut result = None;
            for (branch, constructor) in branches.into_iter().zip(constructors) {
                let fields = constructor.instantiated_fields(arena, &parameters);
                if fields.len() != branch.binders.len() {
                    return Err(failure(
                        "Computation",
                        "infer",
                        "case branch binder count mismatch",
                    ));
                }
                for (binder, (_, ty)) in branch.binders.iter().copied().zip(fields) {
                    session.push_value(binder, ty);
                }
                let branch_ty = infer_computation(session, branch.body);
                for _ in &branch.binders {
                    session.pop();
                }
                let mut branch_ty = branch_ty?;
                for _ in &branch.binders {
                    branch_ty = remove_context_entry_from_computation_type(arena, branch_ty, 0)?;
                }
                if let Some(expected) = result {
                    if !computation_type_is_alpha_eq(arena, expected, branch_ty) {
                        return Err(failure(
                            "Computation",
                            "infer",
                            "case branch result type mismatch",
                        ));
                    }
                } else {
                    result = Some(branch_ty);
                }
            }
            result.ok_or_else(|| {
                failure("Computation", "infer", "cannot infer an empty Program case")
            })
        }
    }
}

fn remove_context_entry_from_value_type(
    arena: &Arena,
    ty: ValueType,
    target: usize,
) -> Result<ValueType, Box<JudgementError>> {
    Ok(match arena.get(ty) {
        ValueTypeNode::Bound(index) if index == target => {
            return Err(failure(
                "ProgramContext",
                "strengthening",
                "a Program type depends on a value binder",
            ));
        }
        ValueTypeNode::Bound(index) if index > target => arena.value_type_bound(index - 1),
        ValueTypeNode::Thunk { computation_ty } => arena.alloc(ValueTypeNode::Thunk {
            computation_ty: remove_context_entry_from_computation_type(
                arena,
                computation_ty,
                target,
            )?,
        }),
        ValueTypeNode::RunStep {
            state_ty,
            result_ty,
        } => arena.alloc(ValueTypeNode::RunStep {
            state_ty: remove_context_entry_from_value_type(arena, state_ty, target)?,
            result_ty: remove_context_entry_from_value_type(arena, result_ty, target)?,
        }),
        ValueTypeNode::Inductive {
            indspec,
            parameters,
        } => arena.alloc(ValueTypeNode::Inductive {
            indspec,
            parameters: parameters
                .into_iter()
                .map(|parameter| remove_context_entry_from_value_type(arena, parameter, target))
                .collect::<Result<_, _>>()?,
        }),
        node => arena.alloc(node),
    })
}

fn remove_context_entry_from_computation_type(
    arena: &Arena,
    ty: ComputationType,
    target: usize,
) -> Result<ComputationType, Box<JudgementError>> {
    Ok(match arena.get(ty) {
        ComputationTypeNode::Return { value_ty } => arena.alloc(ComputationTypeNode::Return {
            value_ty: remove_context_entry_from_value_type(arena, value_ty, target)?,
        }),
        ComputationTypeNode::Function { domain, codomain } => {
            arena.alloc(ComputationTypeNode::Function {
                domain: remove_context_entry_from_value_type(arena, domain, target)?,
                codomain: remove_context_entry_from_computation_type(arena, codomain, target)?,
            })
        }
        node => arena.alloc(node),
    })
}

fn check_recursion_signature(
    session: &mut ProgramCheckSession<'_, '_>,
    state_ty: ValueType,
    result_ty: ValueType,
    step: Value,
) -> Result<(), Box<JudgementError>> {
    check_value_type(session, state_ty)?;
    check_value_type(session, result_ty)?;
    let arena = session.arena();
    let step_result = arena.alloc(ValueTypeNode::RunStep {
        state_ty,
        result_ty,
    });
    let returned = arena.alloc(ComputationTypeNode::Return {
        value_ty: step_result,
    });
    let function = arena.alloc(ComputationTypeNode::Function {
        domain: state_ty,
        codomain: returned,
    });
    let expected = arena.alloc(ValueTypeNode::Thunk {
        computation_ty: function,
    });
    check_value(session, step, expected)
}
