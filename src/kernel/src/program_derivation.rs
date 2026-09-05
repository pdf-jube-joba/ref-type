//! Formation and typing derivations for the CBPV Program calculus.

use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum ProgramTypeClass {
    Value,
    Computation,
}

fn context_entry<'a>(
    session: &'a CheckSession<'_, '_>,
    index: usize,
) -> Result<&'a ContextEntry, Box<JudgementError>> {
    session
        .context
        .len()
        .checked_sub(index + 1)
        .and_then(|position| session.context.get(position))
        .ok_or_else(|| {
            failure(
                "Variable",
                "lookup",
                "bound variable index is outside the context",
            )
        })
}

pub(super) fn check_program_type(
    session: &mut CheckSession<'_, '_>,
    ty: RawExp,
) -> Result<ProgramTypeClass, Box<JudgementError>> {
    if check_value_type(session, ty).is_ok() {
        Ok(ProgramTypeClass::Value)
    } else {
        check_computation_type(session, ty).map(|()| ProgramTypeClass::Computation)
    }
}

pub(super) fn check_value_type(
    session: &mut CheckSession<'_, '_>,
    ty: RawExp,
) -> Result<(), Box<JudgementError>> {
    let arena = session.arena();
    let rule = "ValueType";
    let phase = "formation";
    match arena.get(ty) {
        RawNode::Bound(index) => match context_entry(session, index)? {
            ContextEntry::ProgramType { .. } => Ok(()),
            _ => Err(failure(
                rule,
                phase,
                "bound variable is not a Program type variable",
            )),
        },
        RawNode::ModuleParam(parameter) => match session
            .env()
            .module_parameter_opt(parameter)
            .ok_or_else(|| failure(rule, phase, "module parameter not found"))?
        {
            parameter
                if matches!(parameter.kind, ModuleParameterKind::ProgramType)
                    && session.context.iter().any(
                        |entry| matches!(entry, ContextEntry::ProgramType { var } if *var == parameter.name),
                    ) => Ok(()),
            _ => Err(failure(
                rule,
                phase,
                "module parameter is not a Program type variable",
            )),
        },
        RawNode::ThunkType { computation_ty } => check_computation_type(session, computation_ty),
        RawNode::RunStep {
            state_ty,
            result_ty,
        } => {
            check_value_type(session, state_ty)?;
            check_value_type(session, result_ty)
        }
        RawNode::ProgramIndType {
            indspec,
            parameters,
        } => {
            let spec = session.env().program_inductive(indspec);
            if parameters.len() != spec.parameters().len() {
                return Err(failure(
                    rule,
                    phase,
                    "Program datatype parameter count mismatch",
                ));
            }
            for parameter in parameters {
                check_value_type(session, parameter)?;
            }
            Ok(())
        }
        RawNode::Prod { var, ty, body } => {
            if matches!(arena.get(ty), RawNode::ValueType) {
                session.push_program_type(var);
            } else {
                check_value_type(session, ty)?;
                session.push_program_value(var, ty);
            }
            let result = check_value_type(session, body);
            session.pop();
            result
        }
        _ => Err(failure(rule, phase, "expression is not a value type")),
    }
}

pub(super) fn check_computation_type(
    session: &mut CheckSession<'_, '_>,
    ty: RawExp,
) -> Result<(), Box<JudgementError>> {
    let arena = session.arena();
    let rule = "ComputationType";
    let phase = "formation";
    match arena.get(ty) {
        RawNode::ReturnType { value_ty } => check_value_type(session, value_ty),
        RawNode::ComputationFunction { domain, codomain } => {
            check_value_type(session, domain)?;
            check_computation_type(session, codomain)
        }
        _ => Err(failure(rule, phase, "expression is not a computation type")),
    }
}

pub(super) fn check_value(
    session: &mut CheckSession<'_, '_>,
    value: RawExp,
    expected: RawExp,
) -> Result<(), Box<JudgementError>> {
    check_value_type(session, expected)?;
    let inferred = infer_value(session, value)?;
    if exp_is_alpha_eq(session.env(), inferred, expected) {
        Ok(())
    } else {
        Err(failure("Value", "check", "value type mismatch"))
    }
}

pub(super) fn infer_value(
    session: &mut CheckSession<'_, '_>,
    value: RawExp,
) -> Result<RawExp, Box<JudgementError>> {
    let arena = session.arena();
    let rule = "Value";
    let phase = "infer";
    match arena.get(value) {
        RawNode::Bound(index) => match context_entry(session, index)? {
            ContextEntry::ProgramValue { ty, .. } => {
                Ok(shift_bound_indices(arena, *ty, index + 1, 0))
            }
            _ => Err(failure(
                rule,
                phase,
                "bound variable is not a Program value",
            )),
        },
        RawNode::ModuleParam(parameter) => {
            match session
                .env()
                .module_parameter_opt(parameter)
                .ok_or_else(|| failure(rule, phase, "module parameter not found"))?
            {
                parameter
                    if matches!(parameter.kind, ModuleParameterKind::ProgramValue { .. })
                        && session.context.iter().any(
                            |entry| matches!(entry, ContextEntry::ProgramValue { var, .. } if *var == parameter.name),
                        ) => match parameter.kind {
                            ModuleParameterKind::ProgramValue { ty } => Ok(ty),
                            _ => unreachable!(),
                        },
                _ => Err(failure(
                    rule,
                    phase,
                    "module parameter is not a Program value",
                )),
            }
        }
        RawNode::DefinedConstant(definition) => {
            let definition = session.env().definition(definition);
            if definition.kind == DefinitionKind::ProgramValue {
                Ok(definition.ty)
            } else {
                Err(failure(rule, phase, "definition is not a Program value"))
            }
        }
        RawNode::Lam { var, ty, body } => {
            if matches!(arena.get(ty), RawNode::ValueType) {
                session.push_program_type(var);
            } else {
                check_value_type(session, ty)?;
                session.push_program_value(var, ty);
            }
            let body_ty = infer_value(session, body);
            session.pop();
            let body_ty = body_ty?;
            Ok(arena.alloc(RawNode::Prod {
                var,
                ty,
                body: body_ty,
            }))
        }
        RawNode::App { func, arg } => {
            let func_ty = infer_value(session, func)?;
            let Some((_var, domain, codomain)) = expose_product(session.env(), func_ty) else {
                return Err(failure(
                    rule,
                    phase,
                    "Program value application head is not a function",
                ));
            };
            if matches!(arena.get(domain), RawNode::ValueType) {
                check_value_type(session, arg)?;
            } else {
                check_value(session, arg, domain)?;
            }
            Ok(instantiate(arena, codomain, arg))
        }
        RawNode::Thunk { computation } => {
            let computation_ty = infer_computation(session, computation)?;
            Ok(arena.alloc(RawNode::ThunkType { computation_ty }))
        }
        RawNode::Continue {
            state_ty,
            result_ty,
            next,
        } => {
            check_value_type(session, state_ty)?;
            check_value_type(session, result_ty)?;
            check_value(session, next, state_ty)?;
            Ok(run_step_type(arena, state_ty, result_ty))
        }
        RawNode::Finish {
            state_ty,
            result_ty,
            output,
        } => {
            check_value_type(session, state_ty)?;
            check_value_type(session, result_ty)?;
            check_value(session, output, result_ty)?;
            Ok(run_step_type(arena, state_ty, result_ty))
        }
        RawNode::ProgramIndCtor {
            indspec,
            parameters,
            idx,
            fields,
        } => {
            let spec = session.env().program_inductive(indspec);
            if parameters.len() != spec.parameters().len() {
                return Err(failure(
                    rule,
                    phase,
                    "Program constructor parameter count mismatch",
                ));
            }
            for parameter in &parameters {
                check_value_type(session, *parameter)?;
            }
            let constructor = spec
                .constructors()
                .get(idx)
                .ok_or_else(|| failure(rule, phase, "Program constructor index out of bounds"))?;
            let expected_fields = constructor.instantiated_fields(arena, &parameters);
            if fields.len() != expected_fields.len() {
                return Err(failure(
                    rule,
                    phase,
                    "Program constructor field count mismatch",
                ));
            }
            let mut preceding = Vec::new();
            for (field, (_, expected)) in fields.into_iter().zip(expected_fields) {
                let expected = instantiate_telescope(arena, expected, &preceding);
                check_value(session, field, expected)?;
                preceding.push(field);
            }
            Ok(arena.alloc(RawNode::ProgramIndType {
                indspec,
                parameters,
            }))
        }
        RawNode::ProgramIndProjection {
            indspec,
            parameters,
            value,
            field,
        } => {
            let spec = session.env().program_inductive(indspec);
            if spec.constructors().len() != 1 {
                return Err(failure(
                    rule,
                    phase,
                    "Program projection requires a one-constructor structure",
                ));
            }
            if parameters.len() != spec.parameters().len() {
                return Err(failure(
                    rule,
                    phase,
                    "Program projection parameter count mismatch",
                ));
            }
            for parameter in &parameters {
                check_value_type(session, *parameter)?;
            }
            let structure_ty = arena.alloc(RawNode::ProgramIndType {
                indspec,
                parameters: parameters.clone(),
            });
            check_value(session, value, structure_ty)?;
            let fields = spec.constructors()[0].instantiated_fields(arena, &parameters);
            let (_, field_ty) = fields
                .get(field)
                .copied()
                .ok_or_else(|| failure(rule, phase, "Program projection field out of bounds"))?;
            let preceding = (0..field)
                .map(|preceding_field| {
                    arena.alloc(RawNode::ProgramIndProjection {
                        indspec,
                        parameters: parameters.clone(),
                        value,
                        field: preceding_field,
                    })
                })
                .collect::<Vec<_>>();
            Ok(instantiate_telescope(arena, field_ty, &preceding))
        }
        _ => Err(failure(rule, phase, "expression is not a Program value")),
    }
}

pub(super) fn check_computation(
    session: &mut CheckSession<'_, '_>,
    computation: RawExp,
    expected: RawExp,
) -> Result<(), Box<JudgementError>> {
    check_computation_type(session, expected)?;
    let inferred = infer_computation(session, computation)?;
    if exp_is_alpha_eq(session.env(), inferred, expected) {
        Ok(())
    } else {
        Err(failure("Computation", "check", "computation type mismatch"))
    }
}

pub(super) fn infer_computation(
    session: &mut CheckSession<'_, '_>,
    computation: RawExp,
) -> Result<RawExp, Box<JudgementError>> {
    let arena = session.arena();
    let rule = "Computation";
    let phase = "infer";
    match arena.get(computation) {
        RawNode::DefinedConstant(definition) => {
            let definition = session.env().definition(definition);
            if definition.kind == DefinitionKind::ProgramComputation {
                Ok(definition.ty)
            } else {
                Err(failure(
                    rule,
                    phase,
                    "definition is not a Program computation",
                ))
            }
        }
        RawNode::Return { value } => {
            let value_ty = infer_value(session, value)?;
            Ok(arena.alloc(RawNode::ReturnType { value_ty }))
        }
        RawNode::Force { value } => {
            let value_ty = infer_value(session, value)?;
            let RawNode::ThunkType { computation_ty } = arena.get(value_ty) else {
                return Err(failure(
                    rule,
                    phase,
                    "forced value does not have a thunk type",
                ));
            };
            Ok(computation_ty)
        }
        RawNode::ComputationLam {
            var,
            value_ty,
            body,
        } => {
            check_value_type(session, value_ty)?;
            session.push_program_value(var, value_ty);
            let body_ty = infer_computation(session, body);
            session.pop();
            Ok(arena.alloc(RawNode::ComputationFunction {
                domain: value_ty,
                codomain: body_ty?,
            }))
        }
        RawNode::ComputationApp { computation, value } => {
            let computation_ty = infer_computation(session, computation)?;
            let RawNode::ComputationFunction { domain, codomain } = arena.get(computation_ty)
            else {
                return Err(failure(
                    rule,
                    phase,
                    "application head is not a computation function",
                ));
            };
            check_value(session, value, domain)?;
            Ok(codomain)
        }
        RawNode::Sequence {
            computation,
            var,
            value_ty,
            body,
        } => {
            check_value_type(session, value_ty)?;
            let expected_source = arena.alloc(RawNode::ReturnType { value_ty });
            check_computation(session, computation, expected_source)?;
            session.push_program_value(var, value_ty);
            let body_ty = infer_computation(session, body);
            session.pop();
            body_ty
        }
        RawNode::ValueLet { var, value, body } => {
            let value_ty = infer_value(session, value)?;
            session.push_program_value(var, value_ty);
            let body_ty = infer_computation(session, body);
            session.pop();
            body_ty
        }
        RawNode::Run {
            state_ty,
            result_ty,
            step,
            initial,
        } => {
            check_recursion_signature(session, rule, phase, state_ty, result_ty, step)?;
            check_value(session, initial, state_ty)?;
            Ok(arena.alloc(RawNode::ReturnType {
                value_ty: result_ty,
            }))
        }
        RawNode::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => {
            check_recursion_signature(session, rule, phase, state_ty, result_ty, step)?;
            check_value(session, initial, state_ty)?;
            let transition_ty = arena.alloc(RawNode::ReturnType {
                value_ty: run_step_type(arena, state_ty, result_ty),
            });
            check_computation(session, transition, transition_ty)?;
            Ok(arena.alloc(RawNode::ReturnType {
                value_ty: result_ty,
            }))
        }
        RawNode::ProgramCase {
            indspec,
            scrutinee,
            branches,
        } => {
            let scrutinee_ty = infer_value(session, scrutinee)?;
            let RawNode::ProgramIndType {
                indspec: inferred_spec,
                parameters,
            } = arena.get(scrutinee_ty)
            else {
                return Err(failure(
                    rule,
                    phase,
                    "case scrutinee is not a Program datatype",
                ));
            };
            if inferred_spec != indspec {
                return Err(failure(rule, phase, "case datatype annotation mismatch"));
            }
            let spec = session.env().program_inductive(indspec);
            if branches.len() != spec.constructors().len() {
                return Err(failure(
                    rule,
                    phase,
                    "case must contain exactly one branch per constructor",
                ));
            }
            let mut result_ty = None;
            for (branch, constructor) in branches.into_iter().zip(spec.constructors()) {
                let fields = constructor.instantiated_fields(arena, &parameters);
                if branch.binders.len() != fields.len() {
                    return Err(failure(rule, phase, "case branch binder count mismatch"));
                }
                for (binder, (_, field_ty)) in branch.binders.iter().copied().zip(fields) {
                    session.push_program_value(binder, field_ty);
                }
                let branch_ty = infer_computation(session, branch.body);
                for _ in &branch.binders {
                    session.pop();
                }
                let branch_ty =
                    remove_unused_ambient_binders(arena, branch_ty?, branch.binders.len())
                        .ok_or_else(|| {
                            failure(rule, phase, "case result type depends on branch values")
                        })?;
                check_computation_type(session, branch_ty)?;
                if let Some(expected) = result_ty {
                    if !exp_is_alpha_eq(session.env(), expected, branch_ty) {
                        return Err(failure(rule, phase, "case branch result type mismatch"));
                    }
                } else {
                    result_ty = Some(branch_ty);
                }
            }
            result_ty.ok_or_else(|| failure(rule, phase, "cannot infer an empty Program case"))
        }
        _ => Err(failure(
            rule,
            phase,
            "expression is not a Program computation",
        )),
    }
}

fn step_function_type(arena: &Arena, state_ty: RawExp, result_ty: RawExp) -> RawExp {
    let step_result = arena.alloc(RawNode::ReturnType {
        value_ty: run_step_type(arena, state_ty, result_ty),
    });
    let function = arena.alloc(RawNode::ComputationFunction {
        domain: state_ty,
        codomain: step_result,
    });
    arena.alloc(RawNode::ThunkType {
        computation_ty: function,
    })
}

fn check_recursion_signature(
    session: &mut CheckSession<'_, '_>,
    rule: &str,
    phase: &str,
    state_ty: RawExp,
    result_ty: RawExp,
    step: RawExp,
) -> Result<(), Box<JudgementError>> {
    check_value_type(session, state_ty)?;
    check_value_type(session, result_ty)?;
    let expected_step = step_function_type(session.arena(), state_ty, result_ty);
    check_value(session, step, expected_step)
        .map_err(|error| propagate(error, rule, phase, "check CBPV step function"))
}
