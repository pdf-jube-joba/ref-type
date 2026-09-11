//! Structural operations and weak call-by-value evaluation for Program syntax.

use std::collections::HashMap;

use crate::raw::{
    environment::{CrateEnv, DefinedConstant, ModuleArgument},
    exp::Arena,
    ids::{DefId, ModuleParamId, ProgramInductiveId},
    program::*,
};

pub fn program_type_is_alpha_eq(arena: &Arena, left: ProgramType, right: ProgramType) -> bool {
    match (left, right) {
        (ProgramType::ValueType(left), ProgramType::ValueType(right)) => {
            value_type_is_alpha_eq(arena, left, right)
        }
        (ProgramType::ComputationType(left), ProgramType::ComputationType(right)) => {
            computation_type_is_alpha_eq(arena, left, right)
        }
        _ => false,
    }
}

pub fn program_is_alpha_eq(arena: &Arena, left: ProgramTerm, right: ProgramTerm) -> bool {
    match (left, right) {
        (ProgramTerm::ValueTerm(left), ProgramTerm::ValueTerm(right)) => {
            value_is_alpha_eq(arena, left, right)
        }
        (ProgramTerm::ComputationTerm(left), ProgramTerm::ComputationTerm(right)) => {
            computation_is_alpha_eq(arena, left, right)
        }
        _ => false,
    }
}

pub fn value_type_is_alpha_eq(arena: &Arena, left: ValueType, right: ValueType) -> bool {
    if left == right {
        return true;
    }
    match (arena.get(left), arena.get(right)) {
        (ValueTypeNode::Bound(left), ValueTypeNode::Bound(right)) => left == right,
        (ValueTypeNode::ModuleParam(left), ValueTypeNode::ModuleParam(right)) => left == right,
        (
            ValueTypeNode::Meta {
                metavariable: left,
                spine: left_spine,
            },
            ValueTypeNode::Meta {
                metavariable: right,
                spine: right_spine,
            },
        ) => left == right && program_arguments_alpha_eq(arena, &left_spine, &right_spine),
        (
            ValueTypeNode::Thunk {
                computation_ty: left,
            },
            ValueTypeNode::Thunk {
                computation_ty: right,
            },
        ) => computation_type_is_alpha_eq(arena, left, right),
        (
            ValueTypeNode::RunStep {
                state_ty: left_state,
                result_ty: left_result,
            },
            ValueTypeNode::RunStep {
                state_ty: right_state,
                result_ty: right_result,
            },
        ) => {
            value_type_is_alpha_eq(arena, left_state, right_state)
                && value_type_is_alpha_eq(arena, left_result, right_result)
        }
        (
            ValueTypeNode::Inductive {
                indspec: left,
                parameters: left_parameters,
            },
            ValueTypeNode::Inductive {
                indspec: right,
                parameters: right_parameters,
            },
        ) => {
            left == right
                && left_parameters.len() == right_parameters.len()
                && left_parameters
                    .into_iter()
                    .zip(right_parameters)
                    .all(|(left, right)| value_type_is_alpha_eq(arena, left, right))
        }
        _ => false,
    }
}

pub fn computation_type_is_alpha_eq(
    arena: &Arena,
    left: ComputationType,
    right: ComputationType,
) -> bool {
    if left == right {
        return true;
    }
    match (arena.get(left), arena.get(right)) {
        (
            ComputationTypeNode::Meta {
                metavariable: left,
                spine: left_spine,
            },
            ComputationTypeNode::Meta {
                metavariable: right,
                spine: right_spine,
            },
        ) => left == right && program_arguments_alpha_eq(arena, &left_spine, &right_spine),
        (
            ComputationTypeNode::Return { value_ty: left },
            ComputationTypeNode::Return { value_ty: right },
        ) => value_type_is_alpha_eq(arena, left, right),
        (
            ComputationTypeNode::Function {
                domain: left_domain,
                codomain: left_codomain,
            },
            ComputationTypeNode::Function {
                domain: right_domain,
                codomain: right_codomain,
            },
        ) => {
            value_type_is_alpha_eq(arena, left_domain, right_domain)
                && computation_type_is_alpha_eq(arena, left_codomain, right_codomain)
        }
        _ => false,
    }
}

fn program_arguments_alpha_eq(
    arena: &Arena,
    left: &[ProgramArgument],
    right: &[ProgramArgument],
) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| match (*left, *right) {
                (ProgramArgument::ValueType(left), ProgramArgument::ValueType(right)) => {
                    value_type_is_alpha_eq(arena, left, right)
                }
                (ProgramArgument::ValueTerm(left), ProgramArgument::ValueTerm(right)) => {
                    value_is_alpha_eq(arena, left, right)
                }
                _ => false,
            })
}

pub fn value_is_alpha_eq(arena: &Arena, left: ValueTerm, right: ValueTerm) -> bool {
    if left == right {
        return true;
    }
    match (arena.get(left), arena.get(right)) {
        (ValueTermNode::Bound(left), ValueTermNode::Bound(right)) => left == right,
        (ValueTermNode::ModuleParam(left), ValueTermNode::ModuleParam(right)) => left == right,
        (
            ValueTermNode::DefinitionInstance {
                definition: left,
                parameters: lp,
            },
            ValueTermNode::DefinitionInstance {
                definition: right,
                parameters: rp,
            },
        ) => {
            left == right
                && lp.len() == rp.len()
                && lp
                    .iter()
                    .zip(rp)
                    .all(|(l, r)| value_type_is_alpha_eq(arena, *l, r))
        }
        (ValueTermNode::DefinedConstant(left), ValueTermNode::DefinedConstant(right)) => {
            left == right
        }
        (
            ValueTermNode::Meta {
                metavariable: left,
                spine: left_spine,
            },
            ValueTermNode::Meta {
                metavariable: right,
                spine: right_spine,
            },
        ) => left == right && program_arguments_alpha_eq(arena, &left_spine, &right_spine),
        (
            ValueTermNode::Thunk { computation: left },
            ValueTermNode::Thunk { computation: right },
        ) => computation_is_alpha_eq(arena, left, right),
        (
            ValueTermNode::Continue {
                state_ty: ls,
                result_ty: lr,
                next: ln,
            },
            ValueTermNode::Continue {
                state_ty: rs,
                result_ty: rr,
                next: rn,
            },
        ) => {
            value_type_is_alpha_eq(arena, ls, rs)
                && value_type_is_alpha_eq(arena, lr, rr)
                && value_is_alpha_eq(arena, ln, rn)
        }
        (
            ValueTermNode::Finish {
                state_ty: ls,
                result_ty: lr,
                output: lo,
            },
            ValueTermNode::Finish {
                state_ty: rs,
                result_ty: rr,
                output: ro,
            },
        ) => {
            value_type_is_alpha_eq(arena, ls, rs)
                && value_type_is_alpha_eq(arena, lr, rr)
                && value_is_alpha_eq(arena, lo, ro)
        }
        (
            ValueTermNode::InductiveConstructor {
                indspec: li,
                parameters: lp,
                idx: lx,
                fields: lf,
            },
            ValueTermNode::InductiveConstructor {
                indspec: ri,
                parameters: rp,
                idx: rx,
                fields: rf,
            },
        ) => {
            li == ri
                && lx == rx
                && value_types_alpha_eq(arena, &lp, &rp)
                && values_alpha_eq(arena, &lf, &rf)
        }
        _ => false,
    }
}

pub fn computation_is_alpha_eq(
    arena: &Arena,
    left: ComputationTerm,
    right: ComputationTerm,
) -> bool {
    if left == right {
        return true;
    }
    match (arena.get(left), arena.get(right)) {
        (
            ComputationTermNode::DefinitionInstance {
                definition: left,
                parameters: lp,
            },
            ComputationTermNode::DefinitionInstance {
                definition: right,
                parameters: rp,
            },
        ) => {
            left == right
                && lp.len() == rp.len()
                && lp
                    .iter()
                    .zip(rp)
                    .all(|(l, r)| value_type_is_alpha_eq(arena, *l, r))
        }
        (
            ComputationTermNode::DefinedConstant(left),
            ComputationTermNode::DefinedConstant(right),
        ) => left == right,
        (
            ComputationTermNode::Meta {
                metavariable: left,
                spine: ls,
            },
            ComputationTermNode::Meta {
                metavariable: right,
                spine: rs,
            },
        ) => left == right && program_arguments_alpha_eq(arena, &ls, &rs),
        (
            ComputationTermNode::Return { value: left },
            ComputationTermNode::Return { value: right },
        )
        | (
            ComputationTermNode::Force { value: left },
            ComputationTermNode::Force { value: right },
        ) => value_is_alpha_eq(arena, left, right),
        (
            ComputationTermNode::Lambda {
                value_ty: lt,
                body: lb,
                ..
            },
            ComputationTermNode::Lambda {
                value_ty: rt,
                body: rb,
                ..
            },
        ) => value_type_is_alpha_eq(arena, lt, rt) && computation_is_alpha_eq(arena, lb, rb),
        (
            ComputationTermNode::Application {
                computation: lc,
                value: lv,
            },
            ComputationTermNode::Application {
                computation: rc,
                value: rv,
            },
        ) => computation_is_alpha_eq(arena, lc, rc) && value_is_alpha_eq(arena, lv, rv),
        (
            ComputationTermNode::Sequence {
                computation: lc,
                value_ty: lt,
                body: lb,
                ..
            },
            ComputationTermNode::Sequence {
                computation: rc,
                value_ty: rt,
                body: rb,
                ..
            },
        ) => {
            computation_is_alpha_eq(arena, lc, rc)
                && value_type_is_alpha_eq(arena, lt, rt)
                && computation_is_alpha_eq(arena, lb, rb)
        }
        (
            ComputationTermNode::ValueLet {
                value_ty: lt,
                value: lv,
                body: lb,
                ..
            },
            ComputationTermNode::ValueLet {
                value_ty: rt,
                value: rv,
                body: rb,
                ..
            },
        ) => {
            value_type_is_alpha_eq(arena, lt, rt)
                && value_is_alpha_eq(arena, lv, rv)
                && computation_is_alpha_eq(arena, lb, rb)
        }
        (
            ComputationTermNode::Case {
                indspec: li,
                scrutinee: ls,
                branches: lb,
            },
            ComputationTermNode::Case {
                indspec: ri,
                scrutinee: rs,
                branches: rb,
            },
        ) => {
            li == ri
                && value_is_alpha_eq(arena, ls, rs)
                && lb.len() == rb.len()
                && lb.iter().zip(rb).all(|(left, right)| {
                    left.binders.len() == right.binders.len()
                        && computation_is_alpha_eq(arena, left.body, right.body)
                })
        }
        (
            ComputationTermNode::Run {
                state_ty: ls,
                result_ty: lr,
                step: lp,
                initial: li,
            },
            ComputationTermNode::Run {
                state_ty: rs,
                result_ty: rr,
                step: rp,
                initial: ri,
            },
        ) => {
            value_type_is_alpha_eq(arena, ls, rs)
                && value_type_is_alpha_eq(arena, lr, rr)
                && value_is_alpha_eq(arena, lp, rp)
                && value_is_alpha_eq(arena, li, ri)
        }
        (
            ComputationTermNode::RunCase {
                state_ty: ls,
                result_ty: lr,
                step: lp,
                initial: li,
                transition: lt,
            },
            ComputationTermNode::RunCase {
                state_ty: rs,
                result_ty: rr,
                step: rp,
                initial: ri,
                transition: rt,
            },
        ) => {
            value_type_is_alpha_eq(arena, ls, rs)
                && value_type_is_alpha_eq(arena, lr, rr)
                && value_is_alpha_eq(arena, lp, rp)
                && value_is_alpha_eq(arena, li, ri)
                && computation_is_alpha_eq(arena, lt, rt)
        }
        _ => false,
    }
}

fn value_types_alpha_eq(arena: &Arena, left: &[ValueType], right: &[ValueType]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(l, r)| value_type_is_alpha_eq(arena, *l, *r))
}

fn values_alpha_eq(arena: &Arena, left: &[ValueTerm], right: &[ValueTerm]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(l, r)| value_is_alpha_eq(arena, *l, *r))
}

pub fn shift_value_type_indices(
    arena: &Arena,
    ty: ValueType,
    amount: usize,
    cutoff: usize,
) -> ValueType {
    if amount == 0 {
        return ty;
    }

    fn go(arena: &Arena, ty: ValueType, amount: usize, cutoff: usize) -> ValueType {
        match arena.get(ty) {
            ValueTypeNode::Bound(index) if index >= cutoff => {
                arena.reuse_value_type(ty, ValueTypeNode::Bound(index + amount))
            }
            ValueTypeNode::Thunk { computation_ty } => arena.reuse_value_type(
                ty,
                ValueTypeNode::Thunk {
                    computation_ty: shift_computation_type_indices(
                        arena,
                        computation_ty,
                        amount,
                        cutoff,
                    ),
                },
            ),
            ValueTypeNode::RunStep {
                state_ty,
                result_ty,
            } => arena.reuse_value_type(
                ty,
                ValueTypeNode::RunStep {
                    state_ty: go(arena, state_ty, amount, cutoff),
                    result_ty: go(arena, result_ty, amount, cutoff),
                },
            ),
            ValueTypeNode::Inductive {
                indspec,
                parameters,
            } => arena.reuse_value_type(
                ty,
                ValueTypeNode::Inductive {
                    indspec,
                    parameters: parameters
                        .into_iter()
                        .map(|p| go(arena, p, amount, cutoff))
                        .collect(),
                },
            ),
            _ => ty,
        }
    }
    go(arena, ty, amount, cutoff)
}

pub fn shift_computation_type_indices(
    arena: &Arena,
    ty: ComputationType,
    amount: usize,
    cutoff: usize,
) -> ComputationType {
    if amount == 0 {
        return ty;
    }
    match arena.get(ty) {
        ComputationTypeNode::Return { value_ty } => arena.reuse_computation_type(
            ty,
            ComputationTypeNode::Return {
                value_ty: shift_value_type_indices(arena, value_ty, amount, cutoff),
            },
        ),
        ComputationTypeNode::Function { domain, codomain } => arena.reuse_computation_type(
            ty,
            ComputationTypeNode::Function {
                domain: shift_value_type_indices(arena, domain, amount, cutoff),
                codomain: shift_computation_type_indices(arena, codomain, amount, cutoff),
            },
        ),
        ComputationTypeNode::Meta { .. } => ty,
    }
}

pub fn instantiate_value_type(
    arena: &Arena,
    body: ValueType,
    argument: ValueType,
    target: usize,
) -> ValueType {
    fn go(arena: &Arena, ty: ValueType, arg: ValueType, target: usize) -> ValueType {
        match arena.get(ty) {
            ValueTypeNode::Bound(index) if index == target => {
                shift_value_type_indices(arena, arg, target, 0)
            }
            ValueTypeNode::Bound(index) if index > target => {
                arena.reuse_value_type(ty, ValueTypeNode::Bound(index - 1))
            }
            ValueTypeNode::Thunk { computation_ty } => arena.reuse_value_type(
                ty,
                ValueTypeNode::Thunk {
                    computation_ty: instantiate_computation_type(
                        arena,
                        computation_ty,
                        arg,
                        target,
                    ),
                },
            ),
            ValueTypeNode::RunStep {
                state_ty,
                result_ty,
            } => arena.reuse_value_type(
                ty,
                ValueTypeNode::RunStep {
                    state_ty: go(arena, state_ty, arg, target),
                    result_ty: go(arena, result_ty, arg, target),
                },
            ),
            ValueTypeNode::Inductive {
                indspec,
                parameters,
            } => arena.reuse_value_type(
                ty,
                ValueTypeNode::Inductive {
                    indspec,
                    parameters: parameters
                        .into_iter()
                        .map(|p| go(arena, p, arg, target))
                        .collect(),
                },
            ),
            _ => ty,
        }
    }
    go(arena, body, argument, target)
}

pub fn instantiate_computation_type(
    arena: &Arena,
    body: ComputationType,
    argument: ValueType,
    target: usize,
) -> ComputationType {
    match arena.get(body) {
        ComputationTypeNode::Return { value_ty } => arena.reuse_computation_type(
            body,
            ComputationTypeNode::Return {
                value_ty: instantiate_value_type(arena, value_ty, argument, target),
            },
        ),
        ComputationTypeNode::Function { domain, codomain } => arena.reuse_computation_type(
            body,
            ComputationTypeNode::Function {
                domain: instantiate_value_type(arena, domain, argument, target),
                codomain: instantiate_computation_type(arena, codomain, argument, target),
            },
        ),
        ComputationTypeNode::Meta { .. } => body,
    }
}

pub fn instantiate_type_telescope(
    arena: &Arena,
    ty: ValueType,
    arguments: &[ValueType],
) -> ValueType {
    crate::raw::program_definitions::instantiate_value_type(arena, ty, arguments, 0)
}

/// Removes one value binder from a value type, adjusting outer de Bruijn
/// indices. Returns `None` when the type depends on the binder being removed.
pub fn strengthen_value_type(arena: &Arena, ty: ValueType, target: usize) -> Option<ValueType> {
    match arena.get(ty) {
        ValueTypeNode::Bound(index) if index == target => None,
        ValueTypeNode::Bound(index) if index > target => Some(arena.value_type_bound(index - 1)),
        ValueTypeNode::Thunk { computation_ty } => {
            let strengthened = strengthen_computation_type(arena, computation_ty, target)?;
            if strengthened == computation_ty {
                Some(ty)
            } else {
                Some(arena.alloc(ValueTypeNode::Thunk {
                    computation_ty: strengthened,
                }))
            }
        }
        ValueTypeNode::RunStep {
            state_ty,
            result_ty,
        } => {
            let strengthened_state = strengthen_value_type(arena, state_ty, target)?;
            let strengthened_result = strengthen_value_type(arena, result_ty, target)?;
            if strengthened_state == state_ty && strengthened_result == result_ty {
                Some(ty)
            } else {
                Some(arena.alloc(ValueTypeNode::RunStep {
                    state_ty: strengthened_state,
                    result_ty: strengthened_result,
                }))
            }
        }
        ValueTypeNode::Inductive {
            indspec,
            mut parameters,
        } => {
            let mut changed = false;
            for parameter in &mut parameters {
                let original = *parameter;
                *parameter = strengthen_value_type(arena, original, target)?;
                changed |= *parameter != original;
            }
            if changed {
                Some(arena.alloc(ValueTypeNode::Inductive {
                    indspec,
                    parameters,
                }))
            } else {
                Some(ty)
            }
        }
        _ => Some(ty),
    }
}

/// Removes one value binder from a computation type, adjusting outer de
/// Bruijn indices. Returns `None` when the type depends on that binder.
pub fn strengthen_computation_type(
    arena: &Arena,
    ty: ComputationType,
    target: usize,
) -> Option<ComputationType> {
    match arena.get(ty) {
        ComputationTypeNode::Return { value_ty } => {
            let strengthened = strengthen_value_type(arena, value_ty, target)?;
            if strengthened == value_ty {
                Some(ty)
            } else {
                Some(arena.alloc(ComputationTypeNode::Return {
                    value_ty: strengthened,
                }))
            }
        }
        ComputationTypeNode::Function { domain, codomain } => {
            let strengthened_domain = strengthen_value_type(arena, domain, target)?;
            let strengthened_codomain = strengthen_computation_type(arena, codomain, target)?;
            if strengthened_domain == domain && strengthened_codomain == codomain {
                Some(ty)
            } else {
                Some(arena.alloc(ComputationTypeNode::Function {
                    domain: strengthened_domain,
                    codomain: strengthened_codomain,
                }))
            }
        }
        ComputationTypeNode::Meta { .. } => Some(ty),
    }
}

pub fn shift_value_indices(
    arena: &Arena,
    value: ValueTerm,
    amount: usize,
    cutoff: usize,
) -> ValueTerm {
    if amount == 0 {
        return value;
    }

    fn go(arena: &Arena, value: ValueTerm, amount: usize, cutoff: usize) -> ValueTerm {
        match arena.get(value) {
            ValueTermNode::DefinitionInstance {
                definition,
                parameters,
            } => arena.reuse_value(
                value,
                ValueTermNode::DefinitionInstance {
                    definition,
                    parameters: parameters
                        .into_iter()
                        .map(|t| shift_value_type_indices(arena, t, amount, cutoff))
                        .collect(),
                },
            ),
            ValueTermNode::Bound(index) if index >= cutoff => {
                arena.reuse_value(value, ValueTermNode::Bound(index + amount))
            }
            ValueTermNode::Meta {
                metavariable,
                spine,
            } => arena.reuse_value(
                value,
                ValueTermNode::Meta {
                    metavariable,
                    spine: spine
                        .into_iter()
                        .map(|a| match a {
                            ProgramArgument::ValueType(t) => ProgramArgument::ValueType(
                                shift_value_type_indices(arena, t, amount, cutoff),
                            ),
                            ProgramArgument::ValueTerm(v) => {
                                ProgramArgument::ValueTerm(go(arena, v, amount, cutoff))
                            }
                        })
                        .collect(),
                },
            ),
            ValueTermNode::Thunk { computation } => arena.reuse_value(
                value,
                ValueTermNode::Thunk {
                    computation: shift_computation_indices(arena, computation, amount, cutoff),
                },
            ),
            ValueTermNode::Continue {
                state_ty,
                result_ty,
                next,
            } => arena.reuse_value(
                value,
                ValueTermNode::Continue {
                    state_ty: shift_value_type_indices(arena, state_ty, amount, cutoff),
                    result_ty: shift_value_type_indices(arena, result_ty, amount, cutoff),
                    next: go(arena, next, amount, cutoff),
                },
            ),
            ValueTermNode::Finish {
                state_ty,
                result_ty,
                output,
            } => arena.reuse_value(
                value,
                ValueTermNode::Finish {
                    state_ty: shift_value_type_indices(arena, state_ty, amount, cutoff),
                    result_ty: shift_value_type_indices(arena, result_ty, amount, cutoff),
                    output: go(arena, output, amount, cutoff),
                },
            ),
            ValueTermNode::InductiveConstructor {
                indspec,
                parameters,
                idx,
                fields,
            } => arena.reuse_value(
                value,
                ValueTermNode::InductiveConstructor {
                    indspec,
                    parameters: parameters
                        .into_iter()
                        .map(|t| shift_value_type_indices(arena, t, amount, cutoff))
                        .collect(),
                    idx,
                    fields: fields
                        .into_iter()
                        .map(|v| go(arena, v, amount, cutoff))
                        .collect(),
                },
            ),
            ValueTermNode::Bound(_)
            | ValueTermNode::ModuleParam(_)
            | ValueTermNode::DefinedConstant(_) => value,
        }
    }
    go(arena, value, amount, cutoff)
}

pub fn shift_computation_indices(
    arena: &Arena,
    computation: ComputationTerm,
    amount: usize,
    cutoff: usize,
) -> ComputationTerm {
    if amount == 0 {
        return computation;
    }

    fn go(arena: &Arena, term: ComputationTerm, amount: usize, cutoff: usize) -> ComputationTerm {
        match arena.get(term) {
            ComputationTermNode::DefinitionInstance {
                definition,
                parameters,
            } => arena.reuse_computation(
                term,
                ComputationTermNode::DefinitionInstance {
                    definition,
                    parameters: parameters
                        .into_iter()
                        .map(|t| shift_value_type_indices(arena, t, amount, cutoff))
                        .collect(),
                },
            ),
            ComputationTermNode::Return { value } => arena.reuse_computation(
                term,
                ComputationTermNode::Return {
                    value: shift_value_indices(arena, value, amount, cutoff),
                },
            ),
            ComputationTermNode::Force { value } => arena.reuse_computation(
                term,
                ComputationTermNode::Force {
                    value: shift_value_indices(arena, value, amount, cutoff),
                },
            ),
            ComputationTermNode::Lambda {
                var,
                value_ty,
                body,
            } => arena.reuse_computation(
                term,
                ComputationTermNode::Lambda {
                    var,
                    value_ty: shift_value_type_indices(arena, value_ty, amount, cutoff),
                    body: go(arena, body, amount, cutoff + 1),
                },
            ),
            ComputationTermNode::Application { computation, value } => arena.reuse_computation(
                term,
                ComputationTermNode::Application {
                    computation: go(arena, computation, amount, cutoff),
                    value: shift_value_indices(arena, value, amount, cutoff),
                },
            ),
            ComputationTermNode::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => arena.reuse_computation(
                term,
                ComputationTermNode::Sequence {
                    computation: go(arena, computation, amount, cutoff),
                    var,
                    value_ty: shift_value_type_indices(arena, value_ty, amount, cutoff),
                    body: go(arena, body, amount, cutoff + 1),
                },
            ),
            ComputationTermNode::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => arena.reuse_computation(
                term,
                ComputationTermNode::ValueLet {
                    var,
                    value_ty: shift_value_type_indices(arena, value_ty, amount, cutoff),
                    value: shift_value_indices(arena, value, amount, cutoff),
                    body: go(arena, body, amount, cutoff + 1),
                },
            ),
            ComputationTermNode::Case {
                indspec,
                scrutinee,
                branches,
            } => arena.reuse_computation(
                term,
                ComputationTermNode::Case {
                    indspec,
                    scrutinee: shift_value_indices(arena, scrutinee, amount, cutoff),
                    branches: branches
                        .into_iter()
                        .map(|b| ProgramCaseBranch {
                            body: go(arena, b.body, amount, cutoff + b.binders.len()),
                            binders: b.binders,
                        })
                        .collect(),
                },
            ),
            ComputationTermNode::Run {
                state_ty,
                result_ty,
                step,
                initial,
            } => arena.reuse_computation(
                term,
                ComputationTermNode::Run {
                    state_ty: shift_value_type_indices(arena, state_ty, amount, cutoff),
                    result_ty: shift_value_type_indices(arena, result_ty, amount, cutoff),
                    step: shift_value_indices(arena, step, amount, cutoff),
                    initial: shift_value_indices(arena, initial, amount, cutoff),
                },
            ),
            ComputationTermNode::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
            } => arena.reuse_computation(
                term,
                ComputationTermNode::RunCase {
                    state_ty: shift_value_type_indices(arena, state_ty, amount, cutoff),
                    result_ty: shift_value_type_indices(arena, result_ty, amount, cutoff),
                    step: shift_value_indices(arena, step, amount, cutoff),
                    initial: shift_value_indices(arena, initial, amount, cutoff),
                    transition: go(arena, transition, amount, cutoff),
                },
            ),
            ComputationTermNode::Meta { .. } | ComputationTermNode::DefinedConstant(_) => term,
        }
    }
    go(arena, computation, amount, cutoff)
}

pub fn instantiate_value_in_computation(
    arena: &Arena,
    body: ComputationTerm,
    argument: ValueTerm,
) -> ComputationTerm {
    fn subst_value(
        arena: &Arena,
        value: ValueTerm,
        argument: ValueTerm,
        depth: usize,
    ) -> ValueTerm {
        match arena.get(value) {
            ValueTermNode::DefinitionInstance {
                definition,
                parameters,
            } => arena.reuse_value(
                value,
                ValueTermNode::DefinitionInstance {
                    definition,
                    parameters: parameters
                        .into_iter()
                        .map(|ty| {
                            strengthen_value_type(arena, ty, depth)
                                .expect("value-independent type argument")
                        })
                        .collect(),
                },
            ),
            ValueTermNode::Bound(index) if index == depth => {
                shift_value_indices(arena, argument, depth, 0)
            }
            ValueTermNode::Bound(index) if index > depth => {
                arena.reuse_value(value, ValueTermNode::Bound(index - 1))
            }
            ValueTermNode::Thunk { computation } => arena.reuse_value(
                value,
                ValueTermNode::Thunk {
                    computation: subst_comp(arena, computation, argument, depth),
                },
            ),
            ValueTermNode::Continue {
                state_ty,
                result_ty,
                next,
            } => arena.reuse_value(
                value,
                ValueTermNode::Continue {
                    state_ty,
                    result_ty,
                    next: subst_value(arena, next, argument, depth),
                },
            ),
            ValueTermNode::Finish {
                state_ty,
                result_ty,
                output,
            } => arena.reuse_value(
                value,
                ValueTermNode::Finish {
                    state_ty,
                    result_ty,
                    output: subst_value(arena, output, argument, depth),
                },
            ),
            ValueTermNode::InductiveConstructor {
                indspec,
                parameters,
                idx,
                fields,
            } => arena.reuse_value(
                value,
                ValueTermNode::InductiveConstructor {
                    indspec,
                    parameters,
                    idx,
                    fields: fields
                        .into_iter()
                        .map(|v| subst_value(arena, v, argument, depth))
                        .collect(),
                },
            ),
            _ => value,
        }
    }

    fn subst_comp(
        arena: &Arena,
        term: ComputationTerm,
        argument: ValueTerm,
        depth: usize,
    ) -> ComputationTerm {
        match arena.get(term) {
            ComputationTermNode::DefinitionInstance {
                definition,
                parameters,
            } => arena.reuse_computation(
                term,
                ComputationTermNode::DefinitionInstance {
                    definition,
                    parameters: parameters
                        .into_iter()
                        .map(|ty| {
                            strengthen_value_type(arena, ty, depth)
                                .expect("value-independent type argument")
                        })
                        .collect(),
                },
            ),
            ComputationTermNode::Return { value } => arena.reuse_computation(
                term,
                ComputationTermNode::Return {
                    value: subst_value(arena, value, argument, depth),
                },
            ),
            ComputationTermNode::Force { value } => arena.reuse_computation(
                term,
                ComputationTermNode::Force {
                    value: subst_value(arena, value, argument, depth),
                },
            ),
            ComputationTermNode::Lambda {
                var,
                value_ty,
                body,
            } => arena.reuse_computation(
                term,
                ComputationTermNode::Lambda {
                    var,
                    value_ty,
                    body: subst_comp(arena, body, argument, depth + 1),
                },
            ),
            ComputationTermNode::Application { computation, value } => arena.reuse_computation(
                term,
                ComputationTermNode::Application {
                    computation: subst_comp(arena, computation, argument, depth),
                    value: subst_value(arena, value, argument, depth),
                },
            ),
            ComputationTermNode::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => arena.reuse_computation(
                term,
                ComputationTermNode::Sequence {
                    computation: subst_comp(arena, computation, argument, depth),
                    var,
                    value_ty,
                    body: subst_comp(arena, body, argument, depth + 1),
                },
            ),
            ComputationTermNode::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => arena.reuse_computation(
                term,
                ComputationTermNode::ValueLet {
                    var,
                    value_ty: strengthen_value_type(arena, value_ty, depth)
                        .expect("Program value types cannot depend on a value binder"),
                    value: subst_value(arena, value, argument, depth),
                    body: subst_comp(arena, body, argument, depth + 1),
                },
            ),
            ComputationTermNode::Case {
                indspec,
                scrutinee,
                branches,
            } => arena.reuse_computation(
                term,
                ComputationTermNode::Case {
                    indspec,
                    scrutinee: subst_value(arena, scrutinee, argument, depth),
                    branches: branches
                        .into_iter()
                        .map(|b| ProgramCaseBranch {
                            body: subst_comp(arena, b.body, argument, depth + b.binders.len()),
                            binders: b.binders,
                        })
                        .collect(),
                },
            ),
            ComputationTermNode::Run {
                state_ty,
                result_ty,
                step,
                initial,
            } => arena.reuse_computation(
                term,
                ComputationTermNode::Run {
                    state_ty,
                    result_ty,
                    step: subst_value(arena, step, argument, depth),
                    initial: subst_value(arena, initial, argument, depth),
                },
            ),
            ComputationTermNode::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
            } => arena.reuse_computation(
                term,
                ComputationTermNode::RunCase {
                    state_ty,
                    result_ty,
                    step: subst_value(arena, step, argument, depth),
                    initial: subst_value(arena, initial, argument, depth),
                    transition: subst_comp(arena, transition, argument, depth),
                },
            ),
            ComputationTermNode::Meta { .. } | ComputationTermNode::DefinedConstant(_) => term,
        }
    }
    subst_comp(arena, body, argument, 0)
}

fn unfold_value(env: &CrateEnv, mut value: ValueTerm) -> ValueTerm {
    loop {
        match env.arena().get(value) {
            ValueTermNode::DefinedConstant(id) => {
                let DefinedConstant::ProgramValue { body, .. } = env.definition(id) else {
                    break;
                };
                value = *body;
            }
            ValueTermNode::DefinitionInstance {
                definition,
                parameters,
            } => {
                let DefinedConstant::ProgramValue { body, .. } = env.definition(definition) else {
                    break;
                };
                value = crate::raw::program_definitions::instantiate_value(
                    env.arena(),
                    *body,
                    &parameters,
                    0,
                );
            }
            _ => break,
        }
    }
    value
}

pub fn reduce_computation_once(env: &CrateEnv, term: ComputationTerm) -> Option<ComputationTerm> {
    let arena = env.arena();
    // In particular, selecting a Case branch does not need to clone every
    // branch and its binders. Release the guard before recursive allocation.
    let node = arena.borrow_computation(term);
    match *node {
        ComputationTermNode::DefinitionInstance {
            definition,
            ref parameters,
        } => {
            let parameters = parameters.clone();
            drop(node);
            match env.definition(definition) {
                DefinedConstant::ProgramComputation { body, .. } => {
                    Some(crate::raw::program_definitions::instantiate_computation(
                        arena,
                        *body,
                        &parameters,
                        0,
                    ))
                }
                _ => None,
            }
        }
        ComputationTermNode::DefinedConstant(id) => match env.definition(id) {
            DefinedConstant::ProgramComputation { body, .. } => Some(*body),
            _ => None,
        },
        ComputationTermNode::Force { value } => {
            drop(node);
            match *arena.borrow_value(unfold_value(env, value)) {
                ValueTermNode::Thunk { computation } => Some(computation),
                _ => None,
            }
        }
        ComputationTermNode::Application { computation, value } => {
            drop(node);
            if let Some(next) = reduce_computation_once(env, computation) {
                Some(arena.alloc(ComputationTermNode::Application {
                    computation: next,
                    value,
                }))
            } else if let ComputationTermNode::Lambda { body, .. } = arena.get(computation) {
                Some(instantiate_value_in_computation(arena, body, value))
            } else {
                None
            }
        }
        ComputationTermNode::Sequence {
            computation,
            var,
            value_ty,
            body,
        } => {
            drop(node);
            if let Some(next) = reduce_computation_once(env, computation) {
                Some(arena.alloc(ComputationTermNode::Sequence {
                    computation: next,
                    var,
                    value_ty,
                    body,
                }))
            } else if let ComputationTermNode::Return { value } = arena.get(computation) {
                Some(instantiate_value_in_computation(arena, body, value))
            } else {
                None
            }
        }
        ComputationTermNode::ValueLet { value, body, .. } => {
            drop(node);
            Some(instantiate_value_in_computation(arena, body, value))
        }
        ComputationTermNode::Run {
            state_ty,
            result_ty,
            step,
            initial,
        } => {
            drop(node);
            let force = arena.alloc(ComputationTermNode::Force { value: step });
            let transition = arena.alloc(ComputationTermNode::Application {
                computation: force,
                value: initial,
            });
            Some(arena.alloc(ComputationTermNode::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
            }))
        }
        ComputationTermNode::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => {
            drop(node);
            if let Some(next) = reduce_computation_once(env, transition) {
                return Some(arena.alloc(ComputationTermNode::RunCase {
                    state_ty,
                    result_ty,
                    step,
                    initial,
                    transition: next,
                }));
            }
            let ComputationTermNode::Return { value } = arena.get(transition) else {
                return None;
            };
            match arena.get(unfold_value(env, value)) {
                ValueTermNode::Continue { next, .. } => {
                    Some(arena.alloc(ComputationTermNode::Run {
                        state_ty,
                        result_ty,
                        step,
                        initial: next,
                    }))
                }
                ValueTermNode::Finish { output, .. } => {
                    Some(arena.alloc(ComputationTermNode::Return { value: output }))
                }
                _ => None,
            }
        }
        ComputationTermNode::Case {
            indspec, scrutinee, ..
        } => {
            drop(node);
            let ValueTermNode::InductiveConstructor {
                indspec: actual,
                idx,
                fields,
                ..
            } = arena.get(unfold_value(env, scrutinee))
            else {
                return None;
            };
            if actual != indspec {
                return None;
            }
            let mut body = {
                let node = arena.borrow_computation(term);
                let ComputationTermNode::Case { branches, .. } = &*node else {
                    unreachable!()
                };
                branches.get(idx)?.body
            };
            for field in fields.iter().rev() {
                body = instantiate_value_in_computation(arena, body, *field);
            }
            Some(body)
        }
        ComputationTermNode::Return { .. }
        | ComputationTermNode::Lambda { .. }
        | ComputationTermNode::Meta { .. } => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Evaluation {
    Normal(ComputationTerm),
    OutOfFuel(ComputationTerm),
}

pub fn evaluate_computation_with_fuel(
    env: &CrateEnv,
    mut term: ComputationTerm,
    fuel: usize,
) -> Evaluation {
    let span = tracing::debug_span!(target: "ref_type::reduction::program", "evaluate",
        fuel, term = %crate::raw::printing::format_computation(env, term));
    let _entered = span.enter();
    for steps in 0..fuel {
        let Some(next) = reduce_computation_once(env, term) else {
            tracing::debug!(target: "ref_type::reduction::program", steps, result = %crate::raw::printing::format_computation(env, term), "evaluation finished");
            return Evaluation::Normal(term);
        };
        tracing::trace!(target: "ref_type::reduction::program", steps, before = %crate::raw::printing::format_computation(env, term), after = %crate::raw::printing::format_computation(env, next), "evaluation step");
        term = next;
    }
    if reduce_computation_once(env, term).is_some() {
        tracing::warn!(target: "ref_type::reduction::program", fuel, remaining = %crate::raw::printing::format_computation(env, term), "evaluation fuel exhausted");
        Evaluation::OutOfFuel(term)
    } else {
        tracing::debug!(target: "ref_type::reduction::program", steps = fuel, result = %crate::raw::printing::format_computation(env, term), "evaluation finished");
        Evaluation::Normal(term)
    }
}

pub fn evaluate_computation(env: &CrateEnv, term: ComputationTerm) -> Evaluation {
    evaluate_computation_with_fuel(env, term, 100_000)
}

pub fn remap_value_type_global_ids(
    arena: &Arena,
    ty: ValueType,
    _definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> ValueType {
    if inductives.is_empty() {
        return ty;
    }
    match arena.get(ty) {
        ValueTypeNode::Thunk { computation_ty } => arena.reuse_value_type(
            ty,
            ValueTypeNode::Thunk {
                computation_ty: remap_computation_type_global_ids(
                    arena,
                    computation_ty,
                    _definitions,
                    inductives,
                ),
            },
        ),
        ValueTypeNode::RunStep {
            state_ty,
            result_ty,
        } => arena.reuse_value_type(
            ty,
            ValueTypeNode::RunStep {
                state_ty: remap_value_type_global_ids(arena, state_ty, _definitions, inductives),
                result_ty: remap_value_type_global_ids(arena, result_ty, _definitions, inductives),
            },
        ),
        ValueTypeNode::Inductive {
            indspec,
            parameters,
        } => arena.reuse_value_type(
            ty,
            ValueTypeNode::Inductive {
                indspec: inductives.get(&indspec).copied().unwrap_or(indspec),
                parameters: parameters
                    .into_iter()
                    .map(|p| remap_value_type_global_ids(arena, p, _definitions, inductives))
                    .collect(),
            },
        ),
        _ => ty,
    }
}

pub fn remap_computation_type_global_ids(
    arena: &Arena,
    ty: ComputationType,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> ComputationType {
    if inductives.is_empty() {
        return ty;
    }
    match arena.get(ty) {
        ComputationTypeNode::Return { value_ty } => arena.reuse_computation_type(
            ty,
            ComputationTypeNode::Return {
                value_ty: remap_value_type_global_ids(arena, value_ty, definitions, inductives),
            },
        ),
        ComputationTypeNode::Function { domain, codomain } => arena.reuse_computation_type(
            ty,
            ComputationTypeNode::Function {
                domain: remap_value_type_global_ids(arena, domain, definitions, inductives),
                codomain: remap_computation_type_global_ids(
                    arena,
                    codomain,
                    definitions,
                    inductives,
                ),
            },
        ),
        ComputationTypeNode::Meta { .. } => ty,
    }
}

fn remap_program_arguments(
    arena: &Arena,
    arguments: Vec<ProgramArgument>,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> Vec<ProgramArgument> {
    arguments
        .into_iter()
        .map(|argument| match argument {
            ProgramArgument::ValueType(ty) => ProgramArgument::ValueType(
                remap_value_type_global_ids(arena, ty, definitions, inductives),
            ),
            ProgramArgument::ValueTerm(value) => ProgramArgument::ValueTerm(
                remap_value_global_ids(arena, value, definitions, inductives),
            ),
        })
        .collect()
}

pub fn remap_value_global_ids(
    arena: &Arena,
    value: ValueTerm,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> ValueTerm {
    if definitions.is_empty() && inductives.is_empty() {
        return value;
    }
    match arena.get(value) {
        ValueTermNode::DefinitionInstance {
            definition,
            parameters,
        } => arena.reuse_value(
            value,
            ValueTermNode::DefinitionInstance {
                definition: definitions.get(&definition).copied().unwrap_or(definition),
                parameters: parameters
                    .into_iter()
                    .map(|t| remap_value_type_global_ids(arena, t, definitions, inductives))
                    .collect(),
            },
        ),
        ValueTermNode::DefinedConstant(id) => arena.reuse_value(
            value,
            ValueTermNode::DefinedConstant(definitions.get(&id).copied().unwrap_or(id)),
        ),
        ValueTermNode::Meta {
            metavariable,
            spine,
        } => arena.reuse_value(
            value,
            ValueTermNode::Meta {
                metavariable,
                spine: remap_program_arguments(arena, spine, definitions, inductives),
            },
        ),
        ValueTermNode::Thunk { computation } => arena.reuse_value(
            value,
            ValueTermNode::Thunk {
                computation: remap_computation_global_ids(
                    arena,
                    computation,
                    definitions,
                    inductives,
                ),
            },
        ),
        ValueTermNode::Continue {
            state_ty,
            result_ty,
            next,
        } => arena.reuse_value(
            value,
            ValueTermNode::Continue {
                state_ty: remap_value_type_global_ids(arena, state_ty, definitions, inductives),
                result_ty: remap_value_type_global_ids(arena, result_ty, definitions, inductives),
                next: remap_value_global_ids(arena, next, definitions, inductives),
            },
        ),
        ValueTermNode::Finish {
            state_ty,
            result_ty,
            output,
        } => arena.reuse_value(
            value,
            ValueTermNode::Finish {
                state_ty: remap_value_type_global_ids(arena, state_ty, definitions, inductives),
                result_ty: remap_value_type_global_ids(arena, result_ty, definitions, inductives),
                output: remap_value_global_ids(arena, output, definitions, inductives),
            },
        ),
        ValueTermNode::InductiveConstructor {
            indspec,
            parameters,
            idx,
            fields,
        } => arena.reuse_value(
            value,
            ValueTermNode::InductiveConstructor {
                indspec: inductives.get(&indspec).copied().unwrap_or(indspec),
                parameters: parameters
                    .into_iter()
                    .map(|ty| remap_value_type_global_ids(arena, ty, definitions, inductives))
                    .collect(),
                idx,
                fields: fields
                    .into_iter()
                    .map(|value| remap_value_global_ids(arena, value, definitions, inductives))
                    .collect(),
            },
        ),
        ValueTermNode::Bound(_) | ValueTermNode::ModuleParam(_) => value,
    }
}

pub fn remap_computation_global_ids(
    arena: &Arena,
    computation: ComputationTerm,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> ComputationTerm {
    if definitions.is_empty() && inductives.is_empty() {
        return computation;
    }
    let value = |value| remap_value_global_ids(arena, value, definitions, inductives);
    let recur = |term| remap_computation_global_ids(arena, term, definitions, inductives);
    let value_ty = |ty| remap_value_type_global_ids(arena, ty, definitions, inductives);
    match arena.get(computation) {
        ComputationTermNode::DefinitionInstance {
            definition,
            parameters,
        } => arena.reuse_computation(
            computation,
            ComputationTermNode::DefinitionInstance {
                definition: definitions.get(&definition).copied().unwrap_or(definition),
                parameters: parameters
                    .into_iter()
                    .map(|t| remap_value_type_global_ids(arena, t, definitions, inductives))
                    .collect(),
            },
        ),
        ComputationTermNode::DefinedConstant(id) => arena.reuse_computation(
            computation,
            ComputationTermNode::DefinedConstant(definitions.get(&id).copied().unwrap_or(id)),
        ),
        ComputationTermNode::Meta {
            metavariable,
            spine,
        } => arena.reuse_computation(
            computation,
            ComputationTermNode::Meta {
                metavariable,
                spine: remap_program_arguments(arena, spine, definitions, inductives),
            },
        ),
        ComputationTermNode::Return { value: item } => arena.reuse_computation(
            computation,
            ComputationTermNode::Return { value: value(item) },
        ),
        ComputationTermNode::Force { value: item } => arena.reuse_computation(
            computation,
            ComputationTermNode::Force { value: value(item) },
        ),
        ComputationTermNode::Lambda {
            var,
            value_ty: ty,
            body,
        } => arena.reuse_computation(
            computation,
            ComputationTermNode::Lambda {
                var,
                value_ty: value_ty(ty),
                body: recur(body),
            },
        ),
        ComputationTermNode::Application {
            computation: function,
            value: argument,
        } => arena.reuse_computation(
            computation,
            ComputationTermNode::Application {
                computation: recur(function),
                value: value(argument),
            },
        ),
        ComputationTermNode::Sequence {
            computation: first,
            var,
            value_ty: ty,
            body,
        } => arena.reuse_computation(
            computation,
            ComputationTermNode::Sequence {
                computation: recur(first),
                var,
                value_ty: value_ty(ty),
                body: recur(body),
            },
        ),
        ComputationTermNode::ValueLet {
            var,
            value_ty: ty,
            value: item,
            body,
        } => arena.reuse_computation(
            computation,
            ComputationTermNode::ValueLet {
                var,
                value_ty: value_ty(ty),
                value: value(item),
                body: recur(body),
            },
        ),
        ComputationTermNode::Case {
            indspec,
            scrutinee,
            branches,
        } => arena.reuse_computation(
            computation,
            ComputationTermNode::Case {
                indspec: inductives.get(&indspec).copied().unwrap_or(indspec),
                scrutinee: value(scrutinee),
                branches: branches
                    .into_iter()
                    .map(|branch| ProgramCaseBranch {
                        binders: branch.binders,
                        body: recur(branch.body),
                    })
                    .collect(),
            },
        ),
        ComputationTermNode::Run {
            state_ty,
            result_ty,
            step,
            initial,
        } => arena.reuse_computation(
            computation,
            ComputationTermNode::Run {
                state_ty: value_ty(state_ty),
                result_ty: value_ty(result_ty),
                step: value(step),
                initial: value(initial),
            },
        ),
        ComputationTermNode::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => arena.reuse_computation(
            computation,
            ComputationTermNode::RunCase {
                state_ty: value_ty(state_ty),
                result_ty: value_ty(result_ty),
                step: value(step),
                initial: value(initial),
                transition: recur(transition),
            },
        ),
    }
}

pub fn subst_value_type_module_params(
    arena: &Arena,
    ty: ValueType,
    substitutions: &[(ModuleParamId, ModuleArgument)],
) -> ValueType {
    if substitutions.is_empty() {
        return ty;
    }
    match arena.get(ty) {
        ValueTypeNode::ModuleParam(id) => substitutions
            .iter()
            .find_map(|(candidate, arg)| (*candidate == id).then_some(arg))
            .and_then(|arg| match arg {
                ModuleArgument::ProgramType(t) => Some(*t),
                _ => None,
            })
            .unwrap_or(ty),
        ValueTypeNode::Thunk { computation_ty } => arena.reuse_value_type(
            ty,
            ValueTypeNode::Thunk {
                computation_ty: subst_computation_type_module_params(
                    arena,
                    computation_ty,
                    substitutions,
                ),
            },
        ),
        ValueTypeNode::RunStep {
            state_ty,
            result_ty,
        } => arena.reuse_value_type(
            ty,
            ValueTypeNode::RunStep {
                state_ty: subst_value_type_module_params(arena, state_ty, substitutions),
                result_ty: subst_value_type_module_params(arena, result_ty, substitutions),
            },
        ),
        ValueTypeNode::Inductive {
            indspec,
            parameters,
        } => arena.reuse_value_type(
            ty,
            ValueTypeNode::Inductive {
                indspec,
                parameters: parameters
                    .into_iter()
                    .map(|p| subst_value_type_module_params(arena, p, substitutions))
                    .collect(),
            },
        ),
        _ => ty,
    }
}

pub fn subst_computation_type_module_params(
    arena: &Arena,
    ty: ComputationType,
    substitutions: &[(ModuleParamId, ModuleArgument)],
) -> ComputationType {
    if substitutions.is_empty() {
        return ty;
    }
    match arena.get(ty) {
        ComputationTypeNode::Return { value_ty } => arena.reuse_computation_type(
            ty,
            ComputationTypeNode::Return {
                value_ty: subst_value_type_module_params(arena, value_ty, substitutions),
            },
        ),
        ComputationTypeNode::Function { domain, codomain } => arena.reuse_computation_type(
            ty,
            ComputationTypeNode::Function {
                domain: subst_value_type_module_params(arena, domain, substitutions),
                codomain: subst_computation_type_module_params(arena, codomain, substitutions),
            },
        ),
        ComputationTypeNode::Meta { .. } => ty,
    }
}

fn subst_program_arguments(
    arena: &Arena,
    arguments: Vec<ProgramArgument>,
    substitutions: &[(ModuleParamId, ModuleArgument)],
) -> Vec<ProgramArgument> {
    arguments
        .into_iter()
        .map(|argument| match argument {
            ProgramArgument::ValueType(ty) => {
                ProgramArgument::ValueType(subst_value_type_module_params(arena, ty, substitutions))
            }
            ProgramArgument::ValueTerm(value) => {
                ProgramArgument::ValueTerm(subst_value_module_params(arena, value, substitutions))
            }
        })
        .collect()
}

pub fn subst_value_module_params(
    arena: &Arena,
    value: ValueTerm,
    substitutions: &[(ModuleParamId, ModuleArgument)],
) -> ValueTerm {
    if substitutions.is_empty() {
        return value;
    }
    match arena.get(value) {
        ValueTermNode::DefinitionInstance {
            definition,
            parameters,
        } => arena.reuse_value(
            value,
            ValueTermNode::DefinitionInstance {
                definition,
                parameters: parameters
                    .into_iter()
                    .map(|t| subst_value_type_module_params(arena, t, substitutions))
                    .collect(),
            },
        ),
        ValueTermNode::ModuleParam(id) => substitutions
            .iter()
            .find_map(|(candidate, argument)| (*candidate == id).then_some(argument))
            .and_then(|argument| match argument {
                ModuleArgument::ProgramValue(value) => Some(*value),
                _ => None,
            })
            .unwrap_or(value),
        ValueTermNode::Meta {
            metavariable,
            spine,
        } => arena.reuse_value(
            value,
            ValueTermNode::Meta {
                metavariable,
                spine: subst_program_arguments(arena, spine, substitutions),
            },
        ),
        ValueTermNode::Thunk { computation } => arena.reuse_value(
            value,
            ValueTermNode::Thunk {
                computation: subst_computation_module_params(arena, computation, substitutions),
            },
        ),
        ValueTermNode::Continue {
            state_ty,
            result_ty,
            next,
        } => arena.reuse_value(
            value,
            ValueTermNode::Continue {
                state_ty: subst_value_type_module_params(arena, state_ty, substitutions),
                result_ty: subst_value_type_module_params(arena, result_ty, substitutions),
                next: subst_value_module_params(arena, next, substitutions),
            },
        ),
        ValueTermNode::Finish {
            state_ty,
            result_ty,
            output,
        } => arena.reuse_value(
            value,
            ValueTermNode::Finish {
                state_ty: subst_value_type_module_params(arena, state_ty, substitutions),
                result_ty: subst_value_type_module_params(arena, result_ty, substitutions),
                output: subst_value_module_params(arena, output, substitutions),
            },
        ),
        ValueTermNode::InductiveConstructor {
            indspec,
            parameters,
            idx,
            fields,
        } => arena.reuse_value(
            value,
            ValueTermNode::InductiveConstructor {
                indspec,
                parameters: parameters
                    .into_iter()
                    .map(|ty| subst_value_type_module_params(arena, ty, substitutions))
                    .collect(),
                idx,
                fields: fields
                    .into_iter()
                    .map(|value| subst_value_module_params(arena, value, substitutions))
                    .collect(),
            },
        ),
        _ => value,
    }
}

pub fn subst_computation_module_params(
    arena: &Arena,
    term: ComputationTerm,
    substitutions: &[(ModuleParamId, ModuleArgument)],
) -> ComputationTerm {
    if substitutions.is_empty() {
        return term;
    }
    match arena.get(term) {
        ComputationTermNode::DefinitionInstance {
            definition,
            parameters,
        } => arena.reuse_computation(
            term,
            ComputationTermNode::DefinitionInstance {
                definition,
                parameters: parameters
                    .into_iter()
                    .map(|t| subst_value_type_module_params(arena, t, substitutions))
                    .collect(),
            },
        ),
        ComputationTermNode::Meta {
            metavariable,
            spine,
        } => arena.reuse_computation(
            term,
            ComputationTermNode::Meta {
                metavariable,
                spine: subst_program_arguments(arena, spine, substitutions),
            },
        ),
        ComputationTermNode::Return { value } => arena.reuse_computation(
            term,
            ComputationTermNode::Return {
                value: subst_value_module_params(arena, value, substitutions),
            },
        ),
        ComputationTermNode::Force { value } => arena.reuse_computation(
            term,
            ComputationTermNode::Force {
                value: subst_value_module_params(arena, value, substitutions),
            },
        ),
        ComputationTermNode::Lambda {
            var,
            value_ty,
            body,
        } => arena.reuse_computation(
            term,
            ComputationTermNode::Lambda {
                var,
                value_ty: subst_value_type_module_params(arena, value_ty, substitutions),
                body: subst_computation_module_params(arena, body, substitutions),
            },
        ),
        ComputationTermNode::Application { computation, value } => arena.reuse_computation(
            term,
            ComputationTermNode::Application {
                computation: subst_computation_module_params(arena, computation, substitutions),
                value: subst_value_module_params(arena, value, substitutions),
            },
        ),
        ComputationTermNode::Sequence {
            computation,
            var,
            value_ty,
            body,
        } => arena.reuse_computation(
            term,
            ComputationTermNode::Sequence {
                computation: subst_computation_module_params(arena, computation, substitutions),
                var,
                value_ty: subst_value_type_module_params(arena, value_ty, substitutions),
                body: subst_computation_module_params(arena, body, substitutions),
            },
        ),
        ComputationTermNode::ValueLet {
            var,
            value_ty,
            value,
            body,
        } => arena.reuse_computation(
            term,
            ComputationTermNode::ValueLet {
                var,
                value_ty: subst_value_type_module_params(arena, value_ty, substitutions),
                value: subst_value_module_params(arena, value, substitutions),
                body: subst_computation_module_params(arena, body, substitutions),
            },
        ),
        ComputationTermNode::Case {
            indspec,
            scrutinee,
            branches,
        } => arena.reuse_computation(
            term,
            ComputationTermNode::Case {
                indspec,
                scrutinee: subst_value_module_params(arena, scrutinee, substitutions),
                branches: branches
                    .into_iter()
                    .map(|branch| ProgramCaseBranch {
                        binders: branch.binders,
                        body: subst_computation_module_params(arena, branch.body, substitutions),
                    })
                    .collect(),
            },
        ),
        ComputationTermNode::Run {
            state_ty,
            result_ty,
            step,
            initial,
        } => arena.reuse_computation(
            term,
            ComputationTermNode::Run {
                state_ty: subst_value_type_module_params(arena, state_ty, substitutions),
                result_ty: subst_value_type_module_params(arena, result_ty, substitutions),
                step: subst_value_module_params(arena, step, substitutions),
                initial: subst_value_module_params(arena, initial, substitutions),
            },
        ),
        ComputationTermNode::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => arena.reuse_computation(
            term,
            ComputationTermNode::RunCase {
                state_ty: subst_value_type_module_params(arena, state_ty, substitutions),
                result_ty: subst_value_type_module_params(arena, result_ty, substitutions),
                step: subst_value_module_params(arena, step, substitutions),
                initial: subst_value_module_params(arena, initial, substitutions),
                transition: subst_computation_module_params(arena, transition, substitutions),
            },
        ),
        _ => term,
    }
}
