//! Structural operations and weak call-by-value evaluation for Program syntax.

use std::collections::HashMap;

use crate::{
    environment::{CrateEnv, DefinedConstant, ModuleArgument},
    exp::Arena,
    ids::{DefId, ModuleParamId, ProgramInductiveId},
    program::*,
};

pub fn program_type_is_alpha_eq(arena: &Arena, left: ProgramType, right: ProgramType) -> bool {
    match (left, right) {
        (ProgramType::Value(left), ProgramType::Value(right)) => {
            value_type_is_alpha_eq(arena, left, right)
        }
        (ProgramType::Computation(left), ProgramType::Computation(right)) => {
            computation_type_is_alpha_eq(arena, left, right)
        }
        _ => false,
    }
}

pub fn program_is_alpha_eq(arena: &Arena, left: Program, right: Program) -> bool {
    match (left, right) {
        (Program::Value(left), Program::Value(right)) => value_is_alpha_eq(arena, left, right),
        (Program::Computation(left), Program::Computation(right)) => {
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
                (ProgramArgument::Type(left), ProgramArgument::Type(right)) => {
                    value_type_is_alpha_eq(arena, left, right)
                }
                (ProgramArgument::Value(left), ProgramArgument::Value(right)) => {
                    value_is_alpha_eq(arena, left, right)
                }
                _ => false,
            })
}

pub fn value_is_alpha_eq(arena: &Arena, left: Value, right: Value) -> bool {
    if left == right {
        return true;
    }
    match (arena.get(left), arena.get(right)) {
        (ValueNode::Bound(left), ValueNode::Bound(right)) => left == right,
        (ValueNode::ModuleParam(left), ValueNode::ModuleParam(right)) => left == right,
        (ValueNode::DefinedConstant(left), ValueNode::DefinedConstant(right)) => left == right,
        (
            ValueNode::Meta {
                metavariable: left,
                spine: left_spine,
            },
            ValueNode::Meta {
                metavariable: right,
                spine: right_spine,
            },
        ) => left == right && program_arguments_alpha_eq(arena, &left_spine, &right_spine),
        (ValueNode::Thunk { computation: left }, ValueNode::Thunk { computation: right }) => {
            computation_is_alpha_eq(arena, left, right)
        }
        (
            ValueNode::Continue {
                state_ty: ls,
                result_ty: lr,
                next: ln,
            },
            ValueNode::Continue {
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
            ValueNode::Finish {
                state_ty: ls,
                result_ty: lr,
                output: lo,
            },
            ValueNode::Finish {
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
            ValueNode::InductiveConstructor {
                indspec: li,
                parameters: lp,
                idx: lx,
                fields: lf,
            },
            ValueNode::InductiveConstructor {
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

pub fn computation_is_alpha_eq(arena: &Arena, left: Computation, right: Computation) -> bool {
    if left == right {
        return true;
    }
    match (arena.get(left), arena.get(right)) {
        (ComputationNode::DefinedConstant(left), ComputationNode::DefinedConstant(right)) => {
            left == right
        }
        (
            ComputationNode::Meta {
                metavariable: left,
                spine: ls,
            },
            ComputationNode::Meta {
                metavariable: right,
                spine: rs,
            },
        ) => left == right && program_arguments_alpha_eq(arena, &ls, &rs),
        (ComputationNode::Return { value: left }, ComputationNode::Return { value: right })
        | (ComputationNode::Force { value: left }, ComputationNode::Force { value: right }) => {
            value_is_alpha_eq(arena, left, right)
        }
        (
            ComputationNode::Lambda {
                value_ty: lt,
                body: lb,
                ..
            },
            ComputationNode::Lambda {
                value_ty: rt,
                body: rb,
                ..
            },
        ) => value_type_is_alpha_eq(arena, lt, rt) && computation_is_alpha_eq(arena, lb, rb),
        (
            ComputationNode::Application {
                computation: lc,
                value: lv,
            },
            ComputationNode::Application {
                computation: rc,
                value: rv,
            },
        ) => computation_is_alpha_eq(arena, lc, rc) && value_is_alpha_eq(arena, lv, rv),
        (
            ComputationNode::Sequence {
                computation: lc,
                value_ty: lt,
                body: lb,
                ..
            },
            ComputationNode::Sequence {
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
            ComputationNode::ValueLet {
                value_ty: lt,
                value: lv,
                body: lb,
                ..
            },
            ComputationNode::ValueLet {
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
            ComputationNode::Run {
                state_ty: ls,
                result_ty: lr,
                step: lp,
                initial: li,
            },
            ComputationNode::Run {
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
fn values_alpha_eq(arena: &Arena, left: &[Value], right: &[Value]) -> bool {
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
    mut ty: ValueType,
    arguments: &[ValueType],
) -> ValueType {
    for argument in arguments.iter().rev() {
        ty = instantiate_value_type(arena, ty, *argument, 0);
    }
    ty
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

pub fn shift_value_indices(arena: &Arena, value: Value, amount: usize, cutoff: usize) -> Value {
    if amount == 0 {
        return value;
    }
    fn go(arena: &Arena, value: Value, amount: usize, cutoff: usize) -> Value {
        match arena.get(value) {
            ValueNode::Bound(index) if index >= cutoff => {
                arena.reuse_value(value, ValueNode::Bound(index + amount))
            }
            ValueNode::Meta {
                metavariable,
                spine,
            } => arena.reuse_value(
                value,
                ValueNode::Meta {
                    metavariable,
                    spine: spine
                        .into_iter()
                        .map(|a| match a {
                            ProgramArgument::Type(t) => ProgramArgument::Type(
                                shift_value_type_indices(arena, t, amount, cutoff),
                            ),
                            ProgramArgument::Value(v) => {
                                ProgramArgument::Value(go(arena, v, amount, cutoff))
                            }
                        })
                        .collect(),
                },
            ),
            ValueNode::Thunk { computation } => arena.reuse_value(
                value,
                ValueNode::Thunk {
                    computation: shift_computation_indices(arena, computation, amount, cutoff),
                },
            ),
            ValueNode::Continue {
                state_ty,
                result_ty,
                next,
            } => arena.reuse_value(
                value,
                ValueNode::Continue {
                    state_ty: shift_value_type_indices(arena, state_ty, amount, cutoff),
                    result_ty: shift_value_type_indices(arena, result_ty, amount, cutoff),
                    next: go(arena, next, amount, cutoff),
                },
            ),
            ValueNode::Finish {
                state_ty,
                result_ty,
                output,
            } => arena.reuse_value(
                value,
                ValueNode::Finish {
                    state_ty: shift_value_type_indices(arena, state_ty, amount, cutoff),
                    result_ty: shift_value_type_indices(arena, result_ty, amount, cutoff),
                    output: go(arena, output, amount, cutoff),
                },
            ),
            ValueNode::InductiveConstructor {
                indspec,
                parameters,
                idx,
                fields,
            } => arena.reuse_value(
                value,
                ValueNode::InductiveConstructor {
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
            ValueNode::Bound(_) | ValueNode::ModuleParam(_) | ValueNode::DefinedConstant(_) => {
                value
            }
        }
    }
    go(arena, value, amount, cutoff)
}

pub fn shift_computation_indices(
    arena: &Arena,
    computation: Computation,
    amount: usize,
    cutoff: usize,
) -> Computation {
    if amount == 0 {
        return computation;
    }
    fn go(arena: &Arena, term: Computation, amount: usize, cutoff: usize) -> Computation {
        match arena.get(term) {
            ComputationNode::Return { value } => arena.reuse_computation(
                term,
                ComputationNode::Return {
                    value: shift_value_indices(arena, value, amount, cutoff),
                },
            ),
            ComputationNode::Force { value } => arena.reuse_computation(
                term,
                ComputationNode::Force {
                    value: shift_value_indices(arena, value, amount, cutoff),
                },
            ),
            ComputationNode::Lambda {
                var,
                value_ty,
                body,
            } => arena.reuse_computation(
                term,
                ComputationNode::Lambda {
                    var,
                    value_ty: shift_value_type_indices(arena, value_ty, amount, cutoff),
                    body: go(arena, body, amount, cutoff + 1),
                },
            ),
            ComputationNode::Application { computation, value } => arena.reuse_computation(
                term,
                ComputationNode::Application {
                    computation: go(arena, computation, amount, cutoff),
                    value: shift_value_indices(arena, value, amount, cutoff),
                },
            ),
            ComputationNode::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => arena.reuse_computation(
                term,
                ComputationNode::Sequence {
                    computation: go(arena, computation, amount, cutoff),
                    var,
                    value_ty: shift_value_type_indices(arena, value_ty, amount, cutoff),
                    body: go(arena, body, amount, cutoff + 1),
                },
            ),
            ComputationNode::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => arena.reuse_computation(
                term,
                ComputationNode::ValueLet {
                    var,
                    value_ty: shift_value_type_indices(arena, value_ty, amount, cutoff),
                    value: shift_value_indices(arena, value, amount, cutoff),
                    body: go(arena, body, amount, cutoff + 1),
                },
            ),
            ComputationNode::Case {
                indspec,
                scrutinee,
                branches,
            } => arena.reuse_computation(
                term,
                ComputationNode::Case {
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
            ComputationNode::Run {
                state_ty,
                result_ty,
                step,
                initial,
            } => arena.reuse_computation(
                term,
                ComputationNode::Run {
                    state_ty: shift_value_type_indices(arena, state_ty, amount, cutoff),
                    result_ty: shift_value_type_indices(arena, result_ty, amount, cutoff),
                    step: shift_value_indices(arena, step, amount, cutoff),
                    initial: shift_value_indices(arena, initial, amount, cutoff),
                },
            ),
            ComputationNode::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
            } => arena.reuse_computation(
                term,
                ComputationNode::RunCase {
                    state_ty: shift_value_type_indices(arena, state_ty, amount, cutoff),
                    result_ty: shift_value_type_indices(arena, result_ty, amount, cutoff),
                    step: shift_value_indices(arena, step, amount, cutoff),
                    initial: shift_value_indices(arena, initial, amount, cutoff),
                    transition: go(arena, transition, amount, cutoff),
                },
            ),
            ComputationNode::Meta { .. } | ComputationNode::DefinedConstant(_) => term,
        }
    }
    go(arena, computation, amount, cutoff)
}

pub fn instantiate_value_in_computation(
    arena: &Arena,
    body: Computation,
    argument: Value,
) -> Computation {
    fn subst_value(arena: &Arena, value: Value, argument: Value, depth: usize) -> Value {
        match arena.get(value) {
            ValueNode::Bound(index) if index == depth => {
                shift_value_indices(arena, argument, depth, 0)
            }
            ValueNode::Bound(index) if index > depth => {
                arena.reuse_value(value, ValueNode::Bound(index - 1))
            }
            ValueNode::Thunk { computation } => arena.reuse_value(
                value,
                ValueNode::Thunk {
                    computation: subst_comp(arena, computation, argument, depth),
                },
            ),
            ValueNode::Continue {
                state_ty,
                result_ty,
                next,
            } => arena.reuse_value(
                value,
                ValueNode::Continue {
                    state_ty,
                    result_ty,
                    next: subst_value(arena, next, argument, depth),
                },
            ),
            ValueNode::Finish {
                state_ty,
                result_ty,
                output,
            } => arena.reuse_value(
                value,
                ValueNode::Finish {
                    state_ty,
                    result_ty,
                    output: subst_value(arena, output, argument, depth),
                },
            ),
            ValueNode::InductiveConstructor {
                indspec,
                parameters,
                idx,
                fields,
            } => arena.reuse_value(
                value,
                ValueNode::InductiveConstructor {
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
    fn subst_comp(arena: &Arena, term: Computation, argument: Value, depth: usize) -> Computation {
        match arena.get(term) {
            ComputationNode::Return { value } => arena.reuse_computation(
                term,
                ComputationNode::Return {
                    value: subst_value(arena, value, argument, depth),
                },
            ),
            ComputationNode::Force { value } => arena.reuse_computation(
                term,
                ComputationNode::Force {
                    value: subst_value(arena, value, argument, depth),
                },
            ),
            ComputationNode::Lambda {
                var,
                value_ty,
                body,
            } => arena.reuse_computation(
                term,
                ComputationNode::Lambda {
                    var,
                    value_ty,
                    body: subst_comp(arena, body, argument, depth + 1),
                },
            ),
            ComputationNode::Application { computation, value } => arena.reuse_computation(
                term,
                ComputationNode::Application {
                    computation: subst_comp(arena, computation, argument, depth),
                    value: subst_value(arena, value, argument, depth),
                },
            ),
            ComputationNode::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => arena.reuse_computation(
                term,
                ComputationNode::Sequence {
                    computation: subst_comp(arena, computation, argument, depth),
                    var,
                    value_ty,
                    body: subst_comp(arena, body, argument, depth + 1),
                },
            ),
            ComputationNode::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => arena.reuse_computation(
                term,
                ComputationNode::ValueLet {
                    var,
                    value_ty: strengthen_value_type(arena, value_ty, depth)
                        .expect("Program value types cannot depend on a value binder"),
                    value: subst_value(arena, value, argument, depth),
                    body: subst_comp(arena, body, argument, depth + 1),
                },
            ),
            ComputationNode::Case {
                indspec,
                scrutinee,
                branches,
            } => arena.reuse_computation(
                term,
                ComputationNode::Case {
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
            ComputationNode::Run {
                state_ty,
                result_ty,
                step,
                initial,
            } => arena.reuse_computation(
                term,
                ComputationNode::Run {
                    state_ty,
                    result_ty,
                    step: subst_value(arena, step, argument, depth),
                    initial: subst_value(arena, initial, argument, depth),
                },
            ),
            ComputationNode::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
            } => arena.reuse_computation(
                term,
                ComputationNode::RunCase {
                    state_ty,
                    result_ty,
                    step: subst_value(arena, step, argument, depth),
                    initial: subst_value(arena, initial, argument, depth),
                    transition: subst_comp(arena, transition, argument, depth),
                },
            ),
            ComputationNode::Meta { .. } | ComputationNode::DefinedConstant(_) => term,
        }
    }
    subst_comp(arena, body, argument, 0)
}

fn unfold_value(env: &CrateEnv, mut value: Value) -> Value {
    while let ValueNode::DefinedConstant(id) = *env.arena().borrow_value(value) {
        let DefinedConstant::ProgramValue { body, .. } = env.definition(id) else {
            break;
        };
        value = *body;
    }
    value
}

pub fn reduce_computation_once(env: &CrateEnv, term: Computation) -> Option<Computation> {
    let arena = env.arena();
    // In particular, selecting a Case branch does not need to clone every
    // branch and its binders. Release the guard before recursive allocation.
    let node = arena.borrow_computation(term);
    match *node {
        ComputationNode::DefinedConstant(id) => match env.definition(id) {
            DefinedConstant::ProgramComputation { body, .. } => Some(*body),
            _ => None,
        },
        ComputationNode::Force { value } => match *arena.borrow_value(unfold_value(env, value)) {
            ValueNode::Thunk { computation } => Some(computation),
            _ => None,
        },
        ComputationNode::Application { computation, value } => {
            drop(node);
            if let Some(next) = reduce_computation_once(env, computation) {
                Some(arena.alloc(ComputationNode::Application {
                    computation: next,
                    value,
                }))
            } else if let ComputationNode::Lambda { body, .. } = arena.get(computation) {
                Some(instantiate_value_in_computation(arena, body, value))
            } else {
                None
            }
        }
        ComputationNode::Sequence {
            computation,
            var,
            value_ty,
            body,
        } => {
            drop(node);
            if let Some(next) = reduce_computation_once(env, computation) {
                Some(arena.alloc(ComputationNode::Sequence {
                    computation: next,
                    var,
                    value_ty,
                    body,
                }))
            } else if let ComputationNode::Return { value } = arena.get(computation) {
                Some(instantiate_value_in_computation(arena, body, value))
            } else {
                None
            }
        }
        ComputationNode::ValueLet { value, body, .. } => {
            drop(node);
            Some(instantiate_value_in_computation(arena, body, value))
        }
        ComputationNode::Run {
            state_ty,
            result_ty,
            step,
            initial,
        } => {
            drop(node);
            let force = arena.alloc(ComputationNode::Force { value: step });
            let transition = arena.alloc(ComputationNode::Application {
                computation: force,
                value: initial,
            });
            Some(arena.alloc(ComputationNode::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
            }))
        }
        ComputationNode::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => {
            drop(node);
            if let Some(next) = reduce_computation_once(env, transition) {
                return Some(arena.alloc(ComputationNode::RunCase {
                    state_ty,
                    result_ty,
                    step,
                    initial,
                    transition: next,
                }));
            }
            let ComputationNode::Return { value } = arena.get(transition) else {
                return None;
            };
            match arena.get(unfold_value(env, value)) {
                ValueNode::Continue { next, .. } => Some(arena.alloc(ComputationNode::Run {
                    state_ty,
                    result_ty,
                    step,
                    initial: next,
                })),
                ValueNode::Finish { output, .. } => {
                    Some(arena.alloc(ComputationNode::Return { value: output }))
                }
                _ => None,
            }
        }
        ComputationNode::Case {
            indspec,
            scrutinee,
            ref branches,
        } => {
            let ValueNode::InductiveConstructor {
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
            let branch = branches.get(idx)?;
            let mut body = branch.body;
            drop(node);
            for field in fields.iter().rev() {
                body = instantiate_value_in_computation(arena, body, *field);
            }
            Some(body)
        }
        ComputationNode::Return { .. }
        | ComputationNode::Lambda { .. }
        | ComputationNode::Meta { .. } => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Evaluation {
    Normal(Computation),
    OutOfFuel(Computation),
}

pub fn evaluate_computation_with_fuel(
    env: &CrateEnv,
    mut term: Computation,
    fuel: usize,
) -> Evaluation {
    let span = tracing::debug_span!(target: "ref_type::reduction::program", "evaluate",
        fuel, term = %crate::printing::format_computation(env, term));
    let _entered = span.enter();
    for steps in 0..fuel {
        let Some(next) = reduce_computation_once(env, term) else {
            tracing::debug!(target: "ref_type::reduction::program", steps, result = %crate::printing::format_computation(env, term), "evaluation finished");
            return Evaluation::Normal(term);
        };
        tracing::trace!(target: "ref_type::reduction::program", steps, before = %crate::printing::format_computation(env, term), after = %crate::printing::format_computation(env, next), "evaluation step");
        term = next;
    }
    if reduce_computation_once(env, term).is_some() {
        tracing::warn!(target: "ref_type::reduction::program", fuel, remaining = %crate::printing::format_computation(env, term), "evaluation fuel exhausted");
        Evaluation::OutOfFuel(term)
    } else {
        tracing::debug!(target: "ref_type::reduction::program", steps = fuel, result = %crate::printing::format_computation(env, term), "evaluation finished");
        Evaluation::Normal(term)
    }
}

pub fn evaluate_computation(env: &CrateEnv, term: Computation) -> Evaluation {
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
            ProgramArgument::Type(ty) => ProgramArgument::Type(remap_value_type_global_ids(
                arena,
                ty,
                definitions,
                inductives,
            )),
            ProgramArgument::Value(value) => ProgramArgument::Value(remap_value_global_ids(
                arena,
                value,
                definitions,
                inductives,
            )),
        })
        .collect()
}

pub fn remap_value_global_ids(
    arena: &Arena,
    value: Value,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> Value {
    if definitions.is_empty() && inductives.is_empty() {
        return value;
    }
    match arena.get(value) {
        ValueNode::DefinedConstant(id) => arena.reuse_value(
            value,
            ValueNode::DefinedConstant(definitions.get(&id).copied().unwrap_or(id)),
        ),
        ValueNode::Meta {
            metavariable,
            spine,
        } => arena.reuse_value(
            value,
            ValueNode::Meta {
                metavariable,
                spine: remap_program_arguments(arena, spine, definitions, inductives),
            },
        ),
        ValueNode::Thunk { computation } => arena.reuse_value(
            value,
            ValueNode::Thunk {
                computation: remap_computation_global_ids(
                    arena,
                    computation,
                    definitions,
                    inductives,
                ),
            },
        ),
        ValueNode::Continue {
            state_ty,
            result_ty,
            next,
        } => arena.reuse_value(
            value,
            ValueNode::Continue {
                state_ty: remap_value_type_global_ids(arena, state_ty, definitions, inductives),
                result_ty: remap_value_type_global_ids(arena, result_ty, definitions, inductives),
                next: remap_value_global_ids(arena, next, definitions, inductives),
            },
        ),
        ValueNode::Finish {
            state_ty,
            result_ty,
            output,
        } => arena.reuse_value(
            value,
            ValueNode::Finish {
                state_ty: remap_value_type_global_ids(arena, state_ty, definitions, inductives),
                result_ty: remap_value_type_global_ids(arena, result_ty, definitions, inductives),
                output: remap_value_global_ids(arena, output, definitions, inductives),
            },
        ),
        ValueNode::InductiveConstructor {
            indspec,
            parameters,
            idx,
            fields,
        } => arena.reuse_value(
            value,
            ValueNode::InductiveConstructor {
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
        ValueNode::Bound(_) | ValueNode::ModuleParam(_) => value,
    }
}

pub fn remap_computation_global_ids(
    arena: &Arena,
    computation: Computation,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> Computation {
    if definitions.is_empty() && inductives.is_empty() {
        return computation;
    }
    let value = |value| remap_value_global_ids(arena, value, definitions, inductives);
    let recur = |term| remap_computation_global_ids(arena, term, definitions, inductives);
    let value_ty = |ty| remap_value_type_global_ids(arena, ty, definitions, inductives);
    match arena.get(computation) {
        ComputationNode::DefinedConstant(id) => arena.reuse_computation(
            computation,
            ComputationNode::DefinedConstant(definitions.get(&id).copied().unwrap_or(id)),
        ),
        ComputationNode::Meta {
            metavariable,
            spine,
        } => arena.reuse_computation(
            computation,
            ComputationNode::Meta {
                metavariable,
                spine: remap_program_arguments(arena, spine, definitions, inductives),
            },
        ),
        ComputationNode::Return { value: item } => {
            arena.reuse_computation(computation, ComputationNode::Return { value: value(item) })
        }
        ComputationNode::Force { value: item } => {
            arena.reuse_computation(computation, ComputationNode::Force { value: value(item) })
        }
        ComputationNode::Lambda {
            var,
            value_ty: ty,
            body,
        } => arena.reuse_computation(
            computation,
            ComputationNode::Lambda {
                var,
                value_ty: value_ty(ty),
                body: recur(body),
            },
        ),
        ComputationNode::Application {
            computation: function,
            value: argument,
        } => arena.reuse_computation(
            computation,
            ComputationNode::Application {
                computation: recur(function),
                value: value(argument),
            },
        ),
        ComputationNode::Sequence {
            computation: first,
            var,
            value_ty: ty,
            body,
        } => arena.reuse_computation(
            computation,
            ComputationNode::Sequence {
                computation: recur(first),
                var,
                value_ty: value_ty(ty),
                body: recur(body),
            },
        ),
        ComputationNode::ValueLet {
            var,
            value_ty: ty,
            value: item,
            body,
        } => arena.reuse_computation(
            computation,
            ComputationNode::ValueLet {
                var,
                value_ty: value_ty(ty),
                value: value(item),
                body: recur(body),
            },
        ),
        ComputationNode::Case {
            indspec,
            scrutinee,
            branches,
        } => arena.reuse_computation(
            computation,
            ComputationNode::Case {
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
        ComputationNode::Run {
            state_ty,
            result_ty,
            step,
            initial,
        } => arena.reuse_computation(
            computation,
            ComputationNode::Run {
                state_ty: value_ty(state_ty),
                result_ty: value_ty(result_ty),
                step: value(step),
                initial: value(initial),
            },
        ),
        ComputationNode::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => arena.reuse_computation(
            computation,
            ComputationNode::RunCase {
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
            ProgramArgument::Type(ty) => {
                ProgramArgument::Type(subst_value_type_module_params(arena, ty, substitutions))
            }
            ProgramArgument::Value(value) => {
                ProgramArgument::Value(subst_value_module_params(arena, value, substitutions))
            }
        })
        .collect()
}

pub fn subst_value_module_params(
    arena: &Arena,
    value: Value,
    substitutions: &[(ModuleParamId, ModuleArgument)],
) -> Value {
    if substitutions.is_empty() {
        return value;
    }
    match arena.get(value) {
        ValueNode::ModuleParam(id) => substitutions
            .iter()
            .find_map(|(candidate, argument)| (*candidate == id).then_some(argument))
            .and_then(|argument| match argument {
                ModuleArgument::ProgramValue(value) => Some(*value),
                _ => None,
            })
            .unwrap_or(value),
        ValueNode::Meta {
            metavariable,
            spine,
        } => arena.reuse_value(
            value,
            ValueNode::Meta {
                metavariable,
                spine: subst_program_arguments(arena, spine, substitutions),
            },
        ),
        ValueNode::Thunk { computation } => arena.reuse_value(
            value,
            ValueNode::Thunk {
                computation: subst_computation_module_params(arena, computation, substitutions),
            },
        ),
        ValueNode::Continue {
            state_ty,
            result_ty,
            next,
        } => arena.reuse_value(
            value,
            ValueNode::Continue {
                state_ty: subst_value_type_module_params(arena, state_ty, substitutions),
                result_ty: subst_value_type_module_params(arena, result_ty, substitutions),
                next: subst_value_module_params(arena, next, substitutions),
            },
        ),
        ValueNode::Finish {
            state_ty,
            result_ty,
            output,
        } => arena.reuse_value(
            value,
            ValueNode::Finish {
                state_ty: subst_value_type_module_params(arena, state_ty, substitutions),
                result_ty: subst_value_type_module_params(arena, result_ty, substitutions),
                output: subst_value_module_params(arena, output, substitutions),
            },
        ),
        ValueNode::InductiveConstructor {
            indspec,
            parameters,
            idx,
            fields,
        } => arena.reuse_value(
            value,
            ValueNode::InductiveConstructor {
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
    term: Computation,
    substitutions: &[(ModuleParamId, ModuleArgument)],
) -> Computation {
    if substitutions.is_empty() {
        return term;
    }
    match arena.get(term) {
        ComputationNode::Meta {
            metavariable,
            spine,
        } => arena.reuse_computation(
            term,
            ComputationNode::Meta {
                metavariable,
                spine: subst_program_arguments(arena, spine, substitutions),
            },
        ),
        ComputationNode::Return { value } => arena.reuse_computation(
            term,
            ComputationNode::Return {
                value: subst_value_module_params(arena, value, substitutions),
            },
        ),
        ComputationNode::Force { value } => arena.reuse_computation(
            term,
            ComputationNode::Force {
                value: subst_value_module_params(arena, value, substitutions),
            },
        ),
        ComputationNode::Lambda {
            var,
            value_ty,
            body,
        } => arena.reuse_computation(
            term,
            ComputationNode::Lambda {
                var,
                value_ty: subst_value_type_module_params(arena, value_ty, substitutions),
                body: subst_computation_module_params(arena, body, substitutions),
            },
        ),
        ComputationNode::Application { computation, value } => arena.reuse_computation(
            term,
            ComputationNode::Application {
                computation: subst_computation_module_params(arena, computation, substitutions),
                value: subst_value_module_params(arena, value, substitutions),
            },
        ),
        ComputationNode::Sequence {
            computation,
            var,
            value_ty,
            body,
        } => arena.reuse_computation(
            term,
            ComputationNode::Sequence {
                computation: subst_computation_module_params(arena, computation, substitutions),
                var,
                value_ty: subst_value_type_module_params(arena, value_ty, substitutions),
                body: subst_computation_module_params(arena, body, substitutions),
            },
        ),
        ComputationNode::ValueLet {
            var,
            value_ty,
            value,
            body,
        } => arena.reuse_computation(
            term,
            ComputationNode::ValueLet {
                var,
                value_ty: subst_value_type_module_params(arena, value_ty, substitutions),
                value: subst_value_module_params(arena, value, substitutions),
                body: subst_computation_module_params(arena, body, substitutions),
            },
        ),
        ComputationNode::Case {
            indspec,
            scrutinee,
            branches,
        } => arena.reuse_computation(
            term,
            ComputationNode::Case {
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
        ComputationNode::Run {
            state_ty,
            result_ty,
            step,
            initial,
        } => arena.reuse_computation(
            term,
            ComputationNode::Run {
                state_ty: subst_value_type_module_params(arena, state_ty, substitutions),
                result_ty: subst_value_type_module_params(arena, result_ty, substitutions),
                step: subst_value_module_params(arena, step, substitutions),
                initial: subst_value_module_params(arena, initial, substitutions),
            },
        ),
        ComputationNode::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => arena.reuse_computation(
            term,
            ComputationNode::RunCase {
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
