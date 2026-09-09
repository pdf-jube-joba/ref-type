//! Simultaneous, capture-avoiding instantiation of Program definition parameters.
use super::{exp::Arena, program::*, program_calculus::shift_value_type_indices};

pub fn instantiate_value_type(
    arena: &Arena,
    ty: ValueType,
    arguments: &[ValueType],
    depth: usize,
) -> ValueType {
    match arena.get(ty) {
        ValueTypeNode::Bound(index) if index >= depth && index < depth + arguments.len() => {
            shift_value_type_indices(
                arena,
                arguments[arguments.len() - 1 - (index - depth)],
                depth,
                0,
            )
        }
        ValueTypeNode::Bound(index) if index >= depth + arguments.len() => {
            arena.value_type_bound(index - arguments.len())
        }
        ValueTypeNode::Thunk { computation_ty } => arena.reuse_value_type(
            ty,
            ValueTypeNode::Thunk {
                computation_ty: instantiate_computation_type(
                    arena,
                    computation_ty,
                    arguments,
                    depth,
                ),
            },
        ),
        ValueTypeNode::RunStep {
            state_ty,
            result_ty,
        } => arena.reuse_value_type(
            ty,
            ValueTypeNode::RunStep {
                state_ty: instantiate_value_type(arena, state_ty, arguments, depth),
                result_ty: instantiate_value_type(arena, result_ty, arguments, depth),
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
                    .map(|t| instantiate_value_type(arena, t, arguments, depth))
                    .collect(),
            },
        ),
        _ => ty,
    }
}

pub fn instantiate_computation_type(
    arena: &Arena,
    ty: ComputationType,
    arguments: &[ValueType],
    depth: usize,
) -> ComputationType {
    match arena.get(ty) {
        ComputationTypeNode::Return { value_ty } => arena.reuse_computation_type(
            ty,
            ComputationTypeNode::Return {
                value_ty: instantiate_value_type(arena, value_ty, arguments, depth),
            },
        ),
        ComputationTypeNode::Function { domain, codomain } => arena.reuse_computation_type(
            ty,
            ComputationTypeNode::Function {
                domain: instantiate_value_type(arena, domain, arguments, depth),
                codomain: instantiate_computation_type(arena, codomain, arguments, depth),
            },
        ),
        _ => ty,
    }
}

pub fn instantiate_value(
    arena: &Arena,
    value: ValueTerm,
    arguments: &[ValueType],
    cutoff: usize,
) -> ValueTerm {
    if arguments.is_empty() {
        return value;
    }

    fn go(arena: &Arena, value: ValueTerm, arguments: &[ValueType], cutoff: usize) -> ValueTerm {
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
                        .map(|t| instantiate_value_type(arena, t, arguments, cutoff))
                        .collect(),
                },
            ),
            ValueTermNode::Bound(index) if index >= cutoff + arguments.len() => {
                arena.reuse_value(value, ValueTermNode::Bound(index - arguments.len()))
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
                                instantiate_value_type(arena, t, arguments, cutoff),
                            ),
                            ProgramArgument::ValueTerm(v) => {
                                ProgramArgument::ValueTerm(go(arena, v, arguments, cutoff))
                            }
                        })
                        .collect(),
                },
            ),
            ValueTermNode::Thunk { computation } => arena.reuse_value(
                value,
                ValueTermNode::Thunk {
                    computation: instantiate_computation(arena, computation, arguments, cutoff),
                },
            ),
            ValueTermNode::Continue {
                state_ty,
                result_ty,
                next,
            } => arena.reuse_value(
                value,
                ValueTermNode::Continue {
                    state_ty: instantiate_value_type(arena, state_ty, arguments, cutoff),
                    result_ty: instantiate_value_type(arena, result_ty, arguments, cutoff),
                    next: go(arena, next, arguments, cutoff),
                },
            ),
            ValueTermNode::Finish {
                state_ty,
                result_ty,
                output,
            } => arena.reuse_value(
                value,
                ValueTermNode::Finish {
                    state_ty: instantiate_value_type(arena, state_ty, arguments, cutoff),
                    result_ty: instantiate_value_type(arena, result_ty, arguments, cutoff),
                    output: go(arena, output, arguments, cutoff),
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
                        .map(|t| instantiate_value_type(arena, t, arguments, cutoff))
                        .collect(),
                    idx,
                    fields: fields
                        .into_iter()
                        .map(|v| go(arena, v, arguments, cutoff))
                        .collect(),
                },
            ),
            ValueTermNode::Bound(_)
            | ValueTermNode::ModuleParam(_)
            | ValueTermNode::DefinedConstant(_) => value,
        }
    }
    go(arena, value, arguments, cutoff)
}

pub fn instantiate_computation(
    arena: &Arena,
    computation: ComputationTerm,
    arguments: &[ValueType],
    cutoff: usize,
) -> ComputationTerm {
    if arguments.is_empty() {
        return computation;
    }

    fn go(
        arena: &Arena,
        term: ComputationTerm,
        arguments: &[ValueType],
        cutoff: usize,
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
                        .map(|t| instantiate_value_type(arena, t, arguments, cutoff))
                        .collect(),
                },
            ),
            ComputationTermNode::Return { value } => arena.reuse_computation(
                term,
                ComputationTermNode::Return {
                    value: instantiate_value(arena, value, arguments, cutoff),
                },
            ),
            ComputationTermNode::Force { value } => arena.reuse_computation(
                term,
                ComputationTermNode::Force {
                    value: instantiate_value(arena, value, arguments, cutoff),
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
                    value_ty: instantiate_value_type(arena, value_ty, arguments, cutoff),
                    body: go(arena, body, arguments, cutoff + 1),
                },
            ),
            ComputationTermNode::Application { computation, value } => arena.reuse_computation(
                term,
                ComputationTermNode::Application {
                    computation: go(arena, computation, arguments, cutoff),
                    value: instantiate_value(arena, value, arguments, cutoff),
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
                    computation: go(arena, computation, arguments, cutoff),
                    var,
                    value_ty: instantiate_value_type(arena, value_ty, arguments, cutoff),
                    body: go(arena, body, arguments, cutoff + 1),
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
                    value_ty: instantiate_value_type(arena, value_ty, arguments, cutoff),
                    value: instantiate_value(arena, value, arguments, cutoff),
                    body: go(arena, body, arguments, cutoff + 1),
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
                    scrutinee: instantiate_value(arena, scrutinee, arguments, cutoff),
                    branches: branches
                        .into_iter()
                        .map(|b| ProgramCaseBranch {
                            body: go(arena, b.body, arguments, cutoff + b.binders.len()),
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
                    state_ty: instantiate_value_type(arena, state_ty, arguments, cutoff),
                    result_ty: instantiate_value_type(arena, result_ty, arguments, cutoff),
                    step: instantiate_value(arena, step, arguments, cutoff),
                    initial: instantiate_value(arena, initial, arguments, cutoff),
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
                    state_ty: instantiate_value_type(arena, state_ty, arguments, cutoff),
                    result_ty: instantiate_value_type(arena, result_ty, arguments, cutoff),
                    step: instantiate_value(arena, step, arguments, cutoff),
                    initial: instantiate_value(arena, initial, arguments, cutoff),
                    transition: go(arena, transition, arguments, cutoff),
                },
            ),
            ComputationTermNode::Meta { .. } | ComputationTermNode::DefinedConstant(_) => term,
        }
    }
    go(arena, computation, arguments, cutoff)
}
