//! Source ID remapping and adapters to the common kernel calculus.
use crate::raw::{
    environment::{CrateEnv, ModuleArgument},
    exp::Arena,
    ids::{DefId, ModuleParamId, ProgramInductiveId},
    program::*,
    traversal::Term,
};
use std::collections::HashMap;
pub fn value_type_is_alpha_eq(arena: &Arena, left: ValueType, right: ValueType) -> bool {
    kernel::calculus::alpha_equal(&arena.core, left.0, right.0)
}
pub fn shift_value_type_indices(
    arena: &Arena,
    term: ValueType,
    amount: usize,
    cutoff: usize,
) -> ValueType {
    ValueType(kernel::calculus::shift(&arena.core, term.0, amount, cutoff).expect("valid shift"))
}
#[cfg(test)]
pub fn computation_type_is_alpha_eq(
    arena: &Arena,
    left: ComputationType,
    right: ComputationType,
) -> bool {
    kernel::calculus::alpha_equal(&arena.core, left.0, right.0)
}
#[cfg(test)]
pub fn value_is_alpha_eq(arena: &Arena, left: ValueTerm, right: ValueTerm) -> bool {
    kernel::calculus::alpha_equal(&arena.core, left.0, right.0)
}
#[cfg(test)]
pub fn computation_is_alpha_eq(
    arena: &Arena,
    left: ComputationTerm,
    right: ComputationTerm,
) -> bool {
    kernel::calculus::alpha_equal(&arena.core, left.0, right.0)
}
#[cfg(test)]
pub fn shift_computation_indices(
    arena: &Arena,
    term: ComputationTerm,
    amount: usize,
    cutoff: usize,
) -> ComputationTerm {
    ComputationTerm(
        kernel::calculus::shift(&arena.core, term.0, amount, cutoff).expect("valid shift"),
    )
}
#[cfg(test)]
pub fn strengthen_value_type(arena: &Arena, ty: ValueType, target: usize) -> Option<ValueType> {
    kernel::calculus::strengthen(&arena.core, ty.0, target)
        .ok()
        .map(ValueType)
}

#[cfg(test)]
pub fn instantiate_value_type(
    arena: &Arena,
    body: ValueType,
    argument: ValueType,
    target: usize,
) -> ValueType {
    ValueType(
        kernel::calculus::instantiate_at(&arena.core, body.0, &[argument.0], target)
            .expect("valid substitution"),
    )
}
pub fn instantiate_type_telescope(
    arena: &Arena,
    ty: ValueType,
    arguments: &[ValueType],
) -> ValueType {
    ValueType(
        kernel::calculus::instantiate(
            &arena.core,
            ty.0,
            &arguments.iter().map(|e| e.0).collect::<Vec<_>>(),
        )
        .expect("valid substitution"),
    )
}
#[cfg(test)]
pub fn instantiate_value_in_computation(
    env: &CrateEnv,
    body: ComputationTerm,
    argument: ValueTerm,
) -> ComputationTerm {
    let body = crate::kernel_bridge::expression(env, Term::Computation(body), |_, e| Ok(e))
        .expect("resolved computation");
    let argument = crate::kernel_bridge::expression(env, Term::Value(argument), |_, e| Ok(e))
        .expect("resolved argument");
    ComputationTerm(
        kernel::calculus::instantiate(&env.arena().core, body, &[argument])
            .expect("valid substitution"),
    )
}
pub fn reduce_computation_once(env: &CrateEnv, term: ComputationTerm) -> Option<ComputationTerm> {
    crate::kernel_bridge::expression(env, Term::Computation(term), kernel::reduction::reduce_once)
        .expect("resolved computation")
        .map(ComputationTerm)
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Evaluation {
    Normal(ComputationTerm),
    OutOfFuel(ComputationTerm),
}
pub fn evaluate_computation_with_fuel(
    env: &CrateEnv,
    term: ComputationTerm,
    fuel: usize,
) -> Evaluation {
    match crate::kernel_bridge::expression(env, Term::Computation(term), |env, e| {
        kernel::reduction::evaluate(env, e, fuel)
    })
    .expect("resolved evaluation")
    {
        kernel::reduction::Evaluation::Normal(e) => Evaluation::Normal(ComputationTerm(e)),
        kernel::reduction::Evaluation::OutOfFuel(e) => Evaluation::OutOfFuel(ComputationTerm(e)),
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
    logical_inductives: &HashMap<crate::raw::ids::InductiveId, crate::raw::ids::InductiveId>,
) -> Vec<ProgramArgument> {
    arguments
        .into_iter()
        .map(|argument| match argument {
            ProgramArgument::ValueType(ty) => ProgramArgument::ValueType(
                remap_value_type_global_ids(arena, ty, definitions, inductives),
            ),
            ProgramArgument::ValueTerm(value) => ProgramArgument::ValueTerm(
                remap_value_global_ids(arena, value, definitions, inductives, logical_inductives),
            ),
        })
        .collect()
}

pub fn remap_value_global_ids(
    arena: &Arena,
    value: ValueTerm,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
    logical_inductives: &HashMap<crate::raw::ids::InductiveId, crate::raw::ids::InductiveId>,
) -> ValueTerm {
    if definitions.is_empty() && inductives.is_empty() && logical_inductives.is_empty() {
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
                spine: remap_program_arguments(
                    arena,
                    spine,
                    definitions,
                    inductives,
                    logical_inductives,
                ),
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
                    logical_inductives,
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
                next: remap_value_global_ids(
                    arena,
                    next,
                    definitions,
                    inductives,
                    logical_inductives,
                ),
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
                output: remap_value_global_ids(
                    arena,
                    output,
                    definitions,
                    inductives,
                    logical_inductives,
                ),
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
                    .map(|value| {
                        remap_value_global_ids(
                            arena,
                            value,
                            definitions,
                            inductives,
                            logical_inductives,
                        )
                    })
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
    logical_inductives: &HashMap<crate::raw::ids::InductiveId, crate::raw::ids::InductiveId>,
) -> ComputationTerm {
    if definitions.is_empty() && inductives.is_empty() && logical_inductives.is_empty() {
        return computation;
    }
    let value =
        |value| remap_value_global_ids(arena, value, definitions, inductives, logical_inductives);
    let recur = |term| {
        remap_computation_global_ids(arena, term, definitions, inductives, logical_inductives)
    };
    let value_ty = |ty| remap_value_type_global_ids(arena, ty, definitions, inductives);
    let comp_ty = |ty| remap_computation_type_global_ids(arena, ty, definitions, inductives);
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
                spine: remap_program_arguments(
                    arena,
                    spine,
                    definitions,
                    inductives,
                    logical_inductives,
                ),
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
        ComputationTermNode::StepRec {
            state_ty,
            result_ty,
            computation_ty,
            on_continue,
            on_finish,
            scrutinee,
        } => arena.reuse_computation(
            computation,
            ComputationTermNode::StepRec {
                state_ty: value_ty(state_ty),
                result_ty: value_ty(result_ty),
                computation_ty: comp_ty(computation_ty),
                on_continue: recur(on_continue),
                on_finish: recur(on_finish),
                scrutinee: value(scrutinee),
            },
        ),
        ComputationTermNode::Run {
            state_ty,
            result_ty,
            step,
            initial,
            accessibility,
        } => arena.reuse_computation(
            computation,
            ComputationTermNode::Run {
                state_ty: value_ty(state_ty),
                result_ty: value_ty(result_ty),
                step: value(step),
                initial: value(initial),
                accessibility: crate::raw::calculus::remap_all_global_ids(
                    arena,
                    accessibility,
                    definitions,
                    logical_inductives,
                    inductives,
                ),
            },
        ),
        ComputationTermNode::RunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            accessibility,
            transition_equality,
        } => arena.reuse_computation(
            computation,
            ComputationTermNode::RunCase {
                state_ty: value_ty(state_ty),
                result_ty: value_ty(result_ty),
                step: value(step),
                initial: value(initial),
                transition: recur(transition),
                accessibility: crate::raw::calculus::remap_all_global_ids(
                    arena,
                    accessibility,
                    definitions,
                    logical_inductives,
                    inductives,
                ),
                transition_equality: crate::raw::calculus::remap_all_global_ids(
                    arena,
                    transition_equality,
                    definitions,
                    logical_inductives,
                    inductives,
                ),
            },
        ),
    }
}

pub fn subst_value_type_module_params(
    arena: &Arena,
    ty: ValueType,
    substitutions: &[(ModuleParamId, ModuleArgument)],
) -> ValueType {
    let super::traversal::Term::ValueType(result) =
        super::traversal::Term::ValueType(ty).substitute(arena, substitutions, &[])
    else {
        unreachable!()
    };
    result
}

pub fn subst_computation_type_module_params(
    arena: &Arena,
    ty: ComputationType,
    substitutions: &[(ModuleParamId, ModuleArgument)],
) -> ComputationType {
    let super::traversal::Term::ComputationType(result) =
        super::traversal::Term::ComputationType(ty).substitute(arena, substitutions, &[])
    else {
        unreachable!()
    };
    result
}

pub fn subst_value_module_params(
    arena: &Arena,
    value: ValueTerm,
    substitutions: &[(ModuleParamId, ModuleArgument)],
    reflected_substitutions: &[(ModuleParamId, crate::raw::exp::Exp)],
) -> ValueTerm {
    let super::traversal::Term::Value(result) = super::traversal::Term::Value(value).substitute(
        arena,
        substitutions,
        reflected_substitutions,
    ) else {
        unreachable!()
    };
    result
}

pub fn subst_computation_module_params(
    arena: &Arena,
    term: ComputationTerm,
    substitutions: &[(ModuleParamId, ModuleArgument)],
    reflected_substitutions: &[(ModuleParamId, crate::raw::exp::Exp)],
) -> ComputationTerm {
    let super::traversal::Term::Computation(result) = super::traversal::Term::Computation(term)
        .substitute(arena, substitutions, reflected_substitutions)
    else {
        unreachable!()
    };
    result
}
