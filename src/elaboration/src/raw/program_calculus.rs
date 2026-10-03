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
    term: ValueType,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> ValueType {
    let Term::ValueType(result) = super::remapping::remap(
        arena,
        Term::ValueType(term),
        definitions,
        &HashMap::new(),
        inductives,
    ) else {
        unreachable!()
    };
    result
}

pub fn remap_computation_type_global_ids(
    arena: &Arena,
    term: ComputationType,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> ComputationType {
    let Term::ComputationType(result) = super::remapping::remap(
        arena,
        Term::ComputationType(term),
        definitions,
        &HashMap::new(),
        inductives,
    ) else {
        unreachable!()
    };
    result
}

pub fn remap_value_global_ids(
    arena: &Arena,
    term: ValueTerm,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
    logical_inductives: &HashMap<crate::raw::ids::InductiveId, crate::raw::ids::InductiveId>,
) -> ValueTerm {
    let Term::Value(result) = super::remapping::remap(
        arena,
        Term::Value(term),
        definitions,
        logical_inductives,
        inductives,
    ) else {
        unreachable!()
    };
    result
}

pub fn remap_computation_global_ids(
    arena: &Arena,
    term: ComputationTerm,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
    logical_inductives: &HashMap<crate::raw::ids::InductiveId, crate::raw::ids::InductiveId>,
) -> ComputationTerm {
    let Term::Computation(result) = super::remapping::remap(
        arena,
        Term::Computation(term),
        definitions,
        logical_inductives,
        inductives,
    ) else {
        unreachable!()
    };
    result
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
