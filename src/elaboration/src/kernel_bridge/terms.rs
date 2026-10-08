//! Source handle adapters to kernel structural operations and reduction.
use crate::raw::{environment::CrateEnv, exp::*, program::*, traversal::Term};

pub fn shift_bound_indices(arena: &Arena, exp: Exp, amount: usize, cutoff: usize) -> Exp {
    Exp(kernel::calculus::shift(&arena.core, exp.0, amount, cutoff).expect("valid shift"))
}

pub fn instantiate(arena: &Arena, body: Exp, argument: Exp) -> Exp {
    instantiate_at(arena, body, argument, 0)
}

pub fn instantiate_at(arena: &Arena, body: Exp, argument: Exp, inner: usize) -> Exp {
    instantiate_telescope_at(arena, body, &[argument], inner)
}

pub fn instantiate_telescope(arena: &Arena, exp: Exp, arguments: &[Exp]) -> Exp {
    instantiate_telescope_at(arena, exp, arguments, 0)
}

pub fn instantiate_outer_telescope(
    arena: &Arena,
    exp: Exp,
    arguments: &[Exp],
    inner: usize,
) -> Exp {
    instantiate_telescope_at(arena, exp, arguments, inner)
}

fn instantiate_telescope_at(arena: &Arena, exp: Exp, arguments: &[Exp], inner: usize) -> Exp {
    Exp(kernel::calculus::instantiate_at(
        &arena.core,
        exp.0,
        &arguments.iter().map(|e| e.0).collect::<Vec<_>>(),
        inner,
    )
    .expect("valid substitution"))
}
pub fn remap_ambient_indices(arena: &Arena, exp: Exp, mapping: &[usize]) -> Exp {
    Exp(kernel::calculus::reindex(&arena.core, exp.0, |i| {
        Ok(mapping.get(i).copied().unwrap_or(i))
    })
    .expect("valid reindexing"))
}

pub fn exp_is_alpha_eq(env: &CrateEnv, left: Exp, right: Exp) -> bool {
    kernel::calculus::alpha_equal(&env.arena().core, left.0, right.0)
}
#[cfg(test)]
pub fn exp_reduce_if_top(env: &CrateEnv, exp: Exp) -> Option<Exp> {
    crate::kernel_bridge::expression(env, Term::Logical(exp), |env, e| {
        kernel::reduction::root(env, e)
    })
    .expect("resolved reduction")
    .map(Exp)
}
pub fn whnf(env: &CrateEnv, exp: Exp) -> Exp {
    if let Some(&result) = env.whnf_cache.borrow().get(&exp) {
        return result;
    }
    let result = Exp(
        crate::kernel_bridge::expression(env, Term::Logical(exp), |env, e| env.whnf(e))
            .expect("resolved weak head"),
    );
    env.whnf_cache.borrow_mut().insert(exp, result);
    result
}
pub fn reduce_one(env: &CrateEnv, exp: Exp) -> Option<Exp> {
    crate::kernel_bridge::expression(env, Term::Logical(exp), kernel::reduction::reduce_once)
        .expect("resolved reduction")
        .map(Exp)
}
pub fn normalize(env: &CrateEnv, exp: Exp) -> Exp {
    Exp(
        crate::kernel_bridge::expression(env, Term::Logical(exp), kernel::reduction::normalize)
            .expect("resolved normalization"),
    )
}
#[allow(dead_code)] // Retained for kernel debugging and regression tests.
pub fn convertible(env: &CrateEnv, left: Exp, right: Exp) -> bool {
    resolved_convertible(env, left, right).unwrap_or(false)
}
/// Only resolved kernel comparisons are stable enough to retain across imports.
/// An expression that cannot yet be registered must be retried later.
pub(crate) fn resolved_convertible(env: &CrateEnv, left: Exp, right: Exp) -> Option<bool> {
    if exp_is_alpha_eq(env, left, right) {
        return Some(true);
    }
    let left = crate::kernel_bridge::expression(env, Term::Logical(left), |_, e| Ok(e)).ok()?;
    let right = crate::kernel_bridge::expression(env, Term::Logical(right), |_, e| Ok(e)).ok()?;
    kernel::reduction::convertible(&env.kernel.borrow(), left, right).ok()
}
fn conversion(env: &CrateEnv, left: Exp, right: Exp, erase: bool) -> bool {
    if exp_is_alpha_eq(env, left, right) {
        return true;
    }
    let left = crate::kernel_bridge::expression(env, Term::Logical(left), |_, e| Ok(e));
    let right = crate::kernel_bridge::expression(env, Term::Logical(right), |_, e| Ok(e));
    match (left, right) {
        (Ok(left), Ok(right)) => {
            if erase {
                kernel::reduction::erased_convertible(&env.kernel.borrow(), left, right)
                    .unwrap_or(false)
            } else {
                kernel::reduction::convertible(&env.kernel.borrow(), left, right).unwrap_or(false)
            }
        }
        _ => false,
    }
}
#[allow(dead_code)] // Retained for kernel debugging and regression tests.
pub fn erased_convertible(env: &CrateEnv, left: Exp, right: Exp) -> bool {
    conversion(env, left, right, true)
}
pub(crate) fn type_head_normal(env: &CrateEnv, ty: Exp) -> Exp {
    whnf(env, ty)
}
pub(crate) fn base_carrier(env: &CrateEnv, ty: Exp) -> Exp {
    let mut ty = whnf(env, ty);
    while let ExpNode::TypeLift { superset, .. } = env.arena().get(ty) {
        ty = whnf(env, superset);
    }
    ty
}

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

fn substitute_program_parameters(
    arena: &Arena,
    term: kernel::syntax::Expression,
    arguments: &[ValueType],
    depth: usize,
) -> kernel::syntax::Expression {
    kernel::calculus::instantiate_at(
        &arena.core,
        term,
        &arguments.iter().map(|ty| ty.0).collect::<Vec<_>>(),
        depth,
    )
    .expect("valid Program parameter substitution")
}
pub fn instantiate_value_type_parameters(
    arena: &Arena,
    ty: ValueType,
    arguments: &[ValueType],
    depth: usize,
) -> ValueType {
    ValueType(substitute_program_parameters(arena, ty.0, arguments, depth))
}
pub fn instantiate_computation_type_parameters(
    arena: &Arena,
    ty: ComputationType,
    arguments: &[ValueType],
    depth: usize,
) -> ComputationType {
    ComputationType(substitute_program_parameters(arena, ty.0, arguments, depth))
}
#[cfg(test)]
fn instantiate_term(
    env: &CrateEnv,
    term: Term,
    arguments: &[ValueType],
    depth: usize,
) -> kernel::syntax::Expression {
    let arguments = arguments
        .iter()
        .map(|ty| {
            crate::kernel_bridge::expression(env, Term::ValueType(*ty), |_, e| Ok(e))
                .map(ValueType)
                .expect("resolved Program argument")
        })
        .collect::<Vec<_>>();
    crate::kernel_bridge::expression(env, term, |_, e| {
        Ok(substitute_program_parameters(
            env.arena(),
            e,
            &arguments,
            depth,
        ))
    })
    .expect("resolved Program body")
}
#[cfg(test)]
pub fn instantiate_computation_parameters(
    env: &CrateEnv,
    computation: ComputationTerm,
    arguments: &[ValueType],
    depth: usize,
) -> ComputationTerm {
    if arguments.is_empty() {
        return computation;
    }
    ComputationTerm(instantiate_term(
        env,
        Term::Computation(computation),
        arguments,
        depth,
    ))
}
