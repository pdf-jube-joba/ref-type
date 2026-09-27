//! Program parameter instantiation through the common kernel substitution.
#[cfg(test)]
use super::{environment::CrateEnv, traversal::Term};
use super::{exp::Arena, program::*};

fn substitute(
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
pub fn instantiate_value_type(
    arena: &Arena,
    ty: ValueType,
    arguments: &[ValueType],
    depth: usize,
) -> ValueType {
    ValueType(substitute(arena, ty.0, arguments, depth))
}
pub fn instantiate_computation_type(
    arena: &Arena,
    ty: ComputationType,
    arguments: &[ValueType],
    depth: usize,
) -> ComputationType {
    ComputationType(substitute(arena, ty.0, arguments, depth))
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
        Ok(substitute(env.arena(), e, &arguments, depth))
    })
    .expect("resolved Program body")
}
#[cfg(test)]
pub fn instantiate_computation(
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
