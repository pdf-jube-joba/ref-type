//! Structural operations and reduction for Set/Prop expressions.

use crate::raw::{
    environment::CrateEnv,
    exp::*,
    ids::{DefId, InductiveId, ModuleParamId, ProgramInductiveId},
};
use std::collections::HashMap;

pub fn map_children(mut node: ExpNode, mut map: impl FnMut(Exp) -> Exp) -> ExpNode {
    macro_rules! one { ($($x:ident),+ $(,)?) => {{ $( *$x = map(*$x); )+ }}; }
    macro_rules! vecs { ($($x:ident),+ $(,)?) => { $( for item in $x.iter_mut() { *item = map(*item); } )+ }; }
    match &mut node {
        ExpNode::Sort(_)
        | ExpNode::Bound(_)
        | ExpNode::ModuleParam(_)
        | ExpNode::ReflectedProgramParam(_)
        | ExpNode::DefinedConstant(_)
        | ExpNode::BoxType { .. } => {}
        ExpNode::Meta { spine, .. } => vecs!(spine),
        ExpNode::DefinitionInstance { arguments, .. } => vecs!(arguments),
        ExpNode::Prod { ty, body, .. } | ExpNode::Lam { ty, body, .. } => one!(ty, body),
        ExpNode::Ascribe {
            term: func,
            ty: arg,
        }
        | ExpNode::App { func, arg } => one!(func, arg),
        ExpNode::IndType { parameters, .. } | ExpNode::IndCtor { parameters, .. } => {
            vecs!(parameters)
        }
        ExpNode::IndElim {
            motive_bindings,
            elim,
            return_type,
            cases,
            ..
        } => {
            for (_, ty) in motive_bindings {
                *ty = map(*ty);
            }
            one!(elim, return_type);
            vecs!(cases);
        }
        ExpNode::IndCase {
            scrutinee,
            return_type,
            branches,
            ..
        } => {
            one!(scrutinee, return_type);
            vecs!(branches);
        }
        ExpNode::ReflectedProgramCase {
            scrutinee,
            branches,
            ..
        } => {
            one!(scrutinee);
            for branch in branches {
                branch.body = map(branch.body);
            }
        }
        ExpNode::RunStep {
            state_ty,
            result_ty,
        } => one!(state_ty, result_ty),
        ExpNode::Continue {
            state_ty,
            result_ty,
            next,
        } => one!(state_ty, result_ty, next),
        ExpNode::Finish {
            state_ty,
            result_ty,
            output,
        } => one!(state_ty, result_ty, output),
        ExpNode::SetStepMatch {
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
        } => one!(state_ty, result_ty, motive, on_continue, on_finish),
        ExpNode::SetRun {
            state_ty,
            result_ty,
            step,
            initial,
            accessibility,
        } => one!(state_ty, result_ty, step, initial, accessibility),
        ExpNode::SetRunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            accessibility,
            transition_equality,
        } => one!(
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            accessibility,
            transition_equality
        ),
        ExpNode::BoxProgram { .. } => {}
        ExpNode::ForceBox { boxed, .. } => one!(boxed),
        ExpNode::BoxApp { function, argument } => one!(function, argument),
        ExpNode::PowerSet { set } | ExpNode::Exists { set } => one!(set),
        ExpNode::SubSet { set, predicate, .. } => one!(set, predicate),
        ExpNode::Pred {
            superset,
            subset,
            element,
        } => one!(superset, subset, element),
        ExpNode::TypeLift { superset, subset } => one!(superset, subset),
        ExpNode::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => one!(superset, subset, element, proof),
        ExpNode::Equal { left, right } => one!(left, right),
        ExpNode::Choice {
            set,
            existence,
            uniqueness,
        } => one!(set, existence, uniqueness),
        ExpNode::TakeProp {
            domain,
            proposition,
            map: function,
            existence,
        } => one!(domain, proposition, function, existence),
        ExpNode::Prove(Prove::ExistsIntro { element, set }) => one!(element, set),
        ExpNode::Prove(Prove::SubsetElim {
            element,
            subset,
            superset,
        }) => one!(element, subset, superset),
        ExpNode::Prove(Prove::IdRefl { element }) => one!(element),
        ExpNode::Prove(Prove::IdElim {
            left,
            right,
            ty,
            predicate,
            base,
            equality,
            ..
        }) => one!(left, right, ty, predicate, base, equality),
        ExpNode::Prove(Prove::Axiom(Axiom::SetExt {
            left,
            right,
            left_to_right,
            right_to_left,
        })) => one!(left, right, left_to_right, right_to_left),
        ExpNode::Prove(Prove::Axiom(Axiom::FunExt {
            left,
            right,
            pointwise,
        })) => one!(left, right, pointwise),
        ExpNode::Prove(Prove::Axiom(Axiom::ClassicalIndefiniteChoice {
            domain,
            family,
            inhabited,
        })) => one!(domain, family, inhabited),
        ExpNode::Prove(Prove::ChoiceEq {
            set,
            element,
            existence,
            uniqueness,
        }) => one!(set, element, existence, uniqueness),
    }
    node
}

pub fn exp_contains_bound(arena: &Arena, exp: Exp, target: usize) -> bool {
    use super::traversal::Term;
    fn go(
        arena: &Arena,
        exp: Exp,
        target: usize,
        seen: &mut rustc_hash::FxHashSet<(Exp, usize)>,
    ) -> bool {
        let term = Term::Logical(exp);
        if arena.max_loose_bound(term).is_none_or(|max| max < target) || !seen.insert((exp, target))
        {
            return false;
        }
        if let Some(index) = term.bound_index(arena) {
            return index == target;
        }
        let mut found = false;
        term.visit_children(arena, |child, depth| {
            if !found && let Term::Logical(child) = child {
                found = target
                    .checked_add(depth)
                    .is_some_and(|target| go(arena, child, target, seen));
            }
        });
        found
    }
    go(arena, exp, target, &mut rustc_hash::FxHashSet::default())
}

pub fn exp_contains_inductive(arena: &Arena, exp: Exp, inductive: InductiveId) -> bool {
    use super::traversal::Term;
    let mut pending = vec![exp];
    let mut seen = rustc_hash::FxHashSet::default();
    while let Some(e) = pending.pop() {
        if !seen.insert(e) {
            continue;
        }
        let matches = match *arena.borrow_exp(e) {
            ExpNode::IndType { indspec, .. }
            | ExpNode::IndCtor { indspec, .. }
            | ExpNode::IndElim { indspec, .. }
            | ExpNode::IndCase { indspec, .. } => indspec == inductive,
            _ => false,
        };
        if matches {
            return true;
        }
        Term::Logical(e).visit_children(arena, |child, _| {
            if let Term::Logical(e) = child {
                pending.push(e);
            }
        });
    }
    false
}
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

pub fn exp_subst_map(arena: &Arena, exp: Exp, substitutions: &[(ModuleParamId, Exp)]) -> Exp {
    let super::traversal::Term::Logical(e) =
        super::traversal::Term::Logical(exp).substitute(arena, &[], substitutions)
    else {
        unreachable!()
    };
    e
}

pub fn remap_global_ids(
    arena: &Arena,
    exp: Exp,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<InductiveId, InductiveId>,
) -> Exp {
    remap_all_global_ids(arena, exp, definitions, inductives, &HashMap::new())
}

pub fn remap_all_global_ids(
    arena: &Arena,
    exp: Exp,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<InductiveId, InductiveId>,
    program_inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
) -> Exp {
    let super::traversal::Term::Logical(result) = super::remapping::remap(
        arena,
        super::traversal::Term::Logical(exp),
        definitions,
        inductives,
        program_inductives,
    ) else {
        unreachable!()
    };
    result
}

pub fn exp_is_alpha_eq(env: &CrateEnv, left: Exp, right: Exp) -> bool {
    kernel::calculus::alpha_equal(&env.arena().core, left.0, right.0)
}
#[cfg(test)]
pub fn exp_reduce_if_top(env: &CrateEnv, exp: Exp) -> Option<Exp> {
    crate::kernel_bridge::expression(env, super::traversal::Term::Logical(exp), |env, e| {
        kernel::reduction::root(env, e)
    })
    .expect("resolved reduction")
    .map(Exp)
}
pub fn whnf(env: &CrateEnv, exp: Exp) -> Exp {
    if let Some(&result) = env.whnf_cache.borrow().get(&exp) {
        return result;
    }
    let result = Exp(crate::kernel_bridge::expression(
        env,
        super::traversal::Term::Logical(exp),
        |env, e| env.whnf(e),
    )
    .expect("resolved weak head"));
    env.whnf_cache.borrow_mut().insert(exp, result);
    result
}
pub fn reduce_one(env: &CrateEnv, exp: Exp) -> Option<Exp> {
    crate::kernel_bridge::expression(
        env,
        super::traversal::Term::Logical(exp),
        kernel::reduction::reduce_once,
    )
    .expect("resolved reduction")
    .map(Exp)
}
pub fn normalize(env: &CrateEnv, exp: Exp) -> Exp {
    Exp(crate::kernel_bridge::expression(
        env,
        super::traversal::Term::Logical(exp),
        kernel::reduction::normalize,
    )
    .expect("resolved normalization"))
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
    let left =
        crate::kernel_bridge::expression(env, super::traversal::Term::Logical(left), |_, e| Ok(e))
            .ok()?;
    let right =
        crate::kernel_bridge::expression(env, super::traversal::Term::Logical(right), |_, e| Ok(e))
            .ok()?;
    kernel::reduction::convertible(&env.kernel.borrow(), left, right).ok()
}
fn conversion(env: &CrateEnv, left: Exp, right: Exp, erase: bool) -> bool {
    if exp_is_alpha_eq(env, left, right) {
        return true;
    }
    let left =
        crate::kernel_bridge::expression(env, super::traversal::Term::Logical(left), |_, e| Ok(e));
    let right =
        crate::kernel_bridge::expression(env, super::traversal::Term::Logical(right), |_, e| Ok(e));
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
