//! Structural operations and reduction for Set/Prop expressions.

use crate::raw::{
    environment::{CrateEnv, DefinedConstant},
    exp::*,
    ids::{DefId, InductiveId, ModuleParamId, ProgramInductiveId, SymbolId},
    program::{ComputationTermNode, ComputationType},
};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::collections::HashMap;

pub fn map_children(mut node: ExpNode, mut map: impl FnMut(Exp) -> Exp) -> ExpNode {
    macro_rules! one { ($($x:ident),+ $(,)?) => {{ $( *$x = map($x.clone()); )+ }}; }
    macro_rules! vecs { ($($x:ident),+ $(,)?) => { $( for item in $x.iter_mut() { *item = map(item.clone()); } )+ }; }
    match &mut node {
        ExpNode::Sort(_)
        | ExpNode::Bound(_)
        | ExpNode::ModuleParam(_)
        | ExpNode::ReflectedProgramParam(_)
        | ExpNode::DefinedConstant(_)
        | ExpNode::BoxType { .. } => {}
        ExpNode::Meta { spine, .. } => vecs!(spine),
        ExpNode::Prod { ty, body, .. } | ExpNode::Lam { ty, body, .. } => one!(ty, body),
        ExpNode::App { func, arg } => one!(func, arg),
        ExpNode::IndType { parameters, .. } | ExpNode::IndCtor { parameters, .. } => {
            vecs!(parameters)
        }
        ExpNode::IndElim {
            elim,
            return_type,
            cases,
            ..
        } => {
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
                branch.body = map(branch.body.clone());
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
        ExpNode::Acc {
            state_ty,
            result_ty,
            step,
            state,
        } => one!(state_ty, result_ty, step, state),
        ExpNode::RunStepRec {
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
        } => one!(
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee
        ),
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
        ExpNode::Prove(Prove::AccIntro {
            state_ty,
            result_ty,
            step,
            state,
            predecessors,
        }) => one!(state_ty, result_ty, step, state, predecessors),
        ExpNode::Prove(Prove::AccDescent {
            state_ty,
            result_ty,
            step,
            from,
            to,
            accessibility,
            transition,
        }) => one!(
            state_ty,
            result_ty,
            step,
            from,
            to,
            accessibility,
            transition
        ),
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
        ExpNode::TakeSet {
            domain,
            codomain,
            map: function,
            existence,
            uniqueness,
        } => one!(domain, codomain, function, existence, uniqueness),
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
        ExpNode::Prove(Prove::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        }) => one!(func, domain, codomain, element, existence, uniqueness),
    }
    node
}

fn map_computational_children(node: ExpNode, mut map: impl FnMut(Exp) -> Exp) -> ExpNode {
    match node {
        ExpNode::SetRun {
            state_ty,
            result_ty,
            step,
            initial,
            accessibility,
        } => ExpNode::SetRun {
            state_ty: map(state_ty),
            result_ty: map(result_ty),
            step: map(step),
            initial: map(initial),
            accessibility,
        },
        ExpNode::SetRunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            accessibility,
            transition_equality,
        } => ExpNode::SetRunCase {
            state_ty: map(state_ty),
            result_ty: map(result_ty),
            step: map(step),
            initial: map(initial),
            transition: map(transition),
            accessibility,
            transition_equality,
        },
        ExpNode::BoxProgram {
            program_ty,
            program,
        } => ExpNode::BoxProgram {
            program_ty,
            program,
        },
        other => map_children(other, map),
    }
}

fn transform<F>(arena: &Arena, exp: Exp, depth: usize, operation: &mut F) -> Exp
where
    F: FnMut(Exp, usize) -> Option<Exp>,
{
    use super::traversal::{self, Term};
    traversal::logical(arena, exp, depth, &mut |term, depth| match term {
        Term::Logical(e) => operation(e, depth).map(Term::Logical),
        _ => None,
    })
}

fn direct_children(node: ExpNode) -> Vec<Exp> {
    let mut result = Vec::new();
    let _ = map_children(node, |child| {
        result.push(child.clone());
        child
    });
    result
}

pub fn exp_contains_bound(arena: &Arena, exp: Exp, target: usize) -> bool {
    fn go(arena: &Arena, exp: Exp, target: usize, depth: usize) -> bool {
        match arena.get(exp) {
            ExpNode::Bound(index) => index == target + depth,
            ExpNode::Prod { ty, body, .. } | ExpNode::Lam { ty, body, .. } => {
                go(arena, ty, target, depth) || go(arena, body, target, depth + 1)
            }
            ExpNode::SubSet { set, predicate, .. } => {
                go(arena, set, target, depth) || go(arena, predicate, target, depth + 1)
            }
            ExpNode::Prove(Prove::IdElim {
                left,
                right,
                ty,
                predicate,
                base,
                equality,
                ..
            }) => {
                [left, right, ty, base, equality]
                    .into_iter()
                    .any(|e| go(arena, e, target, depth))
                    || go(arena, predicate, target, depth + 1)
            }
            ExpNode::ReflectedProgramCase {
                scrutinee,
                branches,
                ..
            } => {
                go(arena, scrutinee, target, depth)
                    || branches
                        .into_iter()
                        .any(|b| go(arena, b.body, target, depth + b.binders.len()))
            }
            node => direct_children(node)
                .into_iter()
                .any(|e| go(arena, e, target, depth)),
        }
    }
    go(arena, exp, target, 0)
}

pub fn exp_contains_inductive(arena: &Arena, exp: Exp, inductive: InductiveId) -> bool {
    match arena.get(exp) {
        ExpNode::IndType {
            indspec,
            parameters,
        }
        | ExpNode::IndCtor {
            indspec,
            parameters,
            ..
        } => {
            indspec == inductive
                || parameters
                    .into_iter()
                    .any(|e| exp_contains_inductive(arena, e, inductive))
        }
        ExpNode::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => {
            indspec == inductive
                || [elim, return_type]
                    .into_iter()
                    .chain(cases)
                    .any(|e| exp_contains_inductive(arena, e, inductive))
        }
        ExpNode::IndCase {
            indspec,
            scrutinee,
            return_type,
            branches,
        } => {
            indspec == inductive
                || [scrutinee, return_type]
                    .into_iter()
                    .chain(branches)
                    .any(|e| exp_contains_inductive(arena, e, inductive))
        }
        node => direct_children(node)
            .into_iter()
            .any(|e| exp_contains_inductive(arena, e, inductive)),
    }
}

pub fn shift_bound_indices(arena: &Arena, exp: Exp, amount: usize, cutoff: usize) -> Exp {
    let super::traversal::Term::Logical(e) =
        super::traversal::Term::Logical(exp).shift(arena, amount, cutoff)
    else {
        unreachable!()
    };
    e
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
    if arguments.is_empty() {
        return exp;
    }
    use super::traversal::{self, Term};
    traversal::logical(arena, exp, 0, &mut |term, depth| {
        let Term::Logical(_) = term else {
            return None;
        };
        let index = term.clone().bound_index(arena)?;
        if index < depth + inner {
            return Some(term);
        }
        let telescope_index = index - depth - inner;
        Some(Term::Logical(if telescope_index < arguments.len() {
            shift_bound_indices(
                arena,
                arguments[arguments.len() - 1 - telescope_index].clone(),
                depth + inner,
                0,
            )
        } else {
            arena.exp_bound(index - arguments.len())
        }))
    })
}

pub fn remap_ambient_indices(arena: &Arena, exp: Exp, mapping: &[usize]) -> Exp {
    transform(
        arena,
        exp,
        0,
        &mut |e, depth| match super::traversal::Term::Logical(e).bound_index(arena) {
            Some(index) if index >= depth => mapping
                .get(index - depth)
                .filter(|mapped| **mapped != index - depth)
                .map(|mapped| arena.exp_bound(depth + *mapped)),
            _ => None,
        },
    )
}

pub fn remove_unused_ambient_binders(arena: &Arena, exp: Exp, count: usize) -> Option<Exp> {
    if count == 0 {
        return Some(exp);
    }
    let mut depends = false;
    let result = transform(
        arena,
        exp,
        0,
        &mut |e, depth| match super::traversal::Term::Logical(e).bound_index(arena) {
            Some(index) if index >= depth && index < depth + count => {
                depends = true;
                None
            }
            Some(index) if index >= depth + count => Some(arena.exp_bound(index - count)),
            _ => None,
        },
    );
    (!depends).then_some(result)
}

pub fn exp_subst_module_param(
    arena: &Arena,
    exp: Exp,
    parameter: ModuleParamId,
    replacement: Exp,
) -> Exp {
    transform(arena, exp, 0, &mut |e, depth| {
        let matches = matches!(arena.get(e),
            ExpNode::ModuleParam(id) | ExpNode::ReflectedProgramParam(id) if id == parameter);
        matches.then(|| shift_bound_indices(arena, replacement.clone(), depth, 0))
    })
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
    // Rewrite children as well as the node's own identifiers. In particular,
    // reflected cases and parameterized constructors contain further references
    // to the source module, and boxes carry a separate Program syntax tree.
    let original = arena.get(exp.clone());
    let mut node = map_children(original.clone(), |child| {
        remap_all_global_ids(arena, child, definitions, inductives, program_inductives)
    });
    let remap_computation_type = |ty: &mut ComputationType| {
        *ty = crate::raw::program_calculus::remap_computation_type_global_ids(
            arena,
            ty.clone(),
            definitions,
            program_inductives,
        );
    };
    match &mut node {
        ExpNode::DefinedConstant(id) => {
            *id = definitions.get(id).cloned().unwrap_or(*id);
        }
        ExpNode::IndType { indspec, .. }
        | ExpNode::IndCtor { indspec, .. }
        | ExpNode::IndElim { indspec, .. }
        | ExpNode::IndCase { indspec, .. } => {
            *indspec = inductives.get(indspec).cloned().unwrap_or(*indspec);
        }
        ExpNode::ReflectedProgramCase { indspec, .. } => {
            *indspec = program_inductives.get(indspec).cloned().unwrap_or(*indspec);
        }
        ExpNode::BoxType { program_ty } | ExpNode::ForceBox { program_ty, .. } => {
            remap_computation_type(program_ty);
        }
        ExpNode::BoxProgram {
            program_ty,
            program,
        } => {
            remap_computation_type(program_ty);
            *program = crate::raw::program_calculus::remap_computation_global_ids(
                arena,
                program.clone(),
                definitions,
                program_inductives,
                inductives,
            );
        }
        _ => {}
    }
    if node == original {
        exp
    } else {
        arena.alloc(node)
    }
}

fn same_node_shape(arena: &Arena, left: &ExpNode, right: &ExpNode) -> bool {
    match (left, right) {
        (ExpNode::Sort(left), ExpNode::Sort(right)) => left == right,
        (ExpNode::Bound(left), ExpNode::Bound(right)) => left == right,
        (ExpNode::ModuleParam(left), ExpNode::ModuleParam(right)) => left == right,
        (ExpNode::ReflectedProgramParam(left), ExpNode::ReflectedProgramParam(right)) => {
            left == right
        }
        (
            ExpNode::Meta {
                metavariable: left, ..
            },
            ExpNode::Meta {
                metavariable: right,
                ..
            },
        ) => left == right,
        (ExpNode::DefinedConstant(left), ExpNode::DefinedConstant(right)) => left == right,
        (ExpNode::IndType { indspec: left, .. }, ExpNode::IndType { indspec: right, .. })
        | (ExpNode::IndElim { indspec: left, .. }, ExpNode::IndElim { indspec: right, .. })
        | (ExpNode::IndCase { indspec: left, .. }, ExpNode::IndCase { indspec: right, .. }) => {
            left == right
        }
        (
            ExpNode::IndCtor {
                indspec: left_spec,
                idx: left_idx,
                ..
            },
            ExpNode::IndCtor {
                indspec: right_spec,
                idx: right_idx,
                ..
            },
        ) => left_spec == right_spec && left_idx == right_idx,
        (
            ExpNode::ReflectedProgramCase {
                indspec: left_spec,
                branches: left_branches,
                ..
            },
            ExpNode::ReflectedProgramCase {
                indspec: right_spec,
                branches: right_branches,
                ..
            },
        ) => {
            left_spec == right_spec
                && left_branches.len() == right_branches.len()
                && left_branches
                    .iter()
                    .zip(right_branches)
                    .all(|(left, right)| left.binders.len() == right.binders.len())
        }
        (ExpNode::BoxType { program_ty: left }, ExpNode::BoxType { program_ty: right }) => {
            crate::raw::program_calculus::computation_type_is_alpha_eq(
                arena,
                left.clone(),
                right.clone(),
            )
        }
        (
            ExpNode::BoxProgram {
                program_ty: left_ty,
                program: left_program,
                ..
            },
            ExpNode::BoxProgram {
                program_ty: right_ty,
                program: right_program,
                ..
            },
        ) => {
            crate::raw::program_calculus::computation_type_is_alpha_eq(
                arena,
                left_ty.clone(),
                right_ty.clone(),
            ) && crate::raw::program_calculus::computation_is_alpha_eq(
                arena,
                left_program.clone(),
                right_program.clone(),
            )
        }
        (
            ExpNode::ForceBox {
                program_ty: left, ..
            },
            ExpNode::ForceBox {
                program_ty: right, ..
            },
        ) => crate::raw::program_calculus::computation_type_is_alpha_eq(
            arena,
            left.clone(),
            right.clone(),
        ),
        _ => std::mem::discriminant(left) == std::mem::discriminant(right),
    }
}

fn comparison_children(node: &ExpNode, computational: bool) -> SmallVec<[Exp; 8]> {
    let mut children = SmallVec::new();
    macro_rules! add { ($($child:expr),+ $(,)?) => {{ $( children.push($child.clone()); )+ }}; }
    macro_rules! extend {
        ($children:expr) => {{
            children.extend($children.iter().cloned());
        }};
    }

    if computational {
        match node {
            ExpNode::SetRun {
                state_ty,
                result_ty,
                step,
                initial,
                ..
            } => {
                add!(state_ty, result_ty, step, initial);
                return children;
            }
            ExpNode::SetRunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                ..
            } => {
                add!(state_ty, result_ty, step, initial, transition);
                return children;
            }
            ExpNode::BoxProgram { .. } => return children,
            _ => {}
        }
    }

    match node {
        ExpNode::Sort(_)
        | ExpNode::Bound(_)
        | ExpNode::ModuleParam(_)
        | ExpNode::ReflectedProgramParam(_)
        | ExpNode::DefinedConstant(_)
        | ExpNode::BoxType { .. }
        | ExpNode::BoxProgram { .. } => {}
        ExpNode::Meta { spine, .. } => extend!(spine),
        ExpNode::Prod { ty, body, .. } | ExpNode::Lam { ty, body, .. } => add!(ty, body),
        ExpNode::App { func, arg } => add!(func, arg),
        ExpNode::IndType { parameters, .. } | ExpNode::IndCtor { parameters, .. } => {
            extend!(parameters)
        }
        ExpNode::IndElim {
            elim,
            return_type,
            cases,
            ..
        } => {
            add!(elim, return_type);
            extend!(cases);
        }
        ExpNode::IndCase {
            scrutinee,
            return_type,
            branches,
            ..
        } => {
            add!(scrutinee, return_type);
            extend!(branches);
        }
        ExpNode::ReflectedProgramCase {
            scrutinee,
            branches,
            ..
        } => {
            add!(scrutinee);
            children.extend(branches.iter().map(|branch| branch.body.clone()));
        }
        ExpNode::RunStep {
            state_ty,
            result_ty,
        } => add!(state_ty, result_ty),
        ExpNode::Continue {
            state_ty,
            result_ty,
            next,
        } => add!(state_ty, result_ty, next),
        ExpNode::Finish {
            state_ty,
            result_ty,
            output,
        } => add!(state_ty, result_ty, output),
        ExpNode::Acc {
            state_ty,
            result_ty,
            step,
            state,
        } => add!(state_ty, result_ty, step, state),
        ExpNode::RunStepRec {
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee,
        } => add!(
            state_ty,
            result_ty,
            motive,
            on_continue,
            on_finish,
            scrutinee
        ),
        ExpNode::SetRun {
            state_ty,
            result_ty,
            step,
            initial,
            accessibility,
        } => add!(state_ty, result_ty, step, initial, accessibility),
        ExpNode::SetRunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            accessibility,
            transition_equality,
        } => add!(
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            accessibility,
            transition_equality
        ),
        ExpNode::ForceBox { boxed, .. } => add!(boxed),
        ExpNode::BoxApp { function, argument } => add!(function, argument),
        ExpNode::Prove(proof) => match proof {
            Prove::AccIntro {
                state_ty,
                result_ty,
                step,
                state,
                predecessors,
            } => add!(state_ty, result_ty, step, state, predecessors),
            Prove::AccDescent {
                state_ty,
                result_ty,
                step,
                from,
                to,
                accessibility,
                transition,
            } => add!(
                state_ty,
                result_ty,
                step,
                from,
                to,
                accessibility,
                transition
            ),
            Prove::ExistsIntro { element, set } => add!(element, set),
            Prove::SubsetElim {
                element,
                subset,
                superset,
            } => add!(element, subset, superset),
            Prove::IdRefl { element } => add!(element),
            Prove::IdElim {
                left,
                right,
                ty,
                predicate,
                base,
                equality,
                ..
            } => add!(left, right, ty, predicate, base, equality),
            Prove::Axiom(axiom) => match axiom {
                Axiom::SetExt {
                    left,
                    right,
                    left_to_right,
                    right_to_left,
                } => add!(left, right, left_to_right, right_to_left),
                Axiom::FunExt {
                    left,
                    right,
                    pointwise,
                } => add!(left, right, pointwise),
                Axiom::ClassicalIndefiniteChoice {
                    domain,
                    family,
                    inhabited,
                } => add!(domain, family, inhabited),
            },
            Prove::TakeEq {
                func,
                domain,
                codomain,
                element,
                existence,
                uniqueness,
            } => add!(func, domain, codomain, element, existence, uniqueness),
        },
        ExpNode::PowerSet { set } | ExpNode::Exists { set } => add!(set),
        ExpNode::SubSet { set, predicate, .. } => add!(set, predicate),
        ExpNode::Pred {
            superset,
            subset,
            element,
        } => add!(superset, subset, element),
        ExpNode::TypeLift { superset, subset } => add!(superset, subset),
        ExpNode::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => add!(superset, subset, element, proof),
        ExpNode::Equal { left, right } => add!(left, right),
        ExpNode::TakeSet {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => add!(domain, codomain, map, existence, uniqueness),
        ExpNode::TakeProp {
            domain,
            proposition,
            map,
            existence,
        } => add!(domain, proposition, map, existence),
    }
    children
}

fn whnf_with_erasure(env: &CrateEnv, mut exp: Exp, erase_subset_intro: bool) -> Exp {
    loop {
        exp = whnf(env, exp);
        if erase_subset_intro
            && let ExpNode::SubsetIntro { element, .. } = env.arena().get(exp.clone())
        {
            exp = element;
            continue;
        }
        return exp;
    }
}

fn cached_whnf(env: &CrateEnv, exp: Exp, erase_subset_intro: bool, cache: &mut AlphaCache) -> Exp {
    if let Some(result) = cache.whnf.get(&exp) {
        return result.clone();
    }
    let result = whnf_with_erasure(env, exp.clone(), erase_subset_intro);
    cache.whnf.insert(exp, result.clone());
    result
}

#[derive(Default)]
struct AlphaCache {
    whnf: FxHashMap<Exp, Exp>,
    comparisons: FxHashMap<(Exp, Exp, bool, bool), bool>,
}

fn alpha_rec(
    env: &CrateEnv,
    left: Exp,
    right: Exp,
    reduce: bool,
    erase_subset_intro: bool,
    cache: &mut AlphaCache,
) -> bool {
    if left == right {
        return true;
    }
    let key = if left.index() <= right.index() {
        (left.clone(), right.clone(), reduce, erase_subset_intro)
    } else {
        (right.clone(), left.clone(), reduce, erase_subset_intro)
    };
    if let Some(result) = cache.comparisons.get(&key) {
        return *result;
    }
    let result = alpha_rec_uncached(env, left, right, reduce, erase_subset_intro, cache);
    cache.comparisons.insert(key, result);
    result
}

fn alpha_rec_uncached(
    env: &CrateEnv,
    left: Exp,
    right: Exp,
    reduce: bool,
    erase_subset_intro: bool,
    cache: &mut AlphaCache,
) -> bool {
    // Congruent syntax already establishes conversion. In particular, avoid
    // unfolding identical applications of large reflected/library functions.
    // Keep the non-reducing comparison strict (including refinement proofs);
    // any mismatch falls through to the usual reduction/erasure rules.
    if reduce && alpha_rec(env, left.clone(), right.clone(), false, false, cache) {
        return true;
    }
    let (left, right) = if reduce {
        (
            cached_whnf(env, left, erase_subset_intro, cache),
            cached_whnf(env, right, erase_subset_intro, cache),
        )
    } else {
        (left, right)
    };
    if left == right {
        return true;
    }
    let arena = env.arena();
    let (left_children, right_children) = {
        let left_node = arena.borrow_exp(left);
        let right_node = arena.borrow_exp(right);
        if !same_node_shape(arena, &left_node, &right_node) {
            return false;
        }
        (
            comparison_children(&left_node, reduce),
            comparison_children(&right_node, reduce),
        )
    };
    left_children.len() == right_children.len()
        && left_children
            .into_iter()
            .zip(right_children)
            .all(|(a, b)| alpha_rec(env, a, b, reduce, erase_subset_intro, cache))
}

pub fn exp_is_alpha_eq(env: &CrateEnv, left: Exp, right: Exp) -> bool {
    alpha_rec(env, left, right, false, false, &mut AlphaCache::default())
}

pub fn exp_reduce_if_top(env: &CrateEnv, exp: Exp) -> Option<Exp> {
    let arena = env.arena();
    match arena.get(exp.clone()) {
        ExpNode::App { func, arg } => {
            // Refinement introduction is computationally transparent.  In
            // function position, peel it after exposing the function head so
            // that an enclosed lambda can beta-reduce.
            let func_head = whnf_with_erasure(env, func.clone(), true);
            match arena.get(func_head.clone()) {
                ExpNode::Lam { body, .. } => Some(match arena.get(body.clone()) {
                    // The identity body needs neither a walk nor index adjustment.
                    ExpNode::Bound(0) => arg,
                    _ => instantiate(arena, body, arg),
                }),
                _ if func_head != func => Some(arena.alloc(ExpNode::App {
                    func: func_head,
                    arg,
                })),
                _ => None,
            }
        }
        ExpNode::DefinedConstant(id) => match env.definition(id) {
            DefinedConstant::Pts { body, .. } => Some(body.clone()),
            _ => None,
        },
        ExpNode::Pred {
            subset, element, ..
        } => match arena.get(whnf(env, subset)) {
            ExpNode::SubSet { predicate, .. } => Some(instantiate(arena, predicate, element)),
            _ => None,
        },
        ExpNode::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => {
            let reduced = whnf(env, elim.clone());
            let candidate = if reduced == elim {
                exp.clone()
            } else {
                arena.alloc(ExpNode::IndElim {
                    indspec,
                    elim: reduced,
                    return_type,
                    cases,
                })
            };
            crate::raw::inductive::inductive_type_elim_reduce(env, candidate.clone())
                .ok()
                .or((candidate != exp).then_some(candidate))
        }
        ExpNode::IndCase {
            indspec,
            scrutinee,
            return_type,
            branches,
        } => {
            let reduced = whnf(env, scrutinee.clone());
            let (head, fields) = crate::raw::utils::decompose_app(arena, reduced.clone());
            match arena.get(head) {
                ExpNode::IndCtor {
                    indspec: actual,
                    idx,
                    ..
                } if actual == indspec => branches
                    .get(idx)
                    .cloned()
                    .map(|branch| crate::raw::utils::assoc_apply(arena, branch, fields)),
                _ if reduced != scrutinee => Some(arena.alloc(ExpNode::IndCase {
                    indspec,
                    scrutinee: reduced,
                    return_type,
                    branches,
                })),
                _ => None,
            }
        }
        ExpNode::ReflectedProgramCase {
            indspec,
            scrutinee,
            branches,
        } => {
            let reduced = whnf(env, scrutinee.clone());
            let (head, fields) = crate::raw::utils::decompose_app(arena, reduced.clone());
            match arena.get(head) {
                ExpNode::IndCtor {
                    indspec: actual,
                    idx,
                    ..
                } if actual == env.program_inductive(indspec).reflected() => {
                    let branch = branches.get(idx)?;
                    (branch.binders.len() == fields.len())
                        .then(|| instantiate_telescope(arena, branch.body.clone(), &fields))
                }
                _ if reduced != scrutinee => Some(arena.alloc(ExpNode::ReflectedProgramCase {
                    indspec,
                    scrutinee: reduced,
                    branches,
                })),
                _ => None,
            }
        }
        ExpNode::RunStepRec {
            on_continue,
            on_finish,
            scrutinee,
            ..
        } => match arena.get(whnf(env, scrutinee)) {
            ExpNode::Continue { next, .. } => Some(arena.alloc(ExpNode::App {
                func: on_continue,
                arg: next,
            })),
            ExpNode::Finish { output, .. } => Some(arena.alloc(ExpNode::App {
                func: on_finish,
                arg: output,
            })),
            _ => None,
        },
        ExpNode::SetRun {
            state_ty,
            result_ty,
            step,
            initial,
            accessibility,
        } => Some(arena.alloc(ExpNode::SetRunCase {
            state_ty,
            result_ty,
            step: step.clone(),
            initial: initial.clone(),
            transition: arena.alloc(ExpNode::App {
                func: step.clone(),
                arg: initial.clone(),
            }),
            accessibility,
            transition_equality: arena.alloc(ExpNode::Prove(Prove::IdRefl {
                element: arena.alloc(ExpNode::App {
                    func: step,
                    arg: initial,
                }),
            })),
        })),
        ExpNode::SetRunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
            accessibility,
            transition_equality,
            ..
        } => match arena.get(whnf(env, transition)) {
            ExpNode::Continue { next, .. } => Some(arena.alloc(ExpNode::SetRun {
                state_ty: state_ty.clone(),
                result_ty: result_ty.clone(),
                step: step.clone(),
                initial: next.clone(),
                accessibility: arena.alloc(ExpNode::Prove(Prove::AccDescent {
                    state_ty,
                    result_ty,
                    step,
                    from: initial,
                    to: next,
                    accessibility,
                    transition: transition_equality,
                })),
            })),
            ExpNode::Finish { output, .. } => Some(output),
            _ => None,
        },
        ExpNode::BoxProgram {
            program_ty,
            program: term,
        } => crate::raw::program_calculus::reduce_computation_once(env, term).map(|next| {
            arena.alloc(ExpNode::BoxProgram {
                program_ty,
                program: next,
            })
        }),
        ExpNode::ForceBox { program_ty, boxed } => match arena.get(whnf(env, boxed)) {
            ExpNode::BoxProgram {
                program_ty: actual,
                program,
            } if crate::raw::program_calculus::computation_type_is_alpha_eq(
                arena,
                actual.clone(),
                program_ty,
            ) && crate::raw::program_calculus::reduce_computation_once(
                env,
                program.clone(),
            )
            .is_none() =>
            {
                crate::raw::reflection::reflect_computation(env, program).ok()
            }
            _ => None,
        },
        ExpNode::BoxApp { function, argument } => {
            match (
                arena.get(whnf(env, function)),
                arena.get(whnf(env, argument)),
            ) {
                (
                    ExpNode::BoxProgram {
                        program_ty: ft,
                        program: function,
                    },
                    ExpNode::BoxProgram {
                        program_ty: argument_ty,
                        program: argument,
                    },
                ) => match (arena.get(ft), arena.get(argument_ty), arena.get(argument)) {
                    (
                        crate::raw::program::ComputationTypeNode::Function { domain, codomain },
                        crate::raw::program::ComputationTypeNode::Return { value_ty },
                        ComputationTermNode::Return { value: argument },
                    ) if crate::raw::program_calculus::value_type_is_alpha_eq(
                        arena,
                        domain.clone(),
                        value_ty.clone(),
                    ) =>
                    {
                        Some(arena.alloc(ExpNode::BoxProgram {
                            program_ty: codomain,
                            program: arena.alloc(ComputationTermNode::Application {
                                computation: function,
                                value: argument,
                            }),
                        }))
                    }
                    _ => None,
                },
                _ => None,
            }
        }
        _ => None,
    }
}

pub fn whnf(env: &CrateEnv, mut exp: Exp) -> Exp {
    if let Some(result) = env.whnf_cache.borrow().get(&exp) {
        return result.clone();
    }
    let original = exp.clone();
    while let Some(next) = exp_reduce_if_top(env, exp.clone()) {
        tracing::trace!(target: "ref_type::reduction", before = %crate::raw::printing::format_exp(env, exp.clone()), after = %crate::raw::printing::format_exp(env, next.clone()), "weak-head reduction step");
        if next == exp {
            break;
        }
        exp = next;
    }
    env.whnf_cache.borrow_mut().insert(original, exp.clone());
    exp
}

pub fn reduce_one(env: &CrateEnv, exp: Exp) -> Option<Exp> {
    if let Some(next) = exp_reduce_if_top(env, exp.clone()) {
        return Some(next);
    }
    let node = env.arena().get(exp);
    let mut changed = false;
    let mapped = map_computational_children(node, |child| {
        if changed {
            child
        } else if let Some(next) = reduce_one(env, child.clone()) {
            changed = true;
            next
        } else {
            child
        }
    });
    changed.then(|| env.arena().alloc(mapped))
}

pub fn normalize(env: &CrateEnv, exp: Exp) -> Exp {
    let span = tracing::debug_span!(target: "ref_type::reduction", "normalize", term = %crate::raw::printing::format_exp(env, exp.clone()));
    let _entered = span.enter();
    let result = normalize_with_cache(env, exp, &mut FxHashMap::default());
    tracing::debug!(target: "ref_type::reduction", result = %crate::raw::printing::format_exp(env, result.clone()), "normalization finished");
    result
}

fn normalize_with_cache(env: &CrateEnv, exp: Exp, cache: &mut FxHashMap<Exp, Exp>) -> Exp {
    if let Some(normal) = cache.get(&exp) {
        return normal.clone();
    }
    let arena = env.arena();
    let head = whnf(env, exp.clone());
    let node = arena.get(head.clone());
    let mut changed = false;
    let normalized = map_computational_children(node, |child| {
        let result = normalize_with_cache(env, child.clone(), cache);
        changed |= result != child;
        result
    });
    let candidate = if changed {
        arena.alloc(normalized)
    } else {
        head
    };
    let reduced = whnf(env, candidate.clone());
    let result = if reduced == candidate {
        candidate
    } else {
        normalize_with_cache(env, reduced, cache)
    };
    cache.insert(exp, result.clone());
    result
}

pub fn convertible(env: &CrateEnv, left: Exp, right: Exp) -> bool {
    let result = alpha_rec(
        env,
        left.clone(),
        right.clone(),
        true,
        false,
        &mut AlphaCache::default(),
    );
    tracing::trace!(target: "ref_type::conversion", left = %crate::raw::printing::format_exp(env, left), right = %crate::raw::printing::format_exp(env, right), result, "conversion compared");
    result
}

pub fn erased_convertible(env: &CrateEnv, left: Exp, right: Exp) -> bool {
    alpha_rec(env, left, right, true, true, &mut AlphaCache::default())
}

pub(crate) fn type_head_normal(env: &CrateEnv, ty: Exp) -> Exp {
    whnf_with_erasure(env, ty, true)
}

pub(crate) fn expose_product(env: &CrateEnv, ty: Exp) -> Option<(SymbolId, Exp, Exp)> {
    let arena = env.arena();
    let mut current = type_head_normal(env, ty);
    loop {
        match arena.get(current) {
            ExpNode::Prod { var, ty, body } => return Some((var, ty, body)),
            ExpNode::TypeLift { superset, .. } => current = type_head_normal(env, superset),
            _ => return None,
        }
    }
}

pub(crate) fn base_carrier(env: &CrateEnv, ty: Exp) -> Exp {
    let arena = env.arena();
    let mut current = type_head_normal(env, ty);
    loop {
        match arena.get(current.clone()) {
            ExpNode::TypeLift { superset, .. } => current = type_head_normal(env, superset),
            _ => return current,
        }
    }
}

pub fn common_ambient_carrier(env: &CrateEnv, left: Exp, right: Exp) -> Option<Exp> {
    let carrier = base_carrier(env, left);
    erased_convertible(env, carrier.clone(), base_carrier(env, right)).then_some(carrier)
}

pub fn can_weaken_to(env: &CrateEnv, inferred: Exp, expected: Exp) -> bool {
    if erased_convertible(env, inferred.clone(), expected.clone()) {
        return true;
    }
    let arena = env.arena();
    match (
        arena.get(type_head_normal(env, inferred)),
        arena.get(type_head_normal(env, expected.clone())),
    ) {
        (ExpNode::TypeLift { superset, .. }, _) => can_weaken_to(env, superset, expected),
        (ExpNode::Prod { ty: a, body: b, .. }, ExpNode::Prod { ty: c, body: d, .. })
            if erased_convertible(env, a.clone(), c.clone()) =>
        {
            can_weaken_to(env, b, d)
        }
        _ => false,
    }
}
