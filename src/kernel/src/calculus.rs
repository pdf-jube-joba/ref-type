//! Structural operations and reduction for Set/Prop expressions.

use crate::{
    environment::{CrateEnv, DefinedConstant},
    exp::*,
    ids::{DefId, InductiveId, ModuleParamId, ProgramInductiveId, SymbolId},
    program::{ComputationNode, Program, ProgramType},
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
        | ExpNode::DefinedConstant(_) => {}
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
        ExpNode::Proof { proposition } => one!(proposition),
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
        } => one!(state_ty, result_ty, step, initial),
        ExpNode::SetRunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition,
        } => one!(state_ty, result_ty, step, initial, transition),
        ExpNode::BoxType { .. } | ExpNode::BoxProgram { .. } => {}
        ExpNode::ForceBox { boxed, .. } => one!(boxed),
        ExpNode::BoxApp { function, argument } => one!(function, argument),
        ExpNode::AccIntro {
            state_ty,
            result_ty,
            step,
            state,
            predecessors,
        } => one!(state_ty, result_ty, step, state, predecessors),
        ExpNode::AccDescent {
            state_ty,
            result_ty,
            step,
            from,
            to,
            accessibility,
            transition,
        } => one!(
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
        ExpNode::ExistsIntro { element, set } => one!(element, set),
        ExpNode::SubsetElim {
            element,
            subset,
            superset,
        } => one!(element, subset, superset),
        ExpNode::IdRefl { element } => one!(element),
        ExpNode::IdElim {
            left,
            right,
            ty,
            predicate,
            base,
            equality,
            ..
        } => one!(left, right, ty, predicate, base, equality),
        ExpNode::AxiomSetExt {
            left,
            right,
            left_to_right,
            right_to_left,
        } => one!(left, right, left_to_right, right_to_left),
        ExpNode::AxiomFunExt {
            left,
            right,
            pointwise,
        } => one!(left, right, pointwise),
        ExpNode::AxiomClassicalIndefiniteChoice {
            domain,
            family,
            inhabited,
        } => one!(domain, family, inhabited),
        ExpNode::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => one!(func, domain, codomain, element, existence, uniqueness),
    }
    node
}

fn transform<F>(arena: &Arena, exp: Exp, depth: usize, operation: &mut F) -> Exp
where
    F: FnMut(&ExpNode, usize) -> Option<Exp>,
{
    let node = arena.get(exp);
    if let Some(replacement) = operation(&node, depth) {
        return replacement;
    }
    let mut changed = false;
    let mut child = |value: Exp, child_depth: usize| {
        let result = transform(arena, value, child_depth, operation);
        changed |= result != value;
        result
    };
    let transformed = match node {
        ExpNode::Sort(_)
        | ExpNode::Bound(_)
        | ExpNode::ModuleParam(_)
        | ExpNode::ReflectedProgramParam(_)
        | ExpNode::DefinedConstant(_) => return exp,
        ExpNode::Prod { var, ty, body } => ExpNode::Prod {
            var,
            ty: child(ty, depth),
            body: child(body, depth + 1),
        },
        ExpNode::Lam { var, ty, body } => ExpNode::Lam {
            var,
            ty: child(ty, depth),
            body: child(body, depth + 1),
        },
        ExpNode::SubSet {
            var,
            set,
            predicate,
        } => ExpNode::SubSet {
            var,
            set: child(set, depth),
            predicate: child(predicate, depth + 1),
        },
        ExpNode::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
            base,
            equality,
        } => ExpNode::IdElim {
            left: child(left, depth),
            right: child(right, depth),
            ty: child(ty, depth),
            var,
            predicate: child(predicate, depth + 1),
            base: child(base, depth),
            equality: child(equality, depth),
        },
        ExpNode::ReflectedProgramCase {
            indspec,
            scrutinee,
            branches,
        } => ExpNode::ReflectedProgramCase {
            indspec,
            scrutinee: child(scrutinee, depth),
            branches: branches
                .into_iter()
                .map(|branch| ReflectedProgramCaseBranch {
                    body: child(branch.body, depth + branch.binders.len()),
                    binders: branch.binders,
                })
                .collect(),
        },
        other => map_children(other, |value| child(value, depth)),
    };
    if changed {
        arena.alloc(transformed)
    } else {
        exp
    }
}

fn direct_children(node: ExpNode) -> Vec<Exp> {
    let mut result = Vec::new();
    let _ = map_children(node, |child| {
        result.push(child);
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
            ExpNode::IdElim {
                left,
                right,
                ty,
                predicate,
                base,
                equality,
                ..
            } => {
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

pub fn exp_contains_module_param(env: &CrateEnv, exp: Exp, parameter: ModuleParamId) -> bool {
    match env.arena().get(exp) {
        ExpNode::ModuleParam(id) | ExpNode::ReflectedProgramParam(id) => id == parameter,
        ExpNode::DefinedConstant(id) => match env.definition(id) {
            DefinedConstant::Pts { ty, body } => {
                exp_contains_module_param(env, *ty, parameter)
                    || exp_contains_module_param(env, *body, parameter)
            }
            _ => false,
        },
        node => direct_children(node)
            .into_iter()
            .any(|e| exp_contains_module_param(env, e, parameter)),
    }
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
        node => direct_children(node)
            .into_iter()
            .any(|e| exp_contains_inductive(arena, e, inductive)),
    }
}

pub fn shift_bound_indices(arena: &Arena, exp: Exp, amount: usize, cutoff: usize) -> Exp {
    transform(arena, exp, 0, &mut |node, depth| match node {
        ExpNode::Bound(index) if *index >= cutoff + depth => Some(arena.exp_bound(index + amount)),
        _ => None,
    })
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
    transform(arena, exp, 0, &mut |node, depth| match node {
        ExpNode::Bound(index) if *index >= depth + inner => {
            let telescope_index = *index - depth - inner;
            if telescope_index < arguments.len() {
                Some(shift_bound_indices(
                    arena,
                    arguments[arguments.len() - 1 - telescope_index],
                    depth + inner,
                    0,
                ))
            } else {
                Some(arena.exp_bound(index - arguments.len()))
            }
        }
        _ => None,
    })
}

pub fn remap_ambient_indices(arena: &Arena, exp: Exp, mapping: &[usize]) -> Exp {
    transform(arena, exp, 0, &mut |node, depth| match node {
        ExpNode::Bound(index) if *index >= depth => mapping
            .get(*index - depth)
            .filter(|mapped| **mapped != *index - depth)
            .map(|mapped| arena.exp_bound(depth + *mapped)),
        _ => None,
    })
}

pub fn remove_unused_ambient_binders(arena: &Arena, exp: Exp, count: usize) -> Option<Exp> {
    if count == 0 {
        return Some(exp);
    }
    let mut depends = false;
    let result = transform(arena, exp, 0, &mut |node, depth| match node {
        ExpNode::Bound(index) if *index >= depth && *index < depth + count => {
            depends = true;
            None
        }
        ExpNode::Bound(index) if *index >= depth + count => Some(arena.exp_bound(index - count)),
        _ => None,
    });
    (!depends).then_some(result)
}

pub fn exp_subst_module_param(
    arena: &Arena,
    exp: Exp,
    parameter: ModuleParamId,
    replacement: Exp,
) -> Exp {
    transform(arena, exp, 0, &mut |node, depth| match node {
        ExpNode::ModuleParam(id) if *id == parameter => {
            Some(shift_bound_indices(arena, replacement, depth, 0))
        }
        _ => None,
    })
}

pub fn exp_subst_map(arena: &Arena, mut exp: Exp, substitutions: &[(ModuleParamId, Exp)]) -> Exp {
    for (parameter, replacement) in substitutions {
        exp = exp_subst_module_param(arena, exp, *parameter, *replacement);
    }
    exp
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
    let original = arena.get(exp);
    let mut node = map_children(original.clone(), |child| {
        remap_all_global_ids(arena, child, definitions, inductives, program_inductives)
    });
    let remap_program_type = |ty: &mut ProgramType| {
        *ty = match *ty {
            ProgramType::Value(value) => {
                ProgramType::Value(crate::program_calculus::remap_value_type_global_ids(
                    arena,
                    value,
                    definitions,
                    program_inductives,
                ))
            }
            ProgramType::Computation(computation) => ProgramType::Computation(
                crate::program_calculus::remap_computation_type_global_ids(
                    arena,
                    computation,
                    definitions,
                    program_inductives,
                ),
            ),
        };
    };
    match &mut node {
        ExpNode::DefinedConstant(id) => {
            *id = definitions.get(id).copied().unwrap_or(*id);
        }
        ExpNode::IndType { indspec, .. }
        | ExpNode::IndCtor { indspec, .. }
        | ExpNode::IndElim { indspec, .. } => {
            *indspec = inductives.get(indspec).copied().unwrap_or(*indspec);
        }
        ExpNode::ReflectedProgramCase { indspec, .. } => {
            *indspec = program_inductives.get(indspec).copied().unwrap_or(*indspec);
        }
        ExpNode::BoxType { program_ty } | ExpNode::ForceBox { program_ty, .. } => {
            remap_program_type(program_ty);
        }
        ExpNode::BoxProgram {
            program_ty,
            program,
        } => {
            remap_program_type(program_ty);
            *program = match *program {
                Program::Value(value) => {
                    Program::Value(crate::program_calculus::remap_value_global_ids(
                        arena,
                        value,
                        definitions,
                        program_inductives,
                    ))
                }
                Program::Computation(computation) => {
                    Program::Computation(crate::program_calculus::remap_computation_global_ids(
                        arena,
                        computation,
                        definitions,
                        program_inductives,
                    ))
                }
            };
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
        | (ExpNode::IndElim { indspec: left, .. }, ExpNode::IndElim { indspec: right, .. }) => {
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
            crate::program_calculus::program_type_is_alpha_eq(arena, *left, *right)
        }
        (
            ExpNode::BoxProgram {
                program_ty: left_ty,
                program: left_program,
            },
            ExpNode::BoxProgram {
                program_ty: right_ty,
                program: right_program,
            },
        ) => {
            crate::program_calculus::program_type_is_alpha_eq(arena, *left_ty, *right_ty)
                && crate::program_calculus::program_is_alpha_eq(
                    arena,
                    *left_program,
                    *right_program,
                )
        }
        (
            ExpNode::ForceBox {
                program_ty: left, ..
            },
            ExpNode::ForceBox {
                program_ty: right, ..
            },
        ) => crate::program_calculus::program_type_is_alpha_eq(arena, *left, *right),
        _ => std::mem::discriminant(left) == std::mem::discriminant(right),
    }
}

fn whnf_with_erasure(env: &CrateEnv, mut exp: Exp, erase_subset_intro: bool) -> Exp {
    loop {
        if erase_subset_intro && let ExpNode::SubsetIntro { element, .. } = env.arena().get(exp) {
            exp = element;
            continue;
        }
        let Some(next) = exp_reduce_if_top(env, exp) else {
            return exp;
        };
        if next == exp {
            return exp;
        }
        exp = next;
    }
}

fn cached_whnf(
    env: &CrateEnv,
    exp: Exp,
    erase_subset_intro: bool,
    cache: &mut HashMap<Exp, Exp>,
) -> Exp {
    if let Some(result) = cache.get(&exp) {
        return *result;
    }
    let result = whnf_with_erasure(env, exp, erase_subset_intro);
    cache.insert(exp, result);
    result
}

fn alpha_rec(
    env: &CrateEnv,
    left: Exp,
    right: Exp,
    reduce: bool,
    erase_subset_intro: bool,
    cache: &mut HashMap<Exp, Exp>,
) -> bool {
    if left == right {
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
    let left_node = arena.get(left);
    let right_node = arena.get(right);
    if !same_node_shape(arena, &left_node, &right_node) {
        return false;
    }
    let l = direct_children(left_node);
    let r = direct_children(right_node);
    l.len() == r.len()
        && l.into_iter()
            .zip(r)
            .all(|(a, b)| alpha_rec(env, a, b, reduce, erase_subset_intro, cache))
}

pub fn exp_is_alpha_eq(env: &CrateEnv, left: Exp, right: Exp) -> bool {
    alpha_rec(env, left, right, false, false, &mut HashMap::new())
}

pub fn exp_reduce_if_top(env: &CrateEnv, exp: Exp) -> Option<Exp> {
    let arena = env.arena();
    match arena.get(exp) {
        ExpNode::App { func, arg } => {
            let func_head = whnf(env, func);
            match arena.get(func_head) {
                ExpNode::Lam { body, .. } => Some(instantiate(arena, body, arg)),
                _ if func_head != func => Some(arena.alloc(ExpNode::App {
                    func: func_head,
                    arg,
                })),
                _ => None,
            }
        }
        ExpNode::DefinedConstant(id) => match env.definition(id) {
            DefinedConstant::Pts { body, .. } => Some(*body),
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
            let reduced = whnf(env, elim);
            let candidate = if reduced == elim {
                exp
            } else {
                arena.alloc(ExpNode::IndElim {
                    indspec,
                    elim: reduced,
                    return_type,
                    cases,
                })
            };
            crate::inductive::inductive_type_elim_reduce(env, candidate)
                .ok()
                .or((candidate != exp).then_some(candidate))
        }
        ExpNode::ReflectedProgramCase {
            indspec,
            scrutinee,
            branches,
        } => {
            let reduced = whnf(env, scrutinee);
            let (head, fields) = crate::utils::decompose_app(arena, reduced);
            match arena.get(head) {
                ExpNode::IndCtor {
                    indspec: actual,
                    idx,
                    ..
                } if actual == env.program_inductive(indspec).reflected() => {
                    let branch = branches.get(idx)?;
                    (branch.binders.len() == fields.len())
                        .then(|| instantiate_telescope(arena, branch.body, &fields))
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
        } => Some(arena.alloc(ExpNode::SetRunCase {
            state_ty,
            result_ty,
            step,
            initial,
            transition: arena.alloc(ExpNode::App {
                func: step,
                arg: initial,
            }),
        })),
        ExpNode::SetRunCase {
            state_ty,
            result_ty,
            step,
            transition,
            ..
        } => match arena.get(whnf(env, transition)) {
            ExpNode::Continue { next, .. } => Some(arena.alloc(ExpNode::SetRun {
                state_ty,
                result_ty,
                step,
                initial: next,
            })),
            ExpNode::Finish { output, .. } => Some(output),
            _ => None,
        },
        ExpNode::BoxProgram {
            program_ty,
            program: Program::Computation(term),
        } => crate::program_calculus::reduce_computation_once(env, term).map(|next| {
            arena.alloc(ExpNode::BoxProgram {
                program_ty,
                program: Program::Computation(next),
            })
        }),
        ExpNode::ForceBox { program_ty, boxed } => match arena.get(whnf(env, boxed)) {
            ExpNode::BoxProgram {
                program_ty: actual,
                program,
            } if crate::program_calculus::program_type_is_alpha_eq(arena, actual, program_ty)
                && match program {
                    Program::Computation(c) => {
                        crate::program_calculus::reduce_computation_once(env, c).is_none()
                    }
                    Program::Value(_) => true,
                } =>
            {
                crate::reflection::reflect_program(env, &Vec::new(), program).ok()
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
                        program_ty: ProgramType::Computation(ft),
                        program: Program::Computation(function),
                    },
                    ExpNode::BoxProgram {
                        program_ty: ProgramType::Value(argument_ty),
                        program: Program::Value(argument),
                    },
                ) => match arena.get(ft) {
                    crate::program::ComputationTypeNode::Function { domain, codomain }
                        if crate::program_calculus::value_type_is_alpha_eq(
                            arena,
                            domain,
                            argument_ty,
                        ) =>
                    {
                        Some(arena.alloc(ExpNode::BoxProgram {
                            program_ty: ProgramType::Computation(codomain),
                            program: Program::Computation(arena.alloc(
                                ComputationNode::Application {
                                    computation: function,
                                    value: argument,
                                },
                            )),
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
    while let Some(next) = exp_reduce_if_top(env, exp) {
        if next == exp {
            break;
        }
        exp = next;
    }
    exp
}
pub fn reduce_one(env: &CrateEnv, exp: Exp) -> Option<Exp> {
    if let Some(next) = exp_reduce_if_top(env, exp) {
        return Some(next);
    }
    let node = env.arena().get(exp);
    let mut changed = false;
    let mapped = map_children(node, |child| {
        if changed {
            child
        } else if let Some(next) = reduce_one(env, child) {
            changed = true;
            next
        } else {
            child
        }
    });
    changed.then(|| env.arena().alloc(mapped))
}
pub fn normalize(env: &CrateEnv, exp: Exp) -> Exp {
    normalize_with_cache(env, exp, &mut HashMap::new())
}

fn normalize_with_cache(env: &CrateEnv, exp: Exp, cache: &mut HashMap<Exp, Exp>) -> Exp {
    if let Some(normal) = cache.get(&exp) {
        return *normal;
    }
    let arena = env.arena();
    let head = whnf(env, exp);
    let node = arena.get(head);
    let mut changed = false;
    let normalized = map_children(node, |child| {
        let result = normalize_with_cache(env, child, cache);
        changed |= result != child;
        result
    });
    let candidate = if changed {
        arena.alloc(normalized)
    } else {
        head
    };
    let reduced = whnf(env, candidate);
    let result = if reduced == candidate {
        candidate
    } else {
        normalize_with_cache(env, reduced, cache)
    };
    cache.insert(exp, result);
    result
}
pub fn convertible(env: &CrateEnv, left: Exp, right: Exp) -> bool {
    alpha_rec(env, left, right, true, false, &mut HashMap::new())
}

pub fn erase(env: &CrateEnv, exp: Exp) -> Exp {
    match env.arena().get(exp) {
        ExpNode::SubsetIntro { element, .. } => erase(env, element),
        ExpNode::DefinedConstant(definition) => match env.definition(definition) {
            DefinedConstant::Pts { body, .. } => erase(env, *body),
            _ => exp,
        },
        node => {
            let mut changed = false;
            let erased = map_children(node, |child| {
                let result = erase(env, child);
                changed |= result != child;
                result
            });
            if changed {
                env.arena().alloc(erased)
            } else {
                exp
            }
        }
    }
}
pub fn erased_convertible(env: &CrateEnv, left: Exp, right: Exp) -> bool {
    alpha_rec(env, left, right, true, true, &mut HashMap::new())
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
        match arena.get(current) {
            ExpNode::TypeLift { superset, .. } => current = type_head_normal(env, superset),
            _ => return current,
        }
    }
}
pub fn common_ambient_carrier(env: &CrateEnv, left: Exp, right: Exp) -> Option<Exp> {
    let carrier = base_carrier(env, left);
    erased_convertible(env, carrier, base_carrier(env, right)).then_some(carrier)
}
pub fn can_weaken_to(env: &CrateEnv, inferred: Exp, expected: Exp) -> bool {
    if erased_convertible(env, inferred, expected) {
        return true;
    }
    let arena = env.arena();
    match (
        arena.get(type_head_normal(env, inferred)),
        arena.get(type_head_normal(env, expected)),
    ) {
        (ExpNode::TypeLift { superset, .. }, _) => can_weaken_to(env, superset, expected),
        (ExpNode::Prod { ty: a, body: b, .. }, ExpNode::Prod { ty: c, body: d, .. })
            if erased_convertible(env, a, c) =>
        {
            can_weaken_to(env, b, d)
        }
        _ => false,
    }
}
