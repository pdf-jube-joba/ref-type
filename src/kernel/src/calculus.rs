use crate::environment::CrateEnv;
use crate::ids::{DefId, InductiveId, ModuleParamId, SymbolId};
use crate::inductive::inductive_type_elim_reduce;
use std::collections::HashMap;

use super::exp::*;

pub fn exp_contains_module_param(env: &CrateEnv, exp: Exp, parameter: ModuleParamId) -> bool {
    let arena = env.arena();
    match arena.get(exp) {
        Node::Sort(_) | Node::Bound(_) => false,
        Node::ModuleParam(candidate) => candidate == parameter,
        Node::Prod { ty, body, .. } | Node::Lam { ty, body, .. } => {
            exp_contains_module_param(env, ty, parameter)
                || exp_contains_module_param(env, body, parameter)
        }
        Node::App { func, arg } => {
            exp_contains_module_param(env, func, parameter)
                || exp_contains_module_param(env, arg, parameter)
        }
        Node::DefinedConstant(definition) => {
            let definition = env.definition(definition);
            exp_contains_module_param(env, definition.ty, parameter)
                || exp_contains_module_param(env, definition.body, parameter)
        }
        Node::IndType { parameters, .. } | Node::IndCtor { parameters, .. } => parameters
            .into_iter()
            .any(|argument| exp_contains_module_param(env, argument, parameter)),
        Node::IndElim {
            elim,
            return_type,
            cases,
            ..
        } => {
            exp_contains_module_param(env, elim, parameter)
                || exp_contains_module_param(env, return_type, parameter)
                || cases
                    .into_iter()
                    .any(|case| exp_contains_module_param(env, case, parameter))
        }
        Node::PowerSet { set } | Node::Exists { set } | Node::IdRefl { element: set } => {
            exp_contains_module_param(env, set, parameter)
        }
        Node::SubSet { set, predicate, .. } => {
            exp_contains_module_param(env, set, parameter)
                || exp_contains_module_param(env, predicate, parameter)
        }
        Node::Pred {
            superset,
            subset,
            element,
        }
        | Node::SubsetElim {
            superset,
            subset,
            element,
        } => [superset, subset, element]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::TypeLift { superset, subset }
        | Node::Equal {
            left: superset,
            right: subset,
        } => {
            exp_contains_module_param(env, superset, parameter)
                || exp_contains_module_param(env, subset, parameter)
        }
        Node::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        }
        | Node::TakeProp {
            domain: superset,
            proposition: subset,
            map: element,
            existence: proof,
        } => [superset, subset, element, proof]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::TakeSet {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => [domain, codomain, map, existence, uniqueness]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::ExistsIntro { element, set } => {
            exp_contains_module_param(env, element, parameter)
                || exp_contains_module_param(env, set, parameter)
        }
        Node::IdElim {
            left,
            right,
            ty,
            predicate,
            base,
            equality,
            ..
        } => [left, right, ty, predicate, base, equality]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
        Node::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => [func, domain, codomain, element, existence, uniqueness]
            .into_iter()
            .any(|child| exp_contains_module_param(env, child, parameter)),
    }
}

pub fn exp_contains_inductive(arena: &Arena, exp: Exp, inductive: InductiveId) -> bool {
    fn contains(arena: &Arena, exp: Exp, inductive: InductiveId) -> bool {
        let node = arena.get(exp);
        if matches!(
            node,
            Node::IndType { indspec, .. }
                | Node::IndCtor { indspec, .. }
                | Node::IndElim { indspec, .. }
                if indspec == inductive
        ) {
            return true;
        }
        let mut found = false;
        let _ = map_children(node, |child| {
            found |= contains(arena, child, inductive);
            child
        });
        found
    }

    contains(arena, exp, inductive)
}

#[derive(Clone, Copy)]
struct EqualityMode {
    proof_irrelevant: bool,
    reduce_to_whnf: bool,
    erase_subset_intro: bool,
}

fn is_alpha_eq_rec(env: &CrateEnv, left: Exp, right: Exp, mode: EqualityMode) -> bool {
    let arena = env.arena();
    let left = if mode.reduce_to_whnf {
        exp_whnf_with_mode(env, left, mode.erase_subset_intro)
    } else {
        left
    };
    let right = if mode.reduce_to_whnf {
        exp_whnf_with_mode(env, right, mode.erase_subset_intro)
    } else {
        right
    };
    if left == right {
        return true;
    }

    match (arena.get(left), arena.get(right)) {
        (Node::Sort(left), Node::Sort(right)) => left == right,
        (Node::Bound(left), Node::Bound(right)) => left == right,
        (Node::ModuleParam(left), Node::ModuleParam(right)) => left == right,
        (
            Node::Prod {
                var: left_var,
                ty: left_ty,
                body: left_body,
            },
            Node::Prod {
                var: right_var,
                ty: right_ty,
                body: right_body,
            },
        )
        | (
            Node::Lam {
                var: left_var,
                ty: left_ty,
                body: left_body,
            },
            Node::Lam {
                var: right_var,
                ty: right_ty,
                body: right_body,
            },
        ) => {
            let _ = (left_var, right_var);
            is_alpha_eq_rec(env, left_ty, right_ty, mode)
                && is_alpha_eq_rec(env, left_body, right_body, mode)
        }
        (
            Node::App {
                func: left_func,
                arg: left_arg,
            },
            Node::App {
                func: right_func,
                arg: right_arg,
            },
        ) => {
            is_alpha_eq_rec(env, left_func, right_func, mode)
                && is_alpha_eq_rec(env, left_arg, right_arg, mode)
        }
        (Node::DefinedConstant(left), Node::DefinedConstant(right)) => left == right,
        (
            Node::IndType {
                indspec: left_spec,
                parameters: left_parameters,
            },
            Node::IndType {
                indspec: right_spec,
                parameters: right_parameters,
            },
        ) => left_spec == right_spec && eq_slices(env, &left_parameters, &right_parameters, mode),
        (
            Node::IndCtor {
                indspec: left_spec,
                parameters: left_parameters,
                idx: left_idx,
            },
            Node::IndCtor {
                indspec: right_spec,
                parameters: right_parameters,
                idx: right_idx,
            },
        ) => {
            left_idx == right_idx
                && left_spec == right_spec
                && eq_slices(env, &left_parameters, &right_parameters, mode)
        }
        (
            Node::IndElim {
                indspec: left_spec,
                elim: left_elim,
                return_type: left_return,
                cases: left_cases,
            },
            Node::IndElim {
                indspec: right_spec,
                elim: right_elim,
                return_type: right_return,
                cases: right_cases,
            },
        ) => {
            left_spec == right_spec
                && is_alpha_eq_rec(env, left_elim, right_elim, mode)
                && is_alpha_eq_rec(env, left_return, right_return, mode)
                && eq_slices(env, &left_cases, &right_cases, mode)
        }
        (
            Node::SubsetIntro {
                superset: left_superset,
                subset: left_subset,
                element: left_element,
                proof: left_proof,
            },
            Node::SubsetIntro {
                superset: right_superset,
                subset: right_subset,
                element: right_element,
                proof: right_proof,
            },
        ) => {
            is_alpha_eq_rec(env, left_superset, right_superset, mode)
                && is_alpha_eq_rec(env, left_subset, right_subset, mode)
                && is_alpha_eq_rec(env, left_element, right_element, mode)
                && (mode.proof_irrelevant || is_alpha_eq_rec(env, left_proof, right_proof, mode))
        }
        (Node::PowerSet { set: left }, Node::PowerSet { set: right })
        | (Node::Exists { set: left }, Node::Exists { set: right })
        | (Node::IdRefl { element: left }, Node::IdRefl { element: right }) => {
            is_alpha_eq_rec(env, left, right, mode)
        }
        (
            Node::SubSet {
                var: left_var,
                set: left_set,
                predicate: left_predicate,
            },
            Node::SubSet {
                var: right_var,
                set: right_set,
                predicate: right_predicate,
            },
        ) => {
            let _ = (left_var, right_var);
            is_alpha_eq_rec(env, left_set, right_set, mode)
                && is_alpha_eq_rec(env, left_predicate, right_predicate, mode)
        }
        (
            Node::Pred {
                superset: left_superset,
                subset: left_subset,
                element: left_element,
            },
            Node::Pred {
                superset: right_superset,
                subset: right_subset,
                element: right_element,
            },
        )
        | (
            Node::SubsetElim {
                superset: left_superset,
                subset: left_subset,
                element: left_element,
            },
            Node::SubsetElim {
                superset: right_superset,
                subset: right_subset,
                element: right_element,
            },
        ) => {
            is_alpha_eq_rec(env, left_superset, right_superset, mode)
                && is_alpha_eq_rec(env, left_subset, right_subset, mode)
                && is_alpha_eq_rec(env, left_element, right_element, mode)
        }
        (
            Node::TypeLift {
                superset: left_first,
                subset: left_second,
            },
            Node::TypeLift {
                superset: right_first,
                subset: right_second,
            },
        )
        | (
            Node::Equal {
                left: left_first,
                right: left_second,
            },
            Node::Equal {
                left: right_first,
                right: right_second,
            },
        )
        | (
            Node::ExistsIntro {
                element: left_first,
                set: left_second,
            },
            Node::ExistsIntro {
                element: right_first,
                set: right_second,
            },
        ) => {
            is_alpha_eq_rec(env, left_first, right_first, mode)
                && is_alpha_eq_rec(env, left_second, right_second, mode)
        }
        (
            Node::TakeSet {
                domain: left_domain,
                codomain: left_codomain,
                map: left_map,
                existence: left_existence,
                uniqueness: left_uniqueness,
            },
            Node::TakeSet {
                domain: right_domain,
                codomain: right_codomain,
                map: right_map,
                existence: right_existence,
                uniqueness: right_uniqueness,
            },
        ) => {
            is_alpha_eq_rec(env, left_domain, right_domain, mode)
                && is_alpha_eq_rec(env, left_codomain, right_codomain, mode)
                && is_alpha_eq_rec(env, left_map, right_map, mode)
                && (mode.proof_irrelevant
                    || (is_alpha_eq_rec(env, left_existence, right_existence, mode)
                        && is_alpha_eq_rec(env, left_uniqueness, right_uniqueness, mode)))
        }
        (
            Node::TakeProp {
                domain: left_domain,
                proposition: left_proposition,
                map: left_map,
                existence: left_existence,
            },
            Node::TakeProp {
                domain: right_domain,
                proposition: right_proposition,
                map: right_map,
                existence: right_existence,
            },
        ) => {
            is_alpha_eq_rec(env, left_proposition, right_proposition, mode)
                && (mode.proof_irrelevant
                    || (is_alpha_eq_rec(env, left_domain, right_domain, mode)
                        && is_alpha_eq_rec(env, left_map, right_map, mode)
                        && is_alpha_eq_rec(env, left_existence, right_existence, mode)))
        }
        (
            Node::IdElim {
                left: left_left,
                right: left_right,
                ty: left_ty,
                var: left_var,
                predicate: left_predicate,
                base: left_base,
                equality: left_equality,
                ..
            },
            Node::IdElim {
                left: right_left,
                right: right_right,
                ty: right_ty,
                var: right_var,
                predicate: right_predicate,
                base: right_base,
                equality: right_equality,
                ..
            },
        ) => {
            let _ = (left_var, right_var);
            eq_slices(
                env,
                &[
                    left_left,
                    left_right,
                    left_ty,
                    left_predicate,
                    left_base,
                    left_equality,
                ],
                &[
                    right_left,
                    right_right,
                    right_ty,
                    right_predicate,
                    right_base,
                    right_equality,
                ],
                mode,
            )
        }
        (
            Node::TakeEq {
                func: left_func,
                domain: left_domain,
                codomain: left_codomain,
                element: left_element,
                existence: left_existence,
                uniqueness: left_uniqueness,
            },
            Node::TakeEq {
                func: right_func,
                domain: right_domain,
                codomain: right_codomain,
                element: right_element,
                existence: right_existence,
                uniqueness: right_uniqueness,
            },
        ) => {
            eq_slices(
                env,
                &[left_func, left_domain, left_codomain, left_element],
                &[right_func, right_domain, right_codomain, right_element],
                mode,
            ) && (mode.proof_irrelevant
                || (is_alpha_eq_rec(env, left_existence, right_existence, mode)
                    && is_alpha_eq_rec(env, left_uniqueness, right_uniqueness, mode)))
        }
        _ => false,
    }
}

fn eq_slices(env: &CrateEnv, left: &[Exp], right: &[Exp], mode: EqualityMode) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| is_alpha_eq_rec(env, *left, *right, mode))
}

pub fn exp_is_alpha_eq(env: &CrateEnv, left: Exp, right: Exp) -> bool {
    is_alpha_eq_rec(
        env,
        left,
        right,
        EqualityMode {
            proof_irrelevant: false,
            reduce_to_whnf: false,
            erase_subset_intro: false,
        },
    )
}

fn exp_is_convertible_with_mode(env: &CrateEnv, left: Exp, right: Exp, erase_proofs: bool) -> bool {
    is_alpha_eq_rec(
        env,
        left,
        right,
        EqualityMode {
            proof_irrelevant: erase_proofs,
            reduce_to_whnf: true,
            erase_subset_intro: erase_proofs,
        },
    )
}

fn transform<F>(arena: &Arena, exp: Exp, depth: usize, operation: &mut F) -> Exp
where
    F: FnMut(&Node, usize) -> Option<Exp>,
{
    let node = arena.get(exp);
    if let Some(replacement) = operation(&node, depth) {
        return replacement;
    }

    let mut changed = false;
    let mut child = |child: Exp, child_depth: usize| {
        let transformed = transform(arena, child, child_depth, operation);
        changed |= transformed != child;
        transformed
    };
    let transformed = match node {
        Node::Sort(_) | Node::Bound(_) | Node::ModuleParam(_) => return exp,
        Node::Prod { var, ty, body } => Node::Prod {
            var,
            ty: child(ty, depth),
            body: child(body, depth + 1),
        },
        Node::Lam { var, ty, body } => Node::Lam {
            var,
            ty: child(ty, depth),
            body: child(body, depth + 1),
        },
        Node::SubSet {
            var,
            set,
            predicate,
        } => Node::SubSet {
            var,
            set: child(set, depth),
            predicate: child(predicate, depth + 1),
        },
        Node::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
            base,
            equality,
        } => Node::IdElim {
            left: child(left, depth),
            right: child(right, depth),
            ty: child(ty, depth),
            var,
            predicate: child(predicate, depth + 1),
            base: child(base, depth),
            equality: child(equality, depth),
        },
        Node::DefinedConstant(_) => return exp,
        other => map_children(other, |id| child(id, depth)),
    };
    if changed {
        arena.alloc(transformed)
    } else {
        exp
    }
}

fn map_children(mut node: Node, mut map: impl FnMut(Exp) -> Exp) -> Node {
    match &mut node {
        Node::Sort(_) | Node::Bound(_) | Node::ModuleParam(_) => {}
        Node::Prod { ty, body, .. } | Node::Lam { ty, body, .. } => {
            *ty = map(*ty);
            *body = map(*body);
        }
        Node::App { func, arg } => {
            *func = map(*func);
            *arg = map(*arg);
        }
        Node::DefinedConstant(_) => {}
        Node::IndType { parameters, .. } | Node::IndCtor { parameters, .. } => {
            for parameter in parameters {
                *parameter = map(*parameter);
            }
        }
        Node::IndElim {
            elim,
            return_type,
            cases,
            ..
        } => {
            *elim = map(*elim);
            *return_type = map(*return_type);
            for case in cases {
                *case = map(*case);
            }
        }
        Node::PowerSet { set } | Node::Exists { set } | Node::IdRefl { element: set } => {
            *set = map(*set);
        }
        Node::SubSet { set, predicate, .. } => {
            *set = map(*set);
            *predicate = map(*predicate);
        }
        Node::Pred {
            superset,
            subset,
            element,
        }
        | Node::SubsetElim {
            superset,
            subset,
            element,
        } => {
            *superset = map(*superset);
            *subset = map(*subset);
            *element = map(*element);
        }
        Node::TypeLift { superset, subset } => {
            *superset = map(*superset);
            *subset = map(*subset);
        }
        Node::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => {
            *superset = map(*superset);
            *subset = map(*subset);
            *element = map(*element);
            *proof = map(*proof);
        }
        Node::Equal { left, right } => {
            *left = map(*left);
            *right = map(*right);
        }
        Node::TakeSet {
            domain,
            codomain,
            map: function,
            existence,
            uniqueness,
        } => {
            *domain = map(*domain);
            *codomain = map(*codomain);
            *function = map(*function);
            *existence = map(*existence);
            *uniqueness = map(*uniqueness);
        }
        Node::TakeProp {
            domain,
            proposition,
            map: function,
            existence,
        } => {
            *domain = map(*domain);
            *proposition = map(*proposition);
            *function = map(*function);
            *existence = map(*existence);
        }
        Node::ExistsIntro { element, set } => {
            *element = map(*element);
            *set = map(*set);
        }
        Node::IdElim {
            left,
            right,
            ty,
            predicate,
            base,
            equality,
            ..
        } => {
            *left = map(*left);
            *right = map(*right);
            *ty = map(*ty);
            *predicate = map(*predicate);
            *base = map(*base);
            *equality = map(*equality);
        }
        Node::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => {
            *func = map(*func);
            *domain = map(*domain);
            *codomain = map(*codomain);
            *element = map(*element);
            *existence = map(*existence);
            *uniqueness = map(*uniqueness);
        }
    }
    node
}

/// Rebind references to module-owned entities while materializing a generative
/// module instance. IDs absent from the maps refer outside the source module
/// and remain unchanged.
pub fn remap_global_ids(
    arena: &Arena,
    exp: Exp,
    definitions: &HashMap<DefId, DefId>,
    inductives: &HashMap<InductiveId, InductiveId>,
) -> Exp {
    fn remap(
        arena: &Arena,
        exp: Exp,
        definitions: &HashMap<DefId, DefId>,
        inductives: &HashMap<InductiveId, InductiveId>,
    ) -> Exp {
        let node = arena.get(exp);
        match node {
            Node::DefinedConstant(id) => definitions
                .get(&id)
                .copied()
                .filter(|mapped| *mapped != id)
                .map(|mapped| arena.alloc(Node::DefinedConstant(mapped)))
                .unwrap_or(exp),
            Node::IndType {
                indspec,
                parameters,
            } => {
                let mapped_spec = inductives.get(&indspec).copied().unwrap_or(indspec);
                let mapped_parameters = parameters
                    .iter()
                    .map(|child| remap(arena, *child, definitions, inductives))
                    .collect::<Vec<_>>();
                if mapped_spec == indspec && mapped_parameters == parameters {
                    exp
                } else {
                    arena.alloc(Node::IndType {
                        indspec: mapped_spec,
                        parameters: mapped_parameters,
                    })
                }
            }
            Node::IndCtor {
                indspec,
                parameters,
                idx,
            } => {
                let mapped_spec = inductives.get(&indspec).copied().unwrap_or(indspec);
                let mapped_parameters = parameters
                    .iter()
                    .map(|child| remap(arena, *child, definitions, inductives))
                    .collect::<Vec<_>>();
                if mapped_spec == indspec && mapped_parameters == parameters {
                    exp
                } else {
                    arena.alloc(Node::IndCtor {
                        indspec: mapped_spec,
                        parameters: mapped_parameters,
                        idx,
                    })
                }
            }
            Node::IndElim {
                indspec,
                elim,
                return_type,
                cases,
            } => {
                let mapped_spec = inductives.get(&indspec).copied().unwrap_or(indspec);
                let mapped_elim = remap(arena, elim, definitions, inductives);
                let mapped_return = remap(arena, return_type, definitions, inductives);
                let mapped_cases = cases
                    .iter()
                    .map(|child| remap(arena, *child, definitions, inductives))
                    .collect::<Vec<_>>();
                if mapped_spec == indspec
                    && mapped_elim == elim
                    && mapped_return == return_type
                    && mapped_cases == cases
                {
                    exp
                } else {
                    arena.alloc(Node::IndElim {
                        indspec: mapped_spec,
                        elim: mapped_elim,
                        return_type: mapped_return,
                        cases: mapped_cases,
                    })
                }
            }
            other => {
                let mut changed = false;
                let mapped = map_children(other, |child| {
                    let result = remap(arena, child, definitions, inductives);
                    changed |= result != child;
                    result
                });
                if changed { arena.alloc(mapped) } else { exp }
            }
        }
    }

    remap(arena, exp, definitions, inductives)
}

pub fn exp_subst_module_param(
    arena: &Arena,
    exp: Exp,
    parameter: ModuleParamId,
    replacement: Exp,
) -> Exp {
    transform(arena, exp, 0, &mut |node, depth| match node {
        Node::ModuleParam(candidate) if *candidate == parameter => {
            Some(shift_bound_indices(arena, replacement, depth, 0))
        }
        _ => None,
    })
}

pub(crate) fn shift_bound_indices(arena: &Arena, exp: Exp, amount: usize, cutoff: usize) -> Exp {
    transform(arena, exp, 0, &mut |node, depth| match node {
        Node::Bound(index) if *index >= cutoff + depth => {
            Some(arena.alloc(Node::Bound(index + amount)))
        }
        _ => None,
    })
}

/// Replace the outermost locally bound variable in `body` with `argument`.
pub fn instantiate(arena: &Arena, body: Exp, argument: Exp) -> Exp {
    instantiate_at(arena, body, argument, 0)
}

/// Instantiate one binder in the ambient context, leaving `inner` more recent
/// ambient binders in place.
pub fn instantiate_at(arena: &Arena, body: Exp, argument: Exp, inner: usize) -> Exp {
    instantiate_telescope_at(arena, body, std::slice::from_ref(&argument), inner)
}

/// Instantiate an expression whose ambient telescope consists of `arguments`
/// in declaration order. `Bound(0)` denotes the last telescope entry.
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
        Node::Bound(index) if *index >= depth + inner => {
            let ambient = *index - depth;
            let telescope_index = ambient - inner;
            if telescope_index < arguments.len() {
                let argument = arguments[arguments.len() - 1 - telescope_index];
                Some(shift_bound_indices(arena, argument, depth + inner, 0))
            } else {
                Some(arena.alloc(Node::Bound(index - arguments.len())))
            }
        }
        _ => None,
    })
}

/// Rebase references to an implicit ambient context. `mapping[i]` is the new
/// de Bruijn index for the old ambient index `i`; syntactic binders inside the
/// expression are preserved.
pub fn remap_ambient_indices(arena: &Arena, exp: Exp, mapping: &[usize]) -> Exp {
    transform(arena, exp, 0, &mut |node, depth| match node {
        Node::Bound(index) if *index >= depth => {
            let ambient = *index - depth;
            mapping
                .get(ambient)
                .filter(|mapped| **mapped != ambient)
                .map(|mapped| arena.alloc(Node::Bound(depth + *mapped)))
        }
        _ => None,
    })
}

pub fn exp_contains_bound(arena: &Arena, exp: Exp, target: usize) -> bool {
    fn contains(arena: &Arena, exp: Exp, target: usize, depth: usize) -> bool {
        match arena.get(exp) {
            Node::Bound(index) => index == target + depth,
            Node::Sort(_) | Node::ModuleParam(_) | Node::DefinedConstant(_) => false,
            Node::Prod { ty, body, .. }
            | Node::Lam { ty, body, .. }
            | Node::SubSet {
                set: ty,
                predicate: body,
                ..
            } => contains(arena, ty, target, depth) || contains(arena, body, target, depth + 1),
            Node::IdElim {
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
                    .any(|child| contains(arena, child, target, depth))
                    || contains(arena, predicate, target, depth + 1)
            }
            other => {
                let mut found = false;
                let _ = map_children(other, |child| {
                    found |= contains(arena, child, target, depth);
                    child
                });
                found
            }
        }
    }
    contains(arena, exp, target, 0)
}

pub fn exp_subst_map(arena: &Arena, mut exp: Exp, substitutions: &[(ModuleParamId, Exp)]) -> Exp {
    for (parameter, replacement) in substitutions {
        exp = exp_subst_module_param(arena, exp, *parameter, *replacement);
    }
    exp
}

pub fn erase(env: &CrateEnv, exp: Exp) -> Exp {
    let arena = env.arena();
    match arena.get(exp) {
        Node::SubsetIntro { element, .. } => erase(env, element),
        Node::DefinedConstant(definition) => erase(env, env.definition(definition).body),
        node => {
            let mut changed = false;
            let erased = map_children(node, |child| {
                let result = erase(env, child);
                changed |= result != child;
                result
            });
            if changed { arena.alloc(erased) } else { exp }
        }
    }
}

pub fn exp_reduce_if_top(env: &CrateEnv, exp: Exp) -> Option<Exp> {
    let arena = env.arena();
    match arena.get(exp) {
        Node::App { func, arg } => match arena.get(func) {
            Node::Lam { body, .. } => Some(instantiate(arena, body, arg)),
            _ => None,
        },
        Node::DefinedConstant(definition) => Some(env.definition(definition).body),
        Node::Pred {
            subset, element, ..
        } => match arena.get(subset) {
            Node::SubSet { predicate, .. } => Some(instantiate(arena, predicate, element)),
            _ => None,
        },
        Node::IndElim { .. } => inductive_type_elim_reduce(env, exp).ok(),
        _ => None,
    }
}

fn exp_reduce_head_once(env: &CrateEnv, exp: Exp, erase_subset_intro: bool) -> Option<Exp> {
    let arena = env.arena();
    if erase_subset_intro && let Node::SubsetIntro { element, .. } = arena.get(exp) {
        return Some(element);
    }
    if let Some(reduced) = exp_reduce_if_top(env, exp) {
        return Some(reduced);
    }
    match arena.get(exp) {
        Node::App { func, arg } => {
            let reduced_func = exp_whnf_with_mode(env, func, erase_subset_intro);
            (reduced_func != func).then(|| {
                arena.alloc(Node::App {
                    func: reduced_func,
                    arg,
                })
            })
        }
        Node::Pred {
            superset,
            subset,
            element,
        } => {
            let reduced_subset = exp_whnf_with_mode(env, subset, erase_subset_intro);
            (reduced_subset != subset).then(|| {
                arena.alloc(Node::Pred {
                    superset,
                    subset: reduced_subset,
                    element,
                })
            })
        }
        Node::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => {
            let reduced_elim = exp_whnf_with_mode(env, elim, erase_subset_intro);
            (reduced_elim != elim).then(|| {
                arena.alloc(Node::IndElim {
                    indspec,
                    elim: reduced_elim,
                    return_type,
                    cases,
                })
            })
        }
        _ => None,
    }
}

fn exp_whnf_with_mode(env: &CrateEnv, exp: Exp, erase_subset_intro: bool) -> Exp {
    let mut current = exp;
    while let Some(next) = exp_reduce_head_once(env, current, erase_subset_intro) {
        current = next;
    }
    current
}

pub fn whnf(env: &CrateEnv, exp: Exp) -> Exp {
    exp_whnf_with_mode(env, exp, false)
}

pub fn normalize(env: &CrateEnv, exp: Exp) -> Exp {
    let arena = env.arena();
    let head = whnf(env, exp);
    let node = arena.get(head);
    let mut changed = false;
    let normalized = map_children(node, |child| {
        let result = normalize(env, child);
        changed |= result != child;
        result
    });
    if changed {
        arena.alloc(normalized)
    } else {
        head
    }
}

pub fn reduce_one(env: &CrateEnv, exp: Exp) -> Option<Exp> {
    if let Some(reduced) = exp_reduce_if_top(env, exp) {
        return Some(reduced);
    }
    let normalized = normalize(env, exp);
    (normalized != exp).then_some(normalized)
}

pub fn convertible(env: &CrateEnv, left: Exp, right: Exp) -> bool {
    exp_is_convertible_with_mode(env, left, right, false)
}

pub fn erased_normal(env: &CrateEnv, exp: Exp) -> Exp {
    let erased = erase(env, exp);
    normalize(env, erased)
}

pub fn erased_convertible(env: &CrateEnv, left: Exp, right: Exp) -> bool {
    exp_is_convertible_with_mode(env, left, right, true)
}

pub(crate) fn type_head_normal(env: &CrateEnv, ty: Exp) -> Exp {
    exp_whnf_with_mode(env, ty, true)
}

pub(crate) fn expose_product(env: &CrateEnv, ty: Exp) -> Option<(SymbolId, Exp, Exp)> {
    let arena = env.arena();
    let mut current = type_head_normal(env, ty);
    loop {
        match arena.get(current) {
            Node::Prod { var, ty, body } => return Some((var, ty, body)),
            Node::TypeLift { superset, .. } => current = type_head_normal(env, superset),
            _ => return None,
        }
    }
}

pub(crate) fn base_carrier(env: &CrateEnv, ty: Exp) -> Exp {
    let arena = env.arena();
    let mut current = type_head_normal(env, ty);
    loop {
        match arena.get(current) {
            Node::TypeLift { superset, .. } => current = type_head_normal(env, superset),
            _ => return current,
        }
    }
}

pub(crate) fn common_ambient_carrier(env: &CrateEnv, left_ty: Exp, right_ty: Exp) -> Option<Exp> {
    let left_carrier = base_carrier(env, left_ty);
    let right_carrier = base_carrier(env, right_ty);
    erased_convertible(env, left_carrier, right_carrier).then_some(left_carrier)
}

pub(crate) fn can_weaken_to(env: &CrateEnv, inferred: Exp, expected: Exp) -> bool {
    if erased_convertible(env, inferred, expected) {
        return true;
    }
    let arena = env.arena();
    let inferred = type_head_normal(env, inferred);
    let expected = type_head_normal(env, expected);
    match (arena.get(inferred), arena.get(expected)) {
        (Node::TypeLift { superset, .. }, _) => can_weaken_to(env, superset, expected),
        (
            Node::Prod {
                ty: inferred_domain,
                body: inferred_body,
                ..
            },
            Node::Prod {
                ty: expected_domain,
                body: expected_body,
                ..
            },
        ) if erased_convertible(env, inferred_domain, expected_domain) => {
            can_weaken_to(env, inferred_body, expected_body)
        }
        _ => false,
    }
}
