use std::rc::Rc;

use crate::inductive::inductive_type_elim_reduce;

use super::exp::*;

pub fn exp_contains_as_freevar(arena: &Arena, exp: Exp, var: &Var) -> bool {
    match arena.get(exp) {
        Node::Sort(_) | Node::Bound(_) => false,
        Node::Var(candidate) => candidate.is_eq_ptr(var),
        Node::Prod { ty, body, .. } | Node::Lam { ty, body, .. } => {
            exp_contains_as_freevar(arena, ty, var) || exp_contains_as_freevar(arena, body, var)
        }
        Node::App { func, arg } => {
            exp_contains_as_freevar(arena, func, var) || exp_contains_as_freevar(arena, arg, var)
        }
        Node::DefinedConstant(definition) => {
            exp_contains_as_freevar(arena, definition.ty, var)
                || exp_contains_as_freevar(arena, definition.body, var)
        }
        Node::IndType { parameters, .. } | Node::IndCtor { parameters, .. } => parameters
            .into_iter()
            .any(|argument| exp_contains_as_freevar(arena, argument, var)),
        Node::IndElim {
            elim,
            return_type,
            cases,
            ..
        } => {
            exp_contains_as_freevar(arena, elim, var)
                || exp_contains_as_freevar(arena, return_type, var)
                || cases
                    .into_iter()
                    .any(|case| exp_contains_as_freevar(arena, case, var))
        }
        Node::PowerSet { set } | Node::Exists { set } | Node::IdRefl { element: set } => {
            exp_contains_as_freevar(arena, set, var)
        }
        Node::SubSet { set, predicate, .. } => {
            exp_contains_as_freevar(arena, set, var)
                || exp_contains_as_freevar(arena, predicate, var)
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
            .any(|child| exp_contains_as_freevar(arena, child, var)),
        Node::TypeLift { superset, subset }
        | Node::Equal {
            left: superset,
            right: subset,
        } => {
            exp_contains_as_freevar(arena, superset, var)
                || exp_contains_as_freevar(arena, subset, var)
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
            .any(|child| exp_contains_as_freevar(arena, child, var)),
        Node::TakeSet {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => [domain, codomain, map, existence, uniqueness]
            .into_iter()
            .any(|child| exp_contains_as_freevar(arena, child, var)),
        Node::ExistsIntro { element, set } => {
            exp_contains_as_freevar(arena, element, var) || exp_contains_as_freevar(arena, set, var)
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
            .any(|child| exp_contains_as_freevar(arena, child, var)),
        Node::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => [func, domain, codomain, element, existence, uniqueness]
            .into_iter()
            .any(|child| exp_contains_as_freevar(arena, child, var)),
    }
}

#[derive(Clone, Copy)]
struct EqualityMode {
    proof_irrelevant: bool,
    reduce_to_whnf: bool,
    erase_subset_intro: bool,
}

fn is_alpha_eq_rec(arena: &Arena, left: Exp, right: Exp, mode: EqualityMode) -> bool {
    let left = if mode.reduce_to_whnf {
        exp_whnf_with_mode(arena, left, mode.erase_subset_intro)
    } else {
        left
    };
    let right = if mode.reduce_to_whnf {
        exp_whnf_with_mode(arena, right, mode.erase_subset_intro)
    } else {
        right
    };
    if left == right {
        return true;
    }

    match (arena.get(left), arena.get(right)) {
        (Node::Sort(left), Node::Sort(right)) => left == right,
        (Node::Bound(left), Node::Bound(right)) => left == right,
        (Node::Var(left), Node::Var(right)) => left.as_str() == right.as_str(),
        (
            Node::Prod {
                ty: left_ty,
                body: left_body,
                ..
            },
            Node::Prod {
                ty: right_ty,
                body: right_body,
                ..
            },
        )
        | (
            Node::Lam {
                ty: left_ty,
                body: left_body,
                ..
            },
            Node::Lam {
                ty: right_ty,
                body: right_body,
                ..
            },
        ) => {
            is_alpha_eq_rec(arena, left_ty, right_ty, mode)
                && is_alpha_eq_rec(arena, left_body, right_body, mode)
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
            is_alpha_eq_rec(arena, left_func, right_func, mode)
                && is_alpha_eq_rec(arena, left_arg, right_arg, mode)
        }
        (Node::DefinedConstant(left), Node::DefinedConstant(right)) => {
            Rc::ptr_eq(&left, &right)
                || (is_alpha_eq_rec(arena, left.ty, right.ty, mode)
                    && is_alpha_eq_rec(arena, left.body, right.body, mode))
        }
        (
            Node::IndType {
                indspec: left_spec,
                parameters: left_parameters,
            },
            Node::IndType {
                indspec: right_spec,
                parameters: right_parameters,
            },
        ) => {
            Rc::ptr_eq(&left_spec, &right_spec)
                && eq_slices(arena, &left_parameters, &right_parameters, mode)
        }
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
                && Rc::ptr_eq(&left_spec, &right_spec)
                && eq_slices(arena, &left_parameters, &right_parameters, mode)
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
            Rc::ptr_eq(&left_spec, &right_spec)
                && is_alpha_eq_rec(arena, left_elim, right_elim, mode)
                && is_alpha_eq_rec(arena, left_return, right_return, mode)
                && eq_slices(arena, &left_cases, &right_cases, mode)
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
            is_alpha_eq_rec(arena, left_superset, right_superset, mode)
                && is_alpha_eq_rec(arena, left_subset, right_subset, mode)
                && is_alpha_eq_rec(arena, left_element, right_element, mode)
                && (mode.proof_irrelevant || is_alpha_eq_rec(arena, left_proof, right_proof, mode))
        }
        (Node::PowerSet { set: left }, Node::PowerSet { set: right })
        | (Node::Exists { set: left }, Node::Exists { set: right })
        | (Node::IdRefl { element: left }, Node::IdRefl { element: right }) => {
            is_alpha_eq_rec(arena, left, right, mode)
        }
        (
            Node::SubSet {
                set: left_set,
                predicate: left_predicate,
                ..
            },
            Node::SubSet {
                set: right_set,
                predicate: right_predicate,
                ..
            },
        ) => {
            is_alpha_eq_rec(arena, left_set, right_set, mode)
                && is_alpha_eq_rec(arena, left_predicate, right_predicate, mode)
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
            is_alpha_eq_rec(arena, left_superset, right_superset, mode)
                && is_alpha_eq_rec(arena, left_subset, right_subset, mode)
                && is_alpha_eq_rec(arena, left_element, right_element, mode)
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
            is_alpha_eq_rec(arena, left_first, right_first, mode)
                && is_alpha_eq_rec(arena, left_second, right_second, mode)
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
            is_alpha_eq_rec(arena, left_domain, right_domain, mode)
                && is_alpha_eq_rec(arena, left_codomain, right_codomain, mode)
                && is_alpha_eq_rec(arena, left_map, right_map, mode)
                && (mode.proof_irrelevant
                    || (is_alpha_eq_rec(arena, left_existence, right_existence, mode)
                        && is_alpha_eq_rec(arena, left_uniqueness, right_uniqueness, mode)))
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
            is_alpha_eq_rec(arena, left_proposition, right_proposition, mode)
                && (mode.proof_irrelevant
                    || (is_alpha_eq_rec(arena, left_domain, right_domain, mode)
                        && is_alpha_eq_rec(arena, left_map, right_map, mode)
                        && is_alpha_eq_rec(arena, left_existence, right_existence, mode)))
        }
        (
            Node::IdElim {
                left: left_left,
                right: left_right,
                ty: left_ty,
                predicate: left_predicate,
                base: left_base,
                equality: left_equality,
                ..
            },
            Node::IdElim {
                left: right_left,
                right: right_right,
                ty: right_ty,
                predicate: right_predicate,
                base: right_base,
                equality: right_equality,
                ..
            },
        ) => eq_slices(
            arena,
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
        ),
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
                arena,
                &[left_func, left_domain, left_codomain, left_element],
                &[right_func, right_domain, right_codomain, right_element],
                mode,
            ) && (mode.proof_irrelevant
                || (is_alpha_eq_rec(arena, left_existence, right_existence, mode)
                    && is_alpha_eq_rec(arena, left_uniqueness, right_uniqueness, mode)))
        }
        _ => false,
    }
}

fn eq_slices(arena: &Arena, left: &[Exp], right: &[Exp], mode: EqualityMode) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| is_alpha_eq_rec(arena, *left, *right, mode))
}

pub fn exp_is_alpha_eq(arena: &Arena, left: Exp, right: Exp) -> bool {
    is_alpha_eq_rec(
        arena,
        left,
        right,
        EqualityMode {
            proof_irrelevant: false,
            reduce_to_whnf: false,
            erase_subset_intro: false,
        },
    )
}

fn exp_is_convertible_with_mode(arena: &Arena, left: Exp, right: Exp, erase_proofs: bool) -> bool {
    is_alpha_eq_rec(
        arena,
        left,
        right,
        EqualityMode {
            proof_irrelevant: erase_proofs,
            reduce_to_whnf: true,
            erase_subset_intro: erase_proofs,
        },
    )
}

fn transform<F>(
    arena: &Arena,
    exp: Exp,
    depth: usize,
    descend_definitions: bool,
    operation: &mut F,
) -> Exp
where
    F: FnMut(&Node, usize) -> Option<Exp>,
{
    let node = arena.get(exp);
    if let Some(replacement) = operation(&node, depth) {
        return replacement;
    }

    let mut changed = false;
    let mut child = |child: Exp, child_depth: usize| {
        let transformed = transform(arena, child, child_depth, descend_definitions, operation);
        changed |= transformed != child;
        transformed
    };
    let transformed = match node {
        Node::Sort(_) | Node::Bound(_) | Node::Var(_) => return exp,
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
        Node::DefinedConstant(definition) if descend_definitions => {
            let ty = child(definition.ty, depth);
            let body = child(definition.body, depth);
            Node::DefinedConstant(Rc::new(DefinedConstant { ty, body }))
        }
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
        Node::Sort(_) | Node::Bound(_) | Node::Var(_) => {}
        Node::Prod { ty, body, .. } | Node::Lam { ty, body, .. } => {
            *ty = map(*ty);
            *body = map(*body);
        }
        Node::App { func, arg } => {
            *func = map(*func);
            *arg = map(*arg);
        }
        Node::DefinedConstant(definition) => {
            let ty = map(definition.ty);
            let body = map(definition.body);
            *definition = Rc::new(DefinedConstant { ty, body });
        }
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

pub fn exp_subst(arena: &Arena, exp: Exp, var: &Var, replacement: Exp) -> Exp {
    transform(arena, exp, 0, true, &mut |node, depth| match node {
        Node::Var(candidate) if candidate.is_eq_ptr(var) => {
            Some(shift_bound_indices(arena, replacement, depth, 0))
        }
        _ => None,
    })
}

pub(crate) fn shift_bound_indices(arena: &Arena, exp: Exp, amount: usize, cutoff: usize) -> Exp {
    transform(arena, exp, 0, false, &mut |node, depth| match node {
        Node::Bound(index) if *index >= cutoff + depth => {
            Some(arena.alloc(Node::Bound(index + amount)))
        }
        _ => None,
    })
}

/// Replace the outermost locally bound variable in `body` with `argument`.
pub fn instantiate(arena: &Arena, body: Exp, binder: &Var, argument: Exp) -> Exp {
    let instantiated = transform(arena, body, 0, false, &mut |node, depth| match node {
        Node::Bound(index) if *index == depth => {
            Some(shift_bound_indices(arena, argument, depth, 0))
        }
        Node::Bound(index) if *index > depth => Some(arena.alloc(Node::Bound(index - 1))),
        _ => None,
    });
    if instantiated == body {
        exp_subst(arena, body, binder, argument)
    } else {
        instantiated
    }
}

pub fn exp_contains_bound(arena: &Arena, exp: Exp, target: usize) -> bool {
    fn contains(arena: &Arena, exp: Exp, target: usize, depth: usize) -> bool {
        match arena.get(exp) {
            Node::Bound(index) => index == target + depth,
            Node::Sort(_) | Node::Var(_) | Node::DefinedConstant(_) => false,
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

pub fn exp_subst_map(arena: &Arena, mut exp: Exp, substitutions: &[(Var, Exp)]) -> Exp {
    for (var, replacement) in substitutions {
        exp = exp_subst(arena, exp, var, *replacement);
    }
    exp
}

pub fn erase(arena: &Arena, exp: Exp) -> Exp {
    match arena.get(exp) {
        Node::SubsetIntro { element, .. } => erase(arena, element),
        Node::DefinedConstant(definition) => erase(arena, definition.body),
        node => {
            let mut changed = false;
            let erased = map_children(node, |child| {
                let result = erase(arena, child);
                changed |= result != child;
                result
            });
            if changed { arena.alloc(erased) } else { exp }
        }
    }
}

pub fn exp_reduce_if_top(arena: &Arena, exp: Exp) -> Option<Exp> {
    match arena.get(exp) {
        Node::App { func, arg } => match arena.get(func) {
            Node::Lam { var, body, .. } => Some(instantiate(arena, body, &var, arg)),
            _ => None,
        },
        Node::DefinedConstant(definition) => Some(definition.body),
        Node::Pred {
            subset, element, ..
        } => match arena.get(subset) {
            Node::SubSet { var, predicate, .. } => {
                Some(instantiate(arena, predicate, &var, element))
            }
            _ => None,
        },
        Node::IndElim { .. } => inductive_type_elim_reduce(arena, exp).ok(),
        _ => None,
    }
}

fn exp_reduce_head_once(arena: &Arena, exp: Exp, erase_subset_intro: bool) -> Option<Exp> {
    if erase_subset_intro && let Node::SubsetIntro { element, .. } = arena.get(exp) {
        return Some(element);
    }
    if let Some(reduced) = exp_reduce_if_top(arena, exp) {
        return Some(reduced);
    }
    match arena.get(exp) {
        Node::App { func, arg } => {
            let reduced_func = exp_whnf_with_mode(arena, func, erase_subset_intro);
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
            let reduced_subset = exp_whnf_with_mode(arena, subset, erase_subset_intro);
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
            let reduced_elim = exp_whnf_with_mode(arena, elim, erase_subset_intro);
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

fn exp_whnf_with_mode(arena: &Arena, exp: Exp, erase_subset_intro: bool) -> Exp {
    let mut current = exp;
    while let Some(next) = exp_reduce_head_once(arena, current, erase_subset_intro) {
        current = next;
    }
    current
}

pub fn whnf(arena: &Arena, exp: Exp) -> Exp {
    exp_whnf_with_mode(arena, exp, false)
}

pub fn normalize(arena: &Arena, exp: Exp) -> Exp {
    let head = whnf(arena, exp);
    let node = arena.get(head);
    let mut changed = false;
    let normalized = map_children(node, |child| {
        let result = normalize(arena, child);
        changed |= result != child;
        result
    });
    if changed {
        arena.alloc(normalized)
    } else {
        head
    }
}

pub fn reduce_one(arena: &Arena, exp: Exp) -> Option<Exp> {
    if let Some(reduced) = exp_reduce_if_top(arena, exp) {
        return Some(reduced);
    }
    let normalized = normalize(arena, exp);
    (normalized != exp).then_some(normalized)
}

pub fn convertible(arena: &Arena, left: Exp, right: Exp) -> bool {
    exp_is_convertible_with_mode(arena, left, right, false)
}

pub fn erased_normal(arena: &Arena, exp: Exp) -> Exp {
    let erased = erase(arena, exp);
    normalize(arena, erased)
}

pub fn erased_convertible(arena: &Arena, left: Exp, right: Exp) -> bool {
    exp_is_convertible_with_mode(arena, left, right, true)
}

pub(crate) fn type_head_normal(arena: &Arena, ty: Exp) -> Exp {
    exp_whnf_with_mode(arena, ty, true)
}

pub(crate) fn expose_product(arena: &Arena, ty: Exp) -> Option<(Var, Exp, Exp)> {
    let mut current = type_head_normal(arena, ty);
    loop {
        match arena.get(current) {
            Node::Prod { var, ty, body } => return Some((var, ty, body)),
            Node::TypeLift { superset, .. } => current = type_head_normal(arena, superset),
            _ => return None,
        }
    }
}

pub(crate) fn base_carrier(arena: &Arena, ty: Exp) -> Exp {
    let mut current = type_head_normal(arena, ty);
    loop {
        match arena.get(current) {
            Node::TypeLift { superset, .. } => current = type_head_normal(arena, superset),
            _ => return current,
        }
    }
}

pub(crate) fn common_ambient_carrier(arena: &Arena, left_ty: Exp, right_ty: Exp) -> Option<Exp> {
    let left_carrier = base_carrier(arena, left_ty);
    let right_carrier = base_carrier(arena, right_ty);
    erased_convertible(arena, left_carrier, right_carrier).then_some(left_carrier)
}

pub(crate) fn can_weaken_to(arena: &Arena, inferred: Exp, expected: Exp) -> bool {
    if erased_convertible(arena, inferred, expected) {
        return true;
    }
    let inferred = type_head_normal(arena, inferred);
    let expected = type_head_normal(arena, expected);
    match (arena.get(inferred), arena.get(expected)) {
        (Node::TypeLift { superset, .. }, _) => can_weaken_to(arena, superset, expected),
        (
            Node::Prod {
                ty: inferred_domain,
                body: inferred_body,
                ..
            },
            Node::Prod {
                var: expected_var,
                ty: expected_domain,
                body: expected_body,
            },
        ) if erased_convertible(arena, inferred_domain, expected_domain) => {
            let free = arena.var(expected_var.clone());
            let expected_body = instantiate(arena, expected_body, &expected_var, free);
            can_weaken_to(arena, inferred_body, expected_body)
        }
        _ => false,
    }
}
