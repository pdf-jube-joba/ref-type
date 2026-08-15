use std::{borrow::Cow, ops::Deref, rc};

use crate::inductive::inductive_type_elim_reduce;

use super::exp::*;

pub fn exp_contains_as_freevar(e: &Exp, v: &Var) -> bool {
    match e {
        Exp::Sort(_) => false,
        Exp::Var(var) => var.is_eq_ptr(v),
        Exp::Prod { var, ty, body } => {
            exp_contains_as_freevar(ty, v)
                || (!var.is_eq_ptr(v) && exp_contains_as_freevar(body, v))
        }
        Exp::Lam { var, ty, body } => {
            exp_contains_as_freevar(ty, v)
                || (!var.is_eq_ptr(v) && exp_contains_as_freevar(body, v))
        }
        Exp::App { func, arg } => {
            exp_contains_as_freevar(func, v) || exp_contains_as_freevar(arg, v)
        }
        Exp::DefinedConstant(rc) => {
            let DefinedConstant { ty, body: inner } = rc.as_ref();
            exp_contains_as_freevar(ty, v) || exp_contains_as_freevar(inner, v)
        }
        Exp::IndType { parameters, .. } => {
            parameters.iter().any(|arg| exp_contains_as_freevar(arg, v))
        }
        Exp::IndCtor { parameters, .. } => {
            parameters.iter().any(|arg| exp_contains_as_freevar(arg, v))
        }
        Exp::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => {
            'inner: {
                for (var, arg) in indspec.parameters().iter().chain(indspec.indices().iter()) {
                    if var.is_eq_ptr(v) {
                        break 'inner;
                    }
                    if exp_contains_as_freevar(arg, v) {
                        return true;
                    }
                }
                for ctor in indspec.constructors() {
                    let dummy = Var::dummy();
                    let as_exp = ctor.as_exp_with_type(&Exp::Var(dummy.clone()));
                    if exp_contains_as_freevar(&as_exp, v) {
                        return true;
                    }
                }
            }
            exp_contains_as_freevar(elim, v)
                || exp_contains_as_freevar(return_type, v)
                || cases.iter().any(|case| exp_contains_as_freevar(case, v))
        }
        Exp::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => {
            exp_contains_as_freevar(superset, v)
                || exp_contains_as_freevar(subset, v)
                || exp_contains_as_freevar(element, v)
                || exp_contains_as_freevar(proof, v)
        }
        Exp::PowerSet { set } => exp_contains_as_freevar(set, v),
        Exp::SubSet {
            var,
            set,
            predicate,
        } => {
            exp_contains_as_freevar(set, v)
                || (!var.is_eq_ptr(v) && exp_contains_as_freevar(predicate, v))
        }
        Exp::Pred {
            superset,
            subset,
            element,
        } => {
            exp_contains_as_freevar(superset, v)
                || exp_contains_as_freevar(subset, v)
                || exp_contains_as_freevar(element, v)
        }
        Exp::TypeLift { superset, subset } => {
            exp_contains_as_freevar(superset, v) || exp_contains_as_freevar(subset, v)
        }
        Exp::Equal { left, right } => {
            exp_contains_as_freevar(left, v) || exp_contains_as_freevar(right, v)
        }
        Exp::Exists { set } => exp_contains_as_freevar(set, v),
        Exp::TakeSet {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => {
            exp_contains_as_freevar(domain, v)
                || exp_contains_as_freevar(codomain, v)
                || exp_contains_as_freevar(map, v)
                || exp_contains_as_freevar(existence, v)
                || exp_contains_as_freevar(uniqueness, v)
        }
        Exp::TakeProp {
            domain,
            proposition,
            map,
            existence,
        } => {
            exp_contains_as_freevar(domain, v)
                || exp_contains_as_freevar(proposition, v)
                || exp_contains_as_freevar(map, v)
                || exp_contains_as_freevar(existence, v)
        }
        Exp::ExistsIntro { element, set } => {
            exp_contains_as_freevar(element, v) || exp_contains_as_freevar(set, v)
        }
        Exp::SubsetElim {
            element,
            subset,
            superset,
        } => {
            exp_contains_as_freevar(element, v)
                || exp_contains_as_freevar(subset, v)
                || exp_contains_as_freevar(superset, v)
        }
        Exp::IdRefl { element } => exp_contains_as_freevar(element, v),
        Exp::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
            base,
            equality,
        } => {
            exp_contains_as_freevar(left, v)
                || exp_contains_as_freevar(right, v)
                || exp_contains_as_freevar(ty, v)
                || (!var.is_eq_ptr(v) && exp_contains_as_freevar(predicate, v))
                || exp_contains_as_freevar(base, v)
                || exp_contains_as_freevar(equality, v)
        }
        Exp::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => {
            exp_contains_as_freevar(func, v)
                || exp_contains_as_freevar(domain, v)
                || exp_contains_as_freevar(codomain, v)
                || exp_contains_as_freevar(element, v)
                || exp_contains_as_freevar(existence, v)
                || exp_contains_as_freevar(uniqueness, v)
        }
    }
}

struct AlphaEqEnv {
    bound: Vec<Var>,
    take_proofs_irrelevant: bool,
    reduce_to_whnf: bool,
    erase_subset_intro: bool,
}

impl Deref for AlphaEqEnv {
    type Target = Vec<Var>;

    fn deref(&self) -> &Self::Target {
        &self.bound
    }
}

impl std::ops::DerefMut for AlphaEqEnv {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.bound
    }
}

fn is_alpha_eq_rec(e1: &Exp, e2: &Exp, env1: &mut AlphaEqEnv, env2: &mut AlphaEqEnv) -> bool {
    let whnf1 = env1
        .reduce_to_whnf
        .then(|| exp_whnf_with_mode(e1, env1.erase_subset_intro));
    let whnf2 = env2
        .reduce_to_whnf
        .then(|| exp_whnf_with_mode(e2, env2.erase_subset_intro));
    let e1 = whnf1.as_ref().map_or(e1, Cow::as_ref);
    let e2 = whnf2.as_ref().map_or(e2, Cow::as_ref);

    match (e1, e2) {
        (Exp::Sort(s1), Exp::Sort(s2)) => s1 == s2,
        (Exp::Var(v1), Exp::Var(v2)) => {
            let pos1 = env1.iter().rposition(|v| v.is_eq_ptr(v1));
            let pos2 = env2.iter().rposition(|v| v.is_eq_ptr(v2));
            match (pos1, pos2) {
                (Some(p1), Some(p2)) => p1 == p2,
                (None, None) => v1.as_str() == v2.as_str(),
                _ => false,
            }
        }
        (
            Exp::Prod {
                var: var1,
                ty: ty1,
                body: body1,
            },
            Exp::Prod {
                var: var2,
                ty: ty2,
                body: body2,
            },
        ) => {
            is_alpha_eq_rec(ty1, ty2, env1, env2) && {
                env1.push(var1.clone());
                env2.push(var2.clone());
                let res = is_alpha_eq_rec(body1, body2, env1, env2);
                env1.pop();
                env2.pop();
                res
            }
        }
        (
            Exp::Lam {
                var: var1,
                ty: ty1,
                body: body1,
            },
            Exp::Lam {
                var: var2,
                ty: ty2,
                body: body2,
            },
        ) => {
            is_alpha_eq_rec(ty1, ty2, env1, env2) && {
                env1.push(var1.clone());
                env2.push(var2.clone());
                let res = is_alpha_eq_rec(body1, body2, env1, env2);
                env1.pop();
                env2.pop();
                res
            }
        }
        (Exp::App { func: f1, arg: a1 }, Exp::App { func: f2, arg: a2 }) => {
            is_alpha_eq_rec(f1, f2, env1, env2) && is_alpha_eq_rec(a1, a2, env1, env2)
        }
        (Exp::DefinedConstant(rc1), Exp::DefinedConstant(rc2)) => {
            let DefinedConstant {
                ty: ty1,
                body: inner1,
            } = rc1.as_ref();
            let DefinedConstant {
                ty: ty2,
                body: inner2,
            } = rc2.as_ref();
            is_alpha_eq_rec(ty1, ty2, env1, env2) && is_alpha_eq_rec(inner1, inner2, env1, env2)
        }
        (
            Exp::IndType {
                indspec: ty1,
                parameters: parameter1,
            },
            Exp::IndType {
                indspec: ty2,
                parameters: parameter2,
            },
        ) => {
            std::rc::Rc::ptr_eq(ty1, ty2)
                && parameter1.len() == parameter2.len()
                && parameter1
                    .iter()
                    .zip(parameter2.iter())
                    .all(|(a1, a2)| is_alpha_eq_rec(a1, a2, env1, env2))
        }
        (
            Exp::IndCtor {
                indspec: ty1,
                idx: idx1,
                parameters: parameter1,
            },
            Exp::IndCtor {
                indspec: ty2,
                idx: idx2,
                parameters: parameter2,
            },
        ) => {
            std::rc::Rc::ptr_eq(ty1, ty2)
                && idx1 == idx2
                && parameter1.len() == parameter2.len()
                && parameter1
                    .iter()
                    .zip(parameter2.iter())
                    .all(|(a1, a2)| is_alpha_eq_rec(a1, a2, env1, env2))
        }
        (
            Exp::IndElim {
                indspec: ty1,
                elim: elim1,
                return_type: ret1,
                cases: cases1,
            },
            Exp::IndElim {
                indspec: ty2,
                elim: elim2,
                return_type: ret2,
                cases: cases2,
            },
        ) => {
            std::rc::Rc::ptr_eq(ty1, ty2)
                && is_alpha_eq_rec(elim1, elim2, env1, env2)
                && is_alpha_eq_rec(ret1, ret2, env1, env2)
                && cases1.len() == cases2.len()
                && cases1
                    .iter()
                    .zip(cases2.iter())
                    .all(|(c1, c2)| is_alpha_eq_rec(c1, c2, env1, env2))
        }
        (
            Exp::SubsetIntro {
                superset: a1,
                subset: s1,
                element: e1,
                proof: p1,
            },
            Exp::SubsetIntro {
                superset: a2,
                subset: s2,
                element: e2,
                proof: p2,
            },
        ) => {
            is_alpha_eq_rec(a1, a2, env1, env2)
                && is_alpha_eq_rec(s1, s2, env1, env2)
                && is_alpha_eq_rec(e1, e2, env1, env2)
                && is_alpha_eq_rec(p1, p2, env1, env2)
        }
        (Exp::PowerSet { set: e1 }, Exp::PowerSet { set: e2 }) => {
            is_alpha_eq_rec(e1, e2, env1, env2)
        }
        (
            Exp::SubSet {
                var: var1,
                set: e1,
                predicate: p1,
            },
            Exp::SubSet {
                var: var2,
                set: e2,
                predicate: p2,
            },
        ) => {
            is_alpha_eq_rec(e1, e2, env1, env2) && {
                env1.push(var1.clone());
                env2.push(var2.clone());
                let res = is_alpha_eq_rec(p1, p2, env1, env2);
                env1.pop();
                env2.pop();
                res
            }
        }
        (
            Exp::Pred {
                superset: s1,
                subset: sub1,
                element: e1,
            },
            Exp::Pred {
                superset: s2,
                subset: sub2,
                element: e2,
            },
        ) => {
            is_alpha_eq_rec(s1, s2, env1, env2)
                && is_alpha_eq_rec(sub1, sub2, env1, env2)
                && is_alpha_eq_rec(e1, e2, env1, env2)
        }
        (
            Exp::TypeLift {
                superset: s1,
                subset: sub1,
            },
            Exp::TypeLift {
                superset: s2,
                subset: sub2,
            },
        ) => is_alpha_eq_rec(s1, s2, env1, env2) && is_alpha_eq_rec(sub1, sub2, env1, env2),
        (
            Exp::Equal {
                left: l1,
                right: r1,
            },
            Exp::Equal {
                left: l2,
                right: r2,
            },
        ) => is_alpha_eq_rec(l1, l2, env1, env2) && is_alpha_eq_rec(r1, r2, env1, env2),
        (Exp::Exists { set: ty1 }, Exp::Exists { set: ty2 }) => {
            is_alpha_eq_rec(ty1, ty2, env1, env2)
        }
        (
            Exp::TakeSet {
                domain: d1,
                codomain: c1,
                map: m1,
                existence: e1,
                uniqueness: u1,
            },
            Exp::TakeSet {
                domain: d2,
                codomain: c2,
                map: m2,
                existence: e2,
                uniqueness: u2,
            },
        ) => {
            is_alpha_eq_rec(d1, d2, env1, env2)
                && is_alpha_eq_rec(c1, c2, env1, env2)
                && is_alpha_eq_rec(m1, m2, env1, env2)
                && (env1.take_proofs_irrelevant
                    || (is_alpha_eq_rec(e1, e2, env1, env2) && is_alpha_eq_rec(u1, u2, env1, env2)))
        }
        (
            Exp::TakeProp {
                domain: d1,
                proposition: p1,
                map: m1,
                existence: e1,
            },
            Exp::TakeProp {
                domain: d2,
                proposition: p2,
                map: m2,
                existence: e2,
            },
        ) => {
            is_alpha_eq_rec(p1, p2, env1, env2)
                && (env1.take_proofs_irrelevant
                    || (is_alpha_eq_rec(d1, d2, env1, env2)
                        && is_alpha_eq_rec(m1, m2, env1, env2)
                        && is_alpha_eq_rec(e1, e2, env1, env2)))
        }
        (
            Exp::ExistsIntro {
                element: e1,
                set: s1,
            },
            Exp::ExistsIntro {
                element: e2,
                set: s2,
            },
        ) => is_alpha_eq_rec(e1, e2, env1, env2) && is_alpha_eq_rec(s1, s2, env1, env2),
        (
            Exp::SubsetElim {
                element: e1,
                subset: b1,
                superset: s1,
            },
            Exp::SubsetElim {
                element: e2,
                subset: b2,
                superset: s2,
            },
        ) => {
            is_alpha_eq_rec(e1, e2, env1, env2)
                && is_alpha_eq_rec(b1, b2, env1, env2)
                && is_alpha_eq_rec(s1, s2, env1, env2)
        }
        (Exp::IdRefl { element: e1 }, Exp::IdRefl { element: e2 }) => {
            is_alpha_eq_rec(e1, e2, env1, env2)
        }
        (
            Exp::IdElim {
                left: l1,
                right: r1,
                ty: t1,
                var: v1,
                predicate: p1,
                base: b1,
                equality: q1,
            },
            Exp::IdElim {
                left: l2,
                right: r2,
                ty: t2,
                var: v2,
                predicate: p2,
                base: b2,
                equality: q2,
            },
        ) => {
            is_alpha_eq_rec(l1, l2, env1, env2)
                && is_alpha_eq_rec(r1, r2, env1, env2)
                && is_alpha_eq_rec(t1, t2, env1, env2)
                && {
                    env1.push(v1.clone());
                    env2.push(v2.clone());
                    let equal = is_alpha_eq_rec(p1, p2, env1, env2);
                    env1.pop();
                    env2.pop();
                    equal
                }
                && is_alpha_eq_rec(b1, b2, env1, env2)
                && is_alpha_eq_rec(q1, q2, env1, env2)
        }
        (
            Exp::TakeEq {
                func: f1,
                domain: d1,
                codomain: c1,
                element: e1,
                existence: x1,
                uniqueness: u1,
            },
            Exp::TakeEq {
                func: f2,
                domain: d2,
                codomain: c2,
                element: e2,
                existence: x2,
                uniqueness: u2,
            },
        ) => {
            is_alpha_eq_rec(f1, f2, env1, env2)
                && is_alpha_eq_rec(d1, d2, env1, env2)
                && is_alpha_eq_rec(c1, c2, env1, env2)
                && is_alpha_eq_rec(e1, e2, env1, env2)
                && (env1.take_proofs_irrelevant
                    || (is_alpha_eq_rec(x1, x2, env1, env2) && is_alpha_eq_rec(u1, u2, env1, env2)))
        }
        _ => false,
    }
}

pub fn exp_is_alpha_eq(e1: &Exp, e2: &Exp) -> bool {
    is_alpha_eq_rec(
        e1,
        e2,
        &mut AlphaEqEnv {
            bound: vec![],
            take_proofs_irrelevant: false,
            reduce_to_whnf: false,
            erase_subset_intro: false,
        },
        &mut AlphaEqEnv {
            bound: vec![],
            take_proofs_irrelevant: false,
            reduce_to_whnf: false,
            erase_subset_intro: false,
        },
    )
}

fn exp_is_convertible_with_mode(e1: &Exp, e2: &Exp, erase_proofs: bool) -> bool {
    is_alpha_eq_rec(
        e1,
        e2,
        &mut AlphaEqEnv {
            bound: vec![],
            take_proofs_irrelevant: erase_proofs,
            reduce_to_whnf: true,
            erase_subset_intro: erase_proofs,
        },
        &mut AlphaEqEnv {
            bound: vec![],
            take_proofs_irrelevant: erase_proofs,
            reduce_to_whnf: true,
            erase_subset_intro: erase_proofs,
        },
    )
}

fn exp_subst_child(e: &rc::Rc<Exp>, v: &Var, t: &Exp, parent_changed: &mut bool) -> rc::Rc<Exp> {
    let mut child_changed = false;
    let substituted = exp_subst_tracking(e, v, t, &mut child_changed);
    if child_changed {
        *parent_changed = true;
        rc::Rc::new(substituted)
    } else {
        e.clone()
    }
}

pub fn exp_subst(e: &Exp, v: &Var, t: &Exp) -> Exp {
    let mut changed = false;
    let substituted = exp_subst_tracking(e, v, t, &mut changed);
    if changed { substituted } else { e.clone() }
}

fn exp_subst_tracking(e: &Exp, v: &Var, t: &Exp, changed: &mut bool) -> Exp {
    match e {
        Exp::Sort(sort) => Exp::Sort(*sort),
        Exp::Var(var) => {
            if var.is_eq_ptr(v) {
                *changed = true;
                t.clone()
            } else {
                e.clone()
            }
        }
        Exp::Prod { var, ty, body } => {
            if var.is_eq_ptr(v) {
                Exp::Prod {
                    var: var.clone(),
                    ty: exp_subst_child(ty, v, t, changed),
                    body: body.clone(),
                }
            } else {
                Exp::Prod {
                    var: var.clone(),
                    ty: exp_subst_child(ty, v, t, changed),
                    body: exp_subst_child(body, v, t, changed),
                }
            }
        }
        Exp::Lam { var, ty, body } => {
            if var.is_eq_ptr(v) {
                Exp::Lam {
                    var: var.clone(),
                    ty: exp_subst_child(ty, v, t, changed),
                    body: body.clone(),
                }
            } else {
                Exp::Lam {
                    var: var.clone(),
                    ty: exp_subst_child(ty, v, t, changed),
                    body: exp_subst_child(body, v, t, changed),
                }
            }
        }
        Exp::App { func, arg } => Exp::App {
            func: exp_subst_child(func, v, t, changed),
            arg: exp_subst_child(arg, v, t, changed),
        },
        Exp::DefinedConstant(rc) => {
            let DefinedConstant { ty, body: inner } = rc.as_ref();
            // yet another RC
            Exp::DefinedConstant(rc::Rc::new(DefinedConstant {
                ty: exp_subst_tracking(ty, v, t, changed),
                body: exp_subst_tracking(inner, v, t, changed),
            }))
        }
        Exp::IndType {
            indspec: ty,
            parameters,
        } => Exp::IndType {
            indspec: ty.clone(),
            parameters: parameters
                .iter()
                .map(|arg| exp_subst_tracking(arg, v, t, changed))
                .collect(),
        },
        Exp::IndCtor {
            indspec: ty,
            idx,
            parameters: parameter,
        } => Exp::IndCtor {
            indspec: ty.clone(),
            idx: *idx,
            parameters: parameter
                .iter()
                .map(|arg| exp_subst_tracking(arg, v, t, changed))
                .collect(),
        },
        Exp::IndElim {
            indspec: ty,
            elim,
            return_type,
            cases,
        } => Exp::IndElim {
            indspec: ty.clone(),
            elim: exp_subst_child(elim, v, t, changed),
            return_type: exp_subst_child(return_type, v, t, changed),
            cases: cases
                .iter()
                .map(|case| exp_subst_tracking(case, v, t, changed))
                .collect(),
        },
        Exp::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => Exp::SubsetIntro {
            superset: exp_subst_child(superset, v, t, changed),
            subset: exp_subst_child(subset, v, t, changed),
            element: exp_subst_child(element, v, t, changed),
            proof: exp_subst_child(proof, v, t, changed),
        },
        Exp::PowerSet { set: exp } => Exp::PowerSet {
            set: exp_subst_child(exp, v, t, changed),
        },
        Exp::SubSet {
            var,
            set: exp,
            predicate,
        } => {
            if var.is_eq_ptr(v) {
                Exp::SubSet {
                    var: var.clone(),
                    set: exp_subst_child(exp, v, t, changed),
                    predicate: predicate.clone(),
                }
            } else {
                Exp::SubSet {
                    var: var.clone(),
                    set: exp_subst_child(exp, v, t, changed),
                    predicate: exp_subst_child(predicate, v, t, changed),
                }
            }
        }
        Exp::Pred {
            superset,
            subset,
            element,
        } => Exp::Pred {
            superset: exp_subst_child(superset, v, t, changed),
            subset: exp_subst_child(subset, v, t, changed),
            element: exp_subst_child(element, v, t, changed),
        },
        Exp::TypeLift { superset, subset } => Exp::TypeLift {
            superset: exp_subst_child(superset, v, t, changed),
            subset: exp_subst_child(subset, v, t, changed),
        },
        Exp::Equal { left, right } => Exp::Equal {
            left: exp_subst_child(left, v, t, changed),
            right: exp_subst_child(right, v, t, changed),
        },
        Exp::Exists { set: ty } => Exp::Exists {
            set: exp_subst_child(ty, v, t, changed),
        },
        Exp::TakeSet {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => Exp::TakeSet {
            domain: exp_subst_child(domain, v, t, changed),
            codomain: exp_subst_child(codomain, v, t, changed),
            map: exp_subst_child(map, v, t, changed),
            existence: exp_subst_child(existence, v, t, changed),
            uniqueness: exp_subst_child(uniqueness, v, t, changed),
        },
        Exp::TakeProp {
            domain,
            proposition,
            map,
            existence,
        } => Exp::TakeProp {
            domain: exp_subst_child(domain, v, t, changed),
            proposition: exp_subst_child(proposition, v, t, changed),
            map: exp_subst_child(map, v, t, changed),
            existence: exp_subst_child(existence, v, t, changed),
        },
        Exp::ExistsIntro { element, set } => Exp::ExistsIntro {
            element: exp_subst_child(element, v, t, changed),
            set: exp_subst_child(set, v, t, changed),
        },
        Exp::SubsetElim {
            element,
            subset,
            superset,
        } => Exp::SubsetElim {
            element: exp_subst_child(element, v, t, changed),
            subset: exp_subst_child(subset, v, t, changed),
            superset: exp_subst_child(superset, v, t, changed),
        },
        Exp::IdRefl { element } => Exp::IdRefl {
            element: exp_subst_child(element, v, t, changed),
        },
        Exp::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
            base,
            equality,
        } => Exp::IdElim {
            left: exp_subst_child(left, v, t, changed),
            right: exp_subst_child(right, v, t, changed),
            ty: exp_subst_child(ty, v, t, changed),
            var: var.clone(),
            predicate: if !v.is_eq_ptr(var) {
                exp_subst_child(predicate, v, t, changed)
            } else {
                predicate.clone()
            },
            base: exp_subst_child(base, v, t, changed),
            equality: exp_subst_child(equality, v, t, changed),
        },
        Exp::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => Exp::TakeEq {
            func: exp_subst_child(func, v, t, changed),
            domain: exp_subst_child(domain, v, t, changed),
            codomain: exp_subst_child(codomain, v, t, changed),
            element: exp_subst_child(element, v, t, changed),
            existence: exp_subst_child(existence, v, t, changed),
            uniqueness: exp_subst_child(uniqueness, v, t, changed),
        },
    }
}

pub fn exp_subst_map(e: &Exp, v: &[(Var, Exp)]) -> Exp {
    let mut res = e.clone();
    for (var, exp) in v.iter() {
        res = exp_subst(&res, var, exp);
    }
    res
}

/// Expose the computational content of `SubsetIntro` recursively.
///
/// Take constructors remain checked terms here. Their proof irrelevance is
/// handled only by `erased_convertible`.
pub fn erase(e: &Exp) -> Exp {
    match e {
        Exp::Sort(sort) => Exp::Sort(*sort),
        Exp::Var(var) => Exp::Var(var.clone()),
        Exp::Prod { var, ty, body } => Exp::Prod {
            var: var.clone(),
            ty: rc::Rc::new(erase(ty)),
            body: rc::Rc::new(erase(body)),
        },
        Exp::Lam { var, ty, body } => Exp::Lam {
            var: var.clone(),
            ty: rc::Rc::new(erase(ty)),
            body: rc::Rc::new(erase(body)),
        },
        Exp::App { func, arg } => Exp::App {
            func: rc::Rc::new(erase(func)),
            arg: rc::Rc::new(erase(arg)),
        },
        // Defined constants are transparent.  Unfolding here ensures that a
        // certificate stored in a checked definition is erased as well.
        Exp::DefinedConstant(rc) => erase(&rc.body),
        Exp::IndType {
            indspec,
            parameters,
        } => Exp::IndType {
            indspec: indspec.clone(),
            parameters: parameters.iter().map(erase).collect(),
        },
        Exp::IndCtor {
            indspec,
            parameters,
            idx,
        } => Exp::IndCtor {
            indspec: indspec.clone(),
            parameters: parameters.iter().map(erase).collect(),
            idx: *idx,
        },
        Exp::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => Exp::IndElim {
            indspec: indspec.clone(),
            elim: rc::Rc::new(erase(elim)),
            return_type: rc::Rc::new(erase(return_type)),
            cases: cases.iter().map(erase).collect(),
        },
        Exp::SubsetIntro { element, .. } => erase(element),
        Exp::PowerSet { set } => Exp::PowerSet {
            set: rc::Rc::new(erase(set)),
        },
        Exp::SubSet {
            var,
            set,
            predicate,
        } => Exp::SubSet {
            var: var.clone(),
            set: rc::Rc::new(erase(set)),
            predicate: rc::Rc::new(erase(predicate)),
        },
        Exp::Pred {
            superset,
            subset,
            element,
        } => Exp::Pred {
            superset: rc::Rc::new(erase(superset)),
            subset: rc::Rc::new(erase(subset)),
            element: rc::Rc::new(erase(element)),
        },
        Exp::TypeLift { superset, subset } => Exp::TypeLift {
            superset: rc::Rc::new(erase(superset)),
            subset: rc::Rc::new(erase(subset)),
        },
        Exp::Equal { left, right } => Exp::Equal {
            left: rc::Rc::new(erase(left)),
            right: rc::Rc::new(erase(right)),
        },
        Exp::Exists { set } => Exp::Exists {
            set: rc::Rc::new(erase(set)),
        },
        Exp::TakeSet {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => Exp::TakeSet {
            domain: rc::Rc::new(erase(domain)),
            codomain: rc::Rc::new(erase(codomain)),
            map: rc::Rc::new(erase(map)),
            existence: rc::Rc::new(erase(existence)),
            uniqueness: rc::Rc::new(erase(uniqueness)),
        },
        Exp::TakeProp {
            domain,
            proposition,
            map,
            existence,
        } => Exp::TakeProp {
            domain: rc::Rc::new(erase(domain)),
            proposition: rc::Rc::new(erase(proposition)),
            map: rc::Rc::new(erase(map)),
            existence: rc::Rc::new(erase(existence)),
        },
        Exp::ExistsIntro { element, set } => Exp::ExistsIntro {
            element: rc::Rc::new(erase(element)),
            set: rc::Rc::new(erase(set)),
        },
        Exp::SubsetElim {
            element,
            subset,
            superset,
        } => Exp::SubsetElim {
            element: rc::Rc::new(erase(element)),
            subset: rc::Rc::new(erase(subset)),
            superset: rc::Rc::new(erase(superset)),
        },
        Exp::IdRefl { element } => Exp::IdRefl {
            element: rc::Rc::new(erase(element)),
        },
        Exp::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
            base,
            equality,
        } => Exp::IdElim {
            left: rc::Rc::new(erase(left)),
            right: rc::Rc::new(erase(right)),
            ty: rc::Rc::new(erase(ty)),
            var: var.clone(),
            predicate: rc::Rc::new(erase(predicate)),
            base: rc::Rc::new(erase(base)),
            equality: rc::Rc::new(erase(equality)),
        },
        Exp::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => Exp::TakeEq {
            func: rc::Rc::new(erase(func)),
            domain: rc::Rc::new(erase(domain)),
            codomain: rc::Rc::new(erase(codomain)),
            element: rc::Rc::new(erase(element)),
            existence: rc::Rc::new(erase(existence)),
            uniqueness: rc::Rc::new(erase(uniqueness)),
        },
    }
}

pub fn exp_reduce_if_top(e: &Exp) -> Option<Exp> {
    match e {
        // ((x: A) => B) a  ==>  B[x := a]
        Exp::App { func, arg } => {
            if let Exp::Lam { var, ty: _, body } = func.as_ref() {
                Some(exp_subst(body, var, arg))
            } else {
                None
            }
        }
        Exp::DefinedConstant(rc) => {
            let DefinedConstant { ty: _, body: inner } = rc.as_ref();
            Some(inner.clone())
        }
        // Pred(A, {x: B | P}, a)  ==>  P[x := a]
        Exp::Pred {
            superset: _,
            subset,
            element,
        } => {
            if let Exp::SubSet {
                var,
                set: _,
                predicate,
            } = subset.as_ref()
            {
                Some(exp_subst(predicate, var, element))
            } else {
                None
            }
        }
        Exp::IndElim { .. } => inductive_type_elim_reduce(e).ok(),
        _ => None,
    }
}

/// Reduce only along the elimination spine needed to reveal the outer
/// constructor. Unlike `reduce_one`, this does not search unrelated children.
fn exp_reduce_head_once(e: &Exp, erase_subset_intro: bool) -> Option<Exp> {
    if erase_subset_intro && let Exp::SubsetIntro { element, .. } = e {
        return Some(element.as_ref().clone());
    }

    if let Some(reduced) = exp_reduce_if_top(e) {
        return Some(reduced);
    }

    match e {
        Exp::App { func, arg } => match exp_whnf_with_mode(func, erase_subset_intro) {
            Cow::Borrowed(_) => None,
            Cow::Owned(func) => Some(Exp::App {
                func: rc::Rc::new(func),
                arg: arg.clone(),
            }),
        },
        Exp::Pred {
            superset,
            subset,
            element,
        } => match exp_whnf_with_mode(subset, erase_subset_intro) {
            Cow::Borrowed(_) => None,
            Cow::Owned(subset) => Some(Exp::Pred {
                superset: superset.clone(),
                subset: rc::Rc::new(subset),
                element: element.clone(),
            }),
        },
        Exp::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => match exp_whnf_with_mode(elim, erase_subset_intro) {
            Cow::Borrowed(_) => None,
            Cow::Owned(elim) => Some(Exp::IndElim {
                indspec: indspec.clone(),
                elim: rc::Rc::new(elim),
                return_type: return_type.clone(),
                cases: cases.clone(),
            }),
        },
        _ => None,
    }
}

/// Weak-head normalize an expression without reducing under constructors or
/// traversing arguments that are not needed to expose the head.
fn exp_whnf_with_mode<'a>(e: &'a Exp, erase_subset_intro: bool) -> Cow<'a, Exp> {
    let mut current = Cow::Borrowed(e);
    loop {
        match exp_reduce_head_once(current.as_ref(), erase_subset_intro) {
            Some(next) => current = Cow::Owned(next),
            None => return current,
        }
    }
}

pub fn reduce_one(e: &Exp) -> Option<Exp> {
    if let Some(e) = exp_reduce_if_top(e) {
        return Some(e);
    }

    // challenge reduce exp if changed == true
    // return if [Some(reduced) = reduce(exp)]
    //    then {changed := true, recude}
    //    else exp
    let mut changed = false;
    let mut reduce_if = |e: &Exp| -> Exp {
        if !changed && let Some(reduced) = reduce_one(e) {
            changed = true;
            return reduced;
        }
        e.clone()
    };

    match e {
        Exp::Sort(_) => None,
        Exp::Var(_) => None,
        Exp::Prod { var, ty, body } => {
            let ty = reduce_if(ty);
            let body = reduce_if(body);

            changed.then_some(Exp::Prod {
                var: var.clone(),
                ty: rc::Rc::new(ty),
                body: rc::Rc::new(body),
            })
        }
        Exp::Lam { var, ty, body } => {
            let ty = reduce_if(ty);
            let body = reduce_if(body);

            changed.then_some(Exp::Lam {
                var: var.clone(),
                ty: rc::Rc::new(ty),
                body: rc::Rc::new(body),
            })
        }
        Exp::App { func, arg } => {
            let func = reduce_if(func);
            let arg = reduce_if(arg);

            changed.then_some(Exp::App {
                func: rc::Rc::new(func),
                arg: rc::Rc::new(arg),
            })
        }
        Exp::DefinedConstant(_) => {
            unreachable!("we already called exp_reduce_if_top")
        }
        Exp::IndType {
            indspec: ty,
            parameters,
        } => {
            let parameters = parameters.iter().map(reduce_if).collect::<Vec<_>>();

            changed.then_some(Exp::IndType {
                indspec: ty.clone(),
                parameters,
            })
        }
        Exp::IndCtor {
            indspec: ty,
            idx,
            parameters: parameter,
        } => {
            let parameters = parameter.iter().map(reduce_if).collect::<Vec<_>>();

            changed.then_some(Exp::IndCtor {
                indspec: ty.clone(),
                idx: *idx,
                parameters,
            })
        }
        Exp::IndElim {
            indspec: ty,
            elim,
            return_type,
            cases,
        } => {
            let elim = reduce_if(elim);
            let return_type = reduce_if(return_type);
            let cases = cases.iter().map(reduce_if).collect::<Vec<_>>();

            changed.then_some(Exp::IndElim {
                indspec: ty.clone(),
                elim: rc::Rc::new(elim),
                return_type: rc::Rc::new(return_type),
                cases,
            })
        }
        Exp::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => {
            let superset = reduce_if(superset);
            let subset = reduce_if(subset);
            let element = reduce_if(element);
            let proof = reduce_if(proof);

            changed.then_some(Exp::SubsetIntro {
                superset: rc::Rc::new(superset),
                subset: rc::Rc::new(subset),
                element: rc::Rc::new(element),
                proof: rc::Rc::new(proof),
            })
        }
        Exp::PowerSet { set: exp } => {
            let exp = reduce_if(exp);
            changed.then_some(Exp::PowerSet {
                set: rc::Rc::new(exp),
            })
        }
        Exp::SubSet {
            var,
            set: exp,
            predicate,
        } => {
            let exp = reduce_if(exp);
            let predicate = reduce_if(predicate);

            changed.then_some(Exp::SubSet {
                var: var.clone(),
                set: rc::Rc::new(exp),
                predicate: rc::Rc::new(predicate),
            })
        }
        Exp::Pred {
            superset,
            subset,
            element,
        } => {
            let superset = reduce_if(superset);
            let subset = reduce_if(subset);
            let element = reduce_if(element);

            changed.then_some(Exp::Pred {
                superset: rc::Rc::new(superset),
                subset: rc::Rc::new(subset),
                element: rc::Rc::new(element),
            })
        }
        Exp::TypeLift { superset, subset } => {
            let superset = reduce_if(superset);
            let subset = reduce_if(subset);

            changed.then_some(Exp::TypeLift {
                superset: rc::Rc::new(superset),
                subset: rc::Rc::new(subset),
            })
        }
        Exp::Equal { left, right } => {
            let left = reduce_if(left);
            let right = reduce_if(right);

            changed.then_some(Exp::Equal {
                left: rc::Rc::new(left),
                right: rc::Rc::new(right),
            })
        }
        Exp::Exists { set: ty } => {
            let ty = reduce_if(ty);
            changed.then_some(Exp::Exists {
                set: rc::Rc::new(ty),
            })
        }
        Exp::TakeSet {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => {
            let domain = reduce_if(domain);
            let codomain = reduce_if(codomain);
            let map = reduce_if(map);
            let existence = reduce_if(existence);
            let uniqueness = reduce_if(uniqueness);

            changed.then_some(Exp::TakeSet {
                domain: rc::Rc::new(domain),
                codomain: rc::Rc::new(codomain),
                map: rc::Rc::new(map),
                existence: rc::Rc::new(existence),
                uniqueness: rc::Rc::new(uniqueness),
            })
        }
        Exp::TakeProp {
            domain,
            proposition,
            map,
            existence,
        } => {
            let domain = reduce_if(domain);
            let proposition = reduce_if(proposition);
            let map = reduce_if(map);
            let existence = reduce_if(existence);

            changed.then_some(Exp::TakeProp {
                domain: rc::Rc::new(domain),
                proposition: rc::Rc::new(proposition),
                map: rc::Rc::new(map),
                existence: rc::Rc::new(existence),
            })
        }
        Exp::ExistsIntro { element, set } => {
            let element = reduce_if(element);
            let set = reduce_if(set);
            changed.then_some(Exp::ExistsIntro {
                element: rc::Rc::new(element),
                set: rc::Rc::new(set),
            })
        }
        Exp::SubsetElim {
            element,
            subset,
            superset,
        } => {
            let element = reduce_if(element);
            let subset = reduce_if(subset);
            let superset = reduce_if(superset);
            changed.then_some(Exp::SubsetElim {
                element: rc::Rc::new(element),
                subset: rc::Rc::new(subset),
                superset: rc::Rc::new(superset),
            })
        }
        Exp::IdRefl { element } => {
            let element = reduce_if(element);
            changed.then_some(Exp::IdRefl {
                element: rc::Rc::new(element),
            })
        }
        Exp::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
            base,
            equality,
        } => {
            let left = reduce_if(left);
            let right = reduce_if(right);
            let ty = reduce_if(ty);
            let predicate = reduce_if(predicate);
            let base = reduce_if(base);
            let equality = reduce_if(equality);
            changed.then_some(Exp::IdElim {
                left: rc::Rc::new(left),
                right: rc::Rc::new(right),
                ty: rc::Rc::new(ty),
                var: var.clone(),
                predicate: rc::Rc::new(predicate),
                base: rc::Rc::new(base),
                equality: rc::Rc::new(equality),
            })
        }
        Exp::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => {
            let func = reduce_if(func);
            let domain = reduce_if(domain);
            let codomain = reduce_if(codomain);
            let element = reduce_if(element);
            let existence = reduce_if(existence);
            let uniqueness = reduce_if(uniqueness);
            changed.then_some(Exp::TakeEq {
                func: rc::Rc::new(func),
                domain: rc::Rc::new(domain),
                codomain: rc::Rc::new(codomain),
                element: rc::Rc::new(element),
                existence: rc::Rc::new(existence),
                uniqueness: rc::Rc::new(uniqueness),
            })
        }
    }
}

pub fn normalize(e: &Exp) -> Exp {
    let mut current = e.clone();
    while let Some(next) = reduce_one(&current) {
        current = next;
    }
    current
}

/// Definitional conversion without erasing refinement certificates.
pub fn convertible(e1: &Exp, e2: &Exp) -> bool {
    exp_is_convertible_with_mode(e1, e2, false)
}

/// Computational normal form. Erasure precedes normalization so that
/// removing a `SubsetIntro` certificate may expose another reduction.
pub fn erased_normal(e: &Exp) -> Exp {
    normalize(&erase(e))
}

/// Computational equality modulo `SubsetIntro` certificates and the proof
/// fields of checked Take constructors.
///
/// This function deliberately does not type-check its arguments.  Typing
/// rules using it must establish well-typedness independently.
pub fn erased_convertible(e1: &Exp, e2: &Exp) -> bool {
    exp_is_convertible_with_mode(e1, e2, true)
}

/// Reveal the outer type constructor and make `SubsetIntro` transparent only
/// along its elimination spine. Unrelated children are not normalized.
pub(crate) fn type_head_normal(ty: &Exp) -> Exp {
    exp_whnf_with_mode(ty, true).into_owned()
}

/// Observe a product through refinement carriers and transparent type
/// annotations. No recursively erased term is produced.
pub(crate) fn expose_product(ty: &Exp) -> Option<(Var, Exp, Exp)> {
    let mut current = type_head_normal(ty);
    loop {
        match current {
            Exp::Prod { var, ty, body } => {
                return Some((
                    var,
                    rc::Rc::unwrap_or_clone(ty),
                    rc::Rc::unwrap_or_clone(body),
                ));
            }
            Exp::TypeLift { superset, .. } => current = type_head_normal(&superset),
            _ => return None,
        }
    }
}

/// Follow explicit refinement carriers without recursively erasing the term.
/// Follow explicit refinement carriers to the underlying type.
///
/// Unlike `erase`, this is a type-directed head observation: it does not make
/// refinement introduction and its carrier interchangeable throughout
/// conversion.
pub(crate) fn base_carrier(ty: &Exp) -> Exp {
    let mut current = type_head_normal(ty);
    loop {
        match current {
            Exp::TypeLift { superset, .. } => current = type_head_normal(&superset),
            _ => return current,
        }
    }
}

/// Find a common ambient carrier for two already inferred types.
///
/// This is a syntactic calculation: `TypeLift` contains its `superset`
/// explicitly, and conversion itself needs no context. The caller must first
/// establish that both inputs are well typed in the same context, and remains
/// responsible for checking that the returned carrier has a set sort.
pub(crate) fn common_ambient_carrier(left_ty: &Exp, right_ty: &Exp) -> Option<Exp> {
    let left_carrier = base_carrier(left_ty);
    let right_carrier = base_carrier(right_ty);
    erased_convertible(&left_carrier, &right_carrier).then_some(left_carrier)
}

/// Test the one-way refinement weakening relation, propagating it through
/// product codomains.
pub(crate) fn can_weaken_to(inferred: &Exp, expected: &Exp) -> bool {
    if erased_convertible(inferred, expected) {
        return true;
    }

    let inferred = type_head_normal(inferred);
    let expected = type_head_normal(expected);
    match (&inferred, &expected) {
        (Exp::TypeLift { superset, .. }, expected) => can_weaken_to(superset, expected),
        (
            Exp::Prod {
                var: inferred_var,
                ty: inferred_domain,
                body: inferred_body,
            },
            Exp::Prod {
                var: expected_var,
                ty: expected_domain,
                body: expected_body,
            },
        ) if erased_convertible(inferred_domain, expected_domain) => {
            let expected_body =
                exp_subst(expected_body, expected_var, &Exp::Var(inferred_var.clone()));
            can_weaken_to(inferred_body, &expected_body)
        }
        _ => false,
    }
}

impl Exp {
    pub fn subst(&self, subst_mapping: &[(Var, Exp)]) -> Exp {
        exp_subst_map(self, subst_mapping)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{app, lam, prod, var, var_str};
    #[test]
    fn reduce_test() {
        // ((z: X) => z) Y)
        let ty = app!(lam!(var!("z"), var_str!("X"), var_str!("z")), var_str!("Y"));
        let reduced = normalize(&ty);
        println!("reduced: {:?}", reduced);
        // (x: ty) -> y
        let e = prod!(var!("x"), ty, var_str!("y"));
        let reduced = reduce_one(&e).unwrap();
        // (x: Y) -> y
        println!("reduced: {:?}", reduced);
    }
}
