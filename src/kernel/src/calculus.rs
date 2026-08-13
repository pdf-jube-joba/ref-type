use std::rc;

use crate::inductive::inductive_type_elim_reduce;

use super::exp::*;

// same variable as ptr
pub fn exp_strict_equivalence(e1: &Exp, e2: &Exp) -> bool {
    match (e1, e2) {
        (Exp::Sort(s1), Exp::Sort(s2)) => s1 == s2,
        (Exp::Var(v1), Exp::Var(v2)) => v1.is_eq_ptr(v2),
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
            var1.is_eq_ptr(var2)
                && exp_strict_equivalence(ty1, ty2)
                && exp_strict_equivalence(body1, body2)
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
            var1.is_eq_ptr(var2)
                && exp_strict_equivalence(ty1, ty2)
                && exp_strict_equivalence(body1, body2)
        }
        (Exp::App { func: f1, arg: a1 }, Exp::App { func: f2, arg: a2 }) => {
            exp_strict_equivalence(f1, f2) && exp_strict_equivalence(a1, a2)
        }
        (Exp::DefinedConstant(rc1), Exp::DefinedConstant(rc2)) => std::rc::Rc::ptr_eq(rc1, rc2),
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
                    .all(|(a1, a2)| exp_strict_equivalence(a1, a2))
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
                    .all(|(a1, a2)| exp_strict_equivalence(a1, a2))
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
                && exp_strict_equivalence(elim1, elim2)
                && exp_strict_equivalence(ret1, ret2)
                && cases1.len() == cases2.len()
                && cases1
                    .iter()
                    .zip(cases2.iter())
                    .all(|(c1, c2)| exp_strict_equivalence(c1, c2))
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
            exp_strict_equivalence(a1, a2)
                && exp_strict_equivalence(s1, s2)
                && exp_strict_equivalence(e1, e2)
                && exp_strict_equivalence(p1, p2)
        }
        (Exp::PowerSet { set: e1 }, Exp::PowerSet { set: e2 }) => exp_strict_equivalence(e1, e2),
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
            var1.is_eq_ptr(var2) && exp_strict_equivalence(e1, e2) && exp_strict_equivalence(p1, p2)
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
            exp_strict_equivalence(s1, s2)
                && exp_strict_equivalence(sub1, sub2)
                && exp_strict_equivalence(e1, e2)
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
        ) => exp_strict_equivalence(s1, s2) && exp_strict_equivalence(sub1, sub2),
        (
            Exp::Equal {
                left: l1,
                right: r1,
            },
            Exp::Equal {
                left: l2,
                right: r2,
            },
        ) => exp_strict_equivalence(l1, l2) && exp_strict_equivalence(r1, r2),
        (Exp::Exists { set: set1 }, Exp::Exists { set: set2 }) => {
            exp_strict_equivalence(set1, set2)
        }
        (
            Exp::Take {
                domain: d1,
                codomain: c1,
                map: m1,
                existence: e1,
                uniqueness: u1,
            },
            Exp::Take {
                domain: d2,
                codomain: c2,
                map: m2,
                existence: e2,
                uniqueness: u2,
            },
        ) => {
            exp_strict_equivalence(d1, d2)
                && exp_strict_equivalence(c1, c2)
                && exp_strict_equivalence(m1, m2)
                && exp_strict_equivalence(e1, e2)
                && option_exp_equivalence(u1.as_deref(), u2.as_deref())
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
        ) => exp_strict_equivalence(e1, e2) && exp_strict_equivalence(s1, s2),
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
            exp_strict_equivalence(e1, e2)
                && exp_strict_equivalence(b1, b2)
                && exp_strict_equivalence(s1, s2)
        }
        (Exp::IdRefl { element: e1 }, Exp::IdRefl { element: e2 }) => {
            exp_strict_equivalence(e1, e2)
        }
        (
            Exp::IdElim {
                left: l1,
                right: r1,
                ty: t1,
                var: v1,
                predicate: p1,
                base: b1,
                equality: e1,
            },
            Exp::IdElim {
                left: l2,
                right: r2,
                ty: t2,
                var: v2,
                predicate: p2,
                base: b2,
                equality: e2,
            },
        ) => {
            v1.is_eq_ptr(v2)
                && [
                    (&**l1, &**l2),
                    (&**r1, &**r2),
                    (&**t1, &**t2),
                    (&**p1, &**p2),
                    (&**b1, &**b2),
                    (&**e1, &**e2),
                ]
                .into_iter()
                .all(|(a, b)| exp_strict_equivalence(a, b))
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
            [
                (&**f1, &**f2),
                (&**d1, &**d2),
                (&**c1, &**c2),
                (&**e1, &**e2),
                (&**x1, &**x2),
            ]
            .into_iter()
            .all(|(a, b)| exp_strict_equivalence(a, b))
                && option_exp_equivalence(u1.as_deref(), u2.as_deref())
        }
        _ => false,
    }
}

fn option_exp_equivalence(e1: Option<&Exp>, e2: Option<&Exp>) -> bool {
    match (e1, e2) {
        (Some(e1), Some(e2)) => exp_strict_equivalence(e1, e2),
        (None, None) => true,
        _ => false,
    }
}

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
        Exp::Take {
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
                || uniqueness
                    .as_deref()
                    .is_some_and(|p| exp_contains_as_freevar(p, v))
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
                || uniqueness
                    .as_deref()
                    .is_some_and(|p| exp_contains_as_freevar(p, v))
        }
    }
}

// WARNING we ignore raw proof terms (it behaves like ProofLater(p))
// i.e. ctx |- p1, p2: P: \Prop => p1 == p2
fn is_alpha_eq_rec(e1: &Exp, e2: &Exp, env1: &mut Vec<Var>, env2: &mut Vec<Var>) -> bool {
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
            Exp::Take {
                domain: d1,
                codomain: c1,
                map: m1,
                existence: e1,
                uniqueness: u1,
            },
            Exp::Take {
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
                && is_alpha_eq_rec(e1, e2, env1, env2)
                && option_alpha_eq(u1.as_deref(), u2.as_deref(), env1, env2)
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
                && is_alpha_eq_rec(x1, x2, env1, env2)
                && option_alpha_eq(u1.as_deref(), u2.as_deref(), env1, env2)
        }
        _ => false,
    }
}

fn option_alpha_eq(
    e1: Option<&Exp>,
    e2: Option<&Exp>,
    env1: &mut Vec<Var>,
    env2: &mut Vec<Var>,
) -> bool {
    match (e1, e2) {
        (Some(e1), Some(e2)) => is_alpha_eq_rec(e1, e2, env1, env2),
        (None, None) => true,
        _ => false,
    }
}

pub fn exp_is_alpha_eq(e1: &Exp, e2: &Exp) -> bool {
    is_alpha_eq_rec(e1, e2, &mut vec![], &mut vec![])
}

pub fn ctx_is_alpha_eq(ctx1: &Context, ctx2: &Context) -> bool {
    if ctx1.len() != ctx2.len() {
        return false;
    }

    let mut env1 = vec![];
    let mut env2 = vec![];

    for ((var1, exp1), (var2, exp2)) in ctx1.iter().zip(ctx2.iter()) {
        if !is_alpha_eq_rec(exp1, exp2, &mut env1, &mut env2) {
            return false;
        }
        env1.push(var1.clone());
        env2.push(var2.clone());
    }

    true
}

pub fn exp_is_alpha_eq_under_ctx(ctx1: &Context, t1: &Exp, ctx2: &Context, t2: &Exp) -> bool {
    if !ctx_is_alpha_eq(ctx1, ctx2) {
        return false;
    }

    let mut env1 = vec![];
    let mut env2 = vec![];

    for (var1, _) in ctx1.iter() {
        env1.push(var1.clone());
    }
    for (var2, _) in ctx2.iter() {
        env2.push(var2.clone());
    }

    is_alpha_eq_rec(t1, t2, &mut env1, &mut env2)
}

pub fn exp_subst(e: &Exp, v: &Var, t: &Exp) -> Exp {
    match e {
        Exp::Sort(sort) => Exp::Sort(*sort),
        Exp::Var(var) => {
            if var.is_eq_ptr(v) {
                t.clone()
            } else {
                e.clone()
            }
        }
        Exp::Prod { var, ty, body } => {
            if var.is_eq_ptr(v) {
                Exp::Prod {
                    var: var.clone(),
                    ty: Box::new(exp_subst(ty, v, t)),
                    body: body.clone(),
                }
            } else {
                Exp::Prod {
                    var: var.clone(),
                    ty: Box::new(exp_subst(ty, v, t)),
                    body: Box::new(exp_subst(body, v, t)),
                }
            }
        }
        Exp::Lam { var, ty, body } => {
            if var.is_eq_ptr(v) {
                Exp::Lam {
                    var: var.clone(),
                    ty: Box::new(exp_subst(ty, v, t)),
                    body: body.clone(),
                }
            } else {
                Exp::Lam {
                    var: var.clone(),
                    ty: Box::new(exp_subst(ty, v, t)),
                    body: Box::new(exp_subst(body, v, t)),
                }
            }
        }
        Exp::App { func, arg } => Exp::App {
            func: Box::new(exp_subst(func, v, t)),
            arg: Box::new(exp_subst(arg, v, t)),
        },
        Exp::DefinedConstant(rc) => {
            let DefinedConstant { ty, body: inner } = rc.as_ref();
            // yet another RC
            Exp::DefinedConstant(rc::Rc::new(DefinedConstant {
                ty: exp_subst(ty, v, t),
                body: exp_subst(inner, v, t),
            }))
        }
        Exp::IndType {
            indspec: ty,
            parameters,
        } => Exp::IndType {
            indspec: ty.clone(),
            parameters: parameters.iter().map(|arg| exp_subst(arg, v, t)).collect(),
        },
        Exp::IndCtor {
            indspec: ty,
            idx,
            parameters: parameter,
        } => Exp::IndCtor {
            indspec: ty.clone(),
            idx: *idx,
            parameters: parameter.iter().map(|arg| exp_subst(arg, v, t)).collect(),
        },
        Exp::IndElim {
            indspec: ty,
            elim,
            return_type,
            cases,
        } => Exp::IndElim {
            indspec: ty.clone(),
            elim: Box::new(exp_subst(elim, v, t)),
            return_type: Box::new(exp_subst(return_type, v, t)),
            cases: cases.iter().map(|case| exp_subst(case, v, t)).collect(),
        },
        Exp::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => Exp::SubsetIntro {
            superset: Box::new(exp_subst(superset, v, t)),
            subset: Box::new(exp_subst(subset, v, t)),
            element: Box::new(exp_subst(element, v, t)),
            proof: Box::new(exp_subst(proof, v, t)),
        },
        Exp::PowerSet { set: exp } => Exp::PowerSet {
            set: Box::new(exp_subst(exp, v, t)),
        },
        Exp::SubSet {
            var,
            set: exp,
            predicate,
        } => {
            if var.is_eq_ptr(v) {
                Exp::SubSet {
                    var: var.clone(),
                    set: Box::new(exp_subst(exp, v, t)),
                    predicate: predicate.clone(),
                }
            } else {
                Exp::SubSet {
                    var: var.clone(),
                    set: Box::new(exp_subst(exp, v, t)),
                    predicate: Box::new(exp_subst(predicate, v, t)),
                }
            }
        }
        Exp::Pred {
            superset,
            subset,
            element,
        } => Exp::Pred {
            superset: Box::new(exp_subst(superset, v, t)),
            subset: Box::new(exp_subst(subset, v, t)),
            element: Box::new(exp_subst(element, v, t)),
        },
        Exp::TypeLift { superset, subset } => Exp::TypeLift {
            superset: Box::new(exp_subst(superset, v, t)),
            subset: Box::new(exp_subst(subset, v, t)),
        },
        Exp::Equal { left, right } => Exp::Equal {
            left: Box::new(exp_subst(left, v, t)),
            right: Box::new(exp_subst(right, v, t)),
        },
        Exp::Exists { set: ty } => Exp::Exists {
            set: Box::new(exp_subst(ty, v, t)),
        },
        Exp::Take {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => Exp::Take {
            domain: Box::new(exp_subst(domain, v, t)),
            codomain: Box::new(exp_subst(codomain, v, t)),
            map: Box::new(exp_subst(map, v, t)),
            existence: Box::new(exp_subst(existence, v, t)),
            uniqueness: uniqueness.as_deref().map(|p| Box::new(exp_subst(p, v, t))),
        },
        Exp::ExistsIntro { element, set } => Exp::ExistsIntro {
            element: Box::new(exp_subst(element, v, t)),
            set: Box::new(exp_subst(set, v, t)),
        },
        Exp::SubsetElim {
            element,
            subset,
            superset,
        } => Exp::SubsetElim {
            element: Box::new(exp_subst(element, v, t)),
            subset: Box::new(exp_subst(subset, v, t)),
            superset: Box::new(exp_subst(superset, v, t)),
        },
        Exp::IdRefl { element } => Exp::IdRefl {
            element: Box::new(exp_subst(element, v, t)),
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
            left: Box::new(exp_subst(left, v, t)),
            right: Box::new(exp_subst(right, v, t)),
            ty: Box::new(exp_subst(ty, v, t)),
            var: var.clone(),
            predicate: if !v.is_eq_ptr(var) {
                Box::new(exp_subst(predicate, v, t))
            } else {
                predicate.clone()
            },
            base: Box::new(exp_subst(base, v, t)),
            equality: Box::new(exp_subst(equality, v, t)),
        },
        Exp::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => Exp::TakeEq {
            func: Box::new(exp_subst(func, v, t)),
            domain: Box::new(exp_subst(domain, v, t)),
            codomain: Box::new(exp_subst(codomain, v, t)),
            element: Box::new(exp_subst(element, v, t)),
            existence: Box::new(exp_subst(existence, v, t)),
            uniqueness: uniqueness.as_deref().map(|p| Box::new(exp_subst(p, v, t))),
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

// any bindings in e should be renamed to avoid some problems
// free variable is not affected (ptr_copy)
pub fn exp_alpha_conversion(e: &Exp) -> Exp {
    match e {
        Exp::Sort(sort) => Exp::Sort(*sort),
        Exp::Var(var) => Exp::Var(var.clone()),
        Exp::Prod { var, ty, body } => {
            let new_var = Var::new(var.as_str());
            Exp::Prod {
                var: new_var.clone(),
                ty: Box::new(exp_alpha_conversion(ty)),
                body: Box::new(exp_subst(
                    &exp_alpha_conversion(body),
                    var,
                    &Exp::Var(new_var),
                )),
            }
        }
        Exp::Lam { var, ty, body } => {
            let new_var = Var::new(var.as_str());
            Exp::Lam {
                var: new_var.clone(),
                ty: Box::new(exp_alpha_conversion(ty)),
                body: Box::new(exp_subst(
                    &exp_alpha_conversion(body),
                    var,
                    &Exp::Var(new_var),
                )),
            }
        }
        Exp::App { func, arg } => Exp::App {
            func: Box::new(exp_alpha_conversion(func)),
            arg: Box::new(exp_alpha_conversion(arg)),
        },
        Exp::DefinedConstant(rc) => {
            // TODO?: another RC?
            Exp::DefinedConstant(std::rc::Rc::clone(rc))
        }
        Exp::IndType {
            indspec: ty,
            parameters,
        } => Exp::IndType {
            indspec: ty.clone(),
            parameters: parameters.iter().map(exp_alpha_conversion).collect(),
        },
        Exp::IndCtor {
            indspec: ty,
            idx,
            parameters: parameter,
        } => Exp::IndCtor {
            indspec: ty.clone(),
            idx: *idx,
            parameters: parameter.iter().map(exp_alpha_conversion).collect(),
        },
        Exp::IndElim {
            indspec: ty,
            elim,
            return_type,
            cases,
        } => Exp::IndElim {
            indspec: ty.clone(),
            elim: Box::new(exp_alpha_conversion(elim)),
            return_type: Box::new(exp_alpha_conversion(return_type)),
            cases: cases.iter().map(exp_alpha_conversion).collect(),
        },
        Exp::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => Exp::SubsetIntro {
            superset: Box::new(exp_alpha_conversion(superset)),
            subset: Box::new(exp_alpha_conversion(subset)),
            element: Box::new(exp_alpha_conversion(element)),
            proof: Box::new(exp_alpha_conversion(proof)),
        },
        Exp::PowerSet { set: exp } => Exp::PowerSet {
            set: Box::new(exp_alpha_conversion(exp)),
        },
        Exp::SubSet {
            var,
            set: exp,
            predicate,
        } => {
            let new_var = Var::new(var.as_str());
            Exp::SubSet {
                var: new_var.clone(),
                set: Box::new(exp_alpha_conversion(exp)),
                predicate: Box::new(exp_subst(
                    &exp_alpha_conversion(predicate),
                    var,
                    &Exp::Var(new_var),
                )),
            }
        }
        Exp::Pred {
            superset,
            subset,
            element,
        } => Exp::Pred {
            superset: Box::new(exp_alpha_conversion(superset)),
            subset: Box::new(exp_alpha_conversion(subset)),
            element: Box::new(exp_alpha_conversion(element)),
        },
        Exp::TypeLift { superset, subset } => Exp::TypeLift {
            superset: Box::new(exp_alpha_conversion(superset)),
            subset: Box::new(exp_alpha_conversion(subset)),
        },
        Exp::Equal { left, right } => Exp::Equal {
            left: Box::new(exp_alpha_conversion(left)),
            right: Box::new(exp_alpha_conversion(right)),
        },
        Exp::Exists { set: ty } => Exp::Exists {
            set: Box::new(exp_alpha_conversion(ty)),
        },
        Exp::Take {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => Exp::Take {
            domain: Box::new(exp_alpha_conversion(domain)),
            codomain: Box::new(exp_alpha_conversion(codomain)),
            map: Box::new(exp_alpha_conversion(map)),
            existence: Box::new(exp_alpha_conversion(existence)),
            uniqueness: uniqueness
                .as_deref()
                .map(|p| Box::new(exp_alpha_conversion(p))),
        },
        Exp::ExistsIntro { element, set } => Exp::ExistsIntro {
            element: Box::new(exp_alpha_conversion(element)),
            set: Box::new(exp_alpha_conversion(set)),
        },
        Exp::SubsetElim {
            element,
            subset,
            superset,
        } => Exp::SubsetElim {
            element: Box::new(exp_alpha_conversion(element)),
            subset: Box::new(exp_alpha_conversion(subset)),
            superset: Box::new(exp_alpha_conversion(superset)),
        },
        Exp::IdRefl { element } => Exp::IdRefl {
            element: Box::new(exp_alpha_conversion(element)),
        },
        Exp::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
            base,
            equality,
        } => {
            let new_var = Var::new(var.as_str());
            Exp::IdElim {
                left: Box::new(exp_alpha_conversion(left)),
                right: Box::new(exp_alpha_conversion(right)),
                ty: Box::new(exp_alpha_conversion(ty)),
                var: new_var.clone(),
                predicate: Box::new(exp_subst(
                    &exp_alpha_conversion(predicate),
                    var,
                    &Exp::Var(new_var),
                )),
                base: Box::new(exp_alpha_conversion(base)),
                equality: Box::new(exp_alpha_conversion(equality)),
            }
        }
        Exp::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => Exp::TakeEq {
            func: Box::new(exp_alpha_conversion(func)),
            domain: Box::new(exp_alpha_conversion(domain)),
            codomain: Box::new(exp_alpha_conversion(codomain)),
            element: Box::new(exp_alpha_conversion(element)),
            existence: Box::new(exp_alpha_conversion(existence)),
            uniqueness: uniqueness
                .as_deref()
                .map(|p| Box::new(exp_alpha_conversion(p))),
        },
    }
}

/// Remove refinement-introduction certificates while preserving their
/// computational element.  This operation is purely syntactic: callers are
/// responsible for establishing that the input is well typed.
pub fn erase(e: &Exp) -> Exp {
    match e {
        Exp::Sort(sort) => Exp::Sort(*sort),
        Exp::Var(var) => Exp::Var(var.clone()),
        Exp::Prod { var, ty, body } => Exp::Prod {
            var: var.clone(),
            ty: Box::new(erase(ty)),
            body: Box::new(erase(body)),
        },
        Exp::Lam { var, ty, body } => Exp::Lam {
            var: var.clone(),
            ty: Box::new(erase(ty)),
            body: Box::new(erase(body)),
        },
        Exp::App { func, arg } => Exp::App {
            func: Box::new(erase(func)),
            arg: Box::new(erase(arg)),
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
            elim: Box::new(erase(elim)),
            return_type: Box::new(erase(return_type)),
            cases: cases.iter().map(erase).collect(),
        },
        Exp::SubsetIntro { element, .. } => erase(element),
        Exp::PowerSet { set } => Exp::PowerSet {
            set: Box::new(erase(set)),
        },
        Exp::SubSet {
            var,
            set,
            predicate,
        } => Exp::SubSet {
            var: var.clone(),
            set: Box::new(erase(set)),
            predicate: Box::new(erase(predicate)),
        },
        Exp::Pred {
            superset,
            subset,
            element,
        } => Exp::Pred {
            superset: Box::new(erase(superset)),
            subset: Box::new(erase(subset)),
            element: Box::new(erase(element)),
        },
        Exp::TypeLift { superset, subset } => Exp::TypeLift {
            superset: Box::new(erase(superset)),
            subset: Box::new(erase(subset)),
        },
        Exp::Equal { left, right } => Exp::Equal {
            left: Box::new(erase(left)),
            right: Box::new(erase(right)),
        },
        Exp::Exists { set } => Exp::Exists {
            set: Box::new(erase(set)),
        },
        Exp::Take {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => Exp::Take {
            domain: Box::new(erase(domain)),
            codomain: Box::new(erase(codomain)),
            map: Box::new(erase(map)),
            existence: Box::new(erase(existence)),
            uniqueness: uniqueness.as_deref().map(erase).map(Box::new),
        },
        Exp::ExistsIntro { element, set } => Exp::ExistsIntro {
            element: Box::new(erase(element)),
            set: Box::new(erase(set)),
        },
        Exp::SubsetElim {
            element,
            subset,
            superset,
        } => Exp::SubsetElim {
            element: Box::new(erase(element)),
            subset: Box::new(erase(subset)),
            superset: Box::new(erase(superset)),
        },
        Exp::IdRefl { element } => Exp::IdRefl {
            element: Box::new(erase(element)),
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
            left: Box::new(erase(left)),
            right: Box::new(erase(right)),
            ty: Box::new(erase(ty)),
            var: var.clone(),
            predicate: Box::new(erase(predicate)),
            base: Box::new(erase(base)),
            equality: Box::new(erase(equality)),
        },
        Exp::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => Exp::TakeEq {
            func: Box::new(erase(func)),
            domain: Box::new(erase(domain)),
            codomain: Box::new(erase(codomain)),
            element: Box::new(erase(element)),
            existence: Box::new(erase(existence)),
            uniqueness: uniqueness.as_deref().map(erase).map(Box::new),
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
                ty: Box::new(ty),
                body: Box::new(body),
            })
        }
        Exp::Lam { var, ty, body } => {
            let ty = reduce_if(ty);
            let body = reduce_if(body);

            changed.then_some(Exp::Lam {
                var: var.clone(),
                ty: Box::new(ty),
                body: Box::new(body),
            })
        }
        Exp::App { func, arg } => {
            let func = reduce_if(func);
            let arg = reduce_if(arg);

            changed.then_some(Exp::App {
                func: Box::new(func),
                arg: Box::new(arg),
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
                elim: Box::new(elim),
                return_type: Box::new(return_type),
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
                superset: Box::new(superset),
                subset: Box::new(subset),
                element: Box::new(element),
                proof: Box::new(proof),
            })
        }
        Exp::PowerSet { set: exp } => {
            let exp = reduce_if(exp);
            changed.then_some(Exp::PowerSet { set: Box::new(exp) })
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
                set: Box::new(exp),
                predicate: Box::new(predicate),
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
                superset: Box::new(superset),
                subset: Box::new(subset),
                element: Box::new(element),
            })
        }
        Exp::TypeLift { superset, subset } => {
            let superset = reduce_if(superset);
            let subset = reduce_if(subset);

            changed.then_some(Exp::TypeLift {
                superset: Box::new(superset),
                subset: Box::new(subset),
            })
        }
        Exp::Equal { left, right } => {
            let left = reduce_if(left);
            let right = reduce_if(right);

            changed.then_some(Exp::Equal {
                left: Box::new(left),
                right: Box::new(right),
            })
        }
        Exp::Exists { set: ty } => {
            let ty = reduce_if(ty);
            changed.then_some(Exp::Exists { set: Box::new(ty) })
        }
        Exp::Take {
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
            let uniqueness = uniqueness.as_deref().map(&mut reduce_if).map(Box::new);

            changed.then_some(Exp::Take {
                domain: Box::new(domain),
                codomain: Box::new(codomain),
                map: Box::new(map),
                existence: Box::new(existence),
                uniqueness,
            })
        }
        Exp::ExistsIntro { element, set } => {
            let element = reduce_if(element);
            let set = reduce_if(set);
            changed.then_some(Exp::ExistsIntro {
                element: Box::new(element),
                set: Box::new(set),
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
                element: Box::new(element),
                subset: Box::new(subset),
                superset: Box::new(superset),
            })
        }
        Exp::IdRefl { element } => {
            let element = reduce_if(element);
            changed.then_some(Exp::IdRefl {
                element: Box::new(element),
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
                left: Box::new(left),
                right: Box::new(right),
                ty: Box::new(ty),
                var: var.clone(),
                predicate: Box::new(predicate),
                base: Box::new(base),
                equality: Box::new(equality),
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
            let uniqueness = uniqueness.as_deref().map(&mut reduce_if).map(Box::new);
            changed.then_some(Exp::TakeEq {
                func: Box::new(func),
                domain: Box::new(domain),
                codomain: Box::new(codomain),
                element: Box::new(element),
                existence: Box::new(existence),
                uniqueness,
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
    exp_is_alpha_eq(&normalize(e1), &normalize(e2))
}

/// Computational normal form.  Erasure precedes normalization so that
/// removing a certificate may expose a beta redex or an eliminator redex.
pub fn erased_normal(e: &Exp) -> Exp {
    normalize(&erase(e))
}

/// Computational equality modulo refinement certificates.
///
/// This function deliberately does not type-check its arguments.  Typing
/// rules using it must establish well-typedness independently.
pub fn erased_convertible(e1: &Exp, e2: &Exp) -> bool {
    exp_is_alpha_eq(&erased_normal(e1), &erased_normal(e2))
}

impl Exp {
    pub fn alpha_convert(&self) -> Exp {
        exp_alpha_conversion(self)
    }
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
