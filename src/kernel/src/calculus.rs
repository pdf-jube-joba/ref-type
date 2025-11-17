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
        (Exp::Cast { exp: e1, to: t1 }, Exp::Cast { exp: e2, to: t2 }) => {
            exp_strict_equivalence(e1, e2) && exp_strict_equivalence(t1, t2)
        }
        (Exp::ProveLater { prop: e1 }, Exp::ProveLater { prop: e2 }) => {
            exp_strict_equivalence(e1, e2)
        }
        (
            Exp::ProveHere {
                exp: exp1,
                goals: goals1,
            },
            Exp::ProveHere {
                exp: exp2,
                goals: goals2,
            },
        ) => {
            exp_strict_equivalence(exp1, exp2)
                && goals1.len() == goals2.len()
                && goals1.iter().zip(goals2.iter()).all(|(g1, g2)| {
                    exp_strict_equivalence(&g1.goal_prop, &g2.goal_prop)
                        && command_strict_equivalence(&g1.command, &g2.command)
                        && {
                            if g1.extended_ctx.len() != g2.extended_ctx.len() {
                                return false;
                            }
                            for ((var1, exp1), (var2, exp2)) in
                                g1.extended_ctx.iter().zip(g2.extended_ctx.iter())
                            {
                                if !var1.is_eq_ptr(var2) || !exp_strict_equivalence(exp1, exp2) {
                                    return false;
                                }
                            }
                            true
                        }
                })
        }
        (Exp::ProofTermRaw { command: command1 }, Exp::ProofTermRaw { command: command2 }) => {
            command_strict_equivalence(command1, command2)
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
        (Exp::Take { map: m1 }, Exp::Take { map: m2 }) => exp_strict_equivalence(m1, m2),
        _ => false,
    }
}

pub fn command_strict_equivalence(command1: &ProveCommandBy, command2: &ProveCommandBy) -> bool {
    match (command1, command2) {
        (ProveCommandBy::Construct(pt1), ProveCommandBy::Construct(pt2)) => {
            exp_strict_equivalence(pt1, pt2)
        }
        (
            ProveCommandBy::ExactElem {
                elem: elem1,
                ty: ty1,
            },
            ProveCommandBy::ExactElem {
                elem: elem2,
                ty: ty2,
            },
        ) => exp_strict_equivalence(elem1, elem2) && exp_strict_equivalence(ty1, ty2),
        (ProveCommandBy::IdRefl { elem: elem1 }, ProveCommandBy::IdRefl { elem: elem2 }) => {
            exp_strict_equivalence(elem1, elem2)
        }
        (
            ProveCommandBy::IdElim {
                left: left1,
                right: right1,
                ty: ty1,
                var: var1,
                predicate: predicate1,
            },
            ProveCommandBy::IdElim {
                left: left2,
                right: right2,
                ty: ty2,
                var: var2,
                predicate: predicate2,
            },
        ) => {
            var1.is_eq_ptr(var2)
                && exp_strict_equivalence(left1, left2)
                && exp_strict_equivalence(right1, right2)
                && exp_strict_equivalence(ty1, ty2)
                && exp_strict_equivalence(predicate1, predicate2)
        }
        (
            ProveCommandBy::SubsetElim {
                elem: elem1,
                subset: subset1,
                superset: superset1,
            },
            ProveCommandBy::SubsetElim {
                elem: elem2,
                subset: subset2,
                superset: superset2,
            },
        ) => {
            exp_strict_equivalence(elem1, elem2)
                && exp_strict_equivalence(subset1, subset2)
                && exp_strict_equivalence(superset1, superset2)
        }
        (
            ProveCommandBy::TakeEq {
                func: func1,
                domain: domain1,
                codomain: codomain1,
                elem: elem1,
            },
            ProveCommandBy::TakeEq {
                func: func2,
                domain: domain2,
                codomain: codomain2,
                elem: elem2,
            },
        ) => {
            exp_strict_equivalence(func1, func2)
                && exp_strict_equivalence(domain1, domain2)
                && exp_strict_equivalence(codomain1, codomain2)
                && exp_strict_equivalence(elem1, elem2)
        }
        (ProveCommandBy::Axiom(_), ProveCommandBy::Axiom(_)) => {
            todo!("axiom later fix")
        }
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
            indspec: _, // todo: check indty?
            elim,
            return_type,
            cases,
        } => {
            exp_contains_as_freevar(elim, v)
                || exp_contains_as_freevar(return_type, v)
                || cases.iter().any(|case| exp_contains_as_freevar(case, v))
        }
        Exp::Cast { exp, to } => exp_contains_as_freevar(exp, v) || exp_contains_as_freevar(to, v),
        Exp::ProveLater { prop } => exp_contains_as_freevar(prop, v),
        Exp::ProveHere { exp, goals } => {
            exp_contains_as_freevar(exp, v)
                || goals.iter().any(|goal| {
                    goal.extended_ctx.iter().any(|(var, _)| var.is_eq_ptr(v))
                        || exp_contains_as_freevar(&goal.goal_prop, v)
                        || command_contains_as_free_var(&goal.command, v)
                })
        }
        Exp::ProofTermRaw { command } => match command.as_ref() {
            ProveCommandBy::Construct(proof_term) => exp_contains_as_freevar(proof_term, v),
            ProveCommandBy::ExactElem { elem, ty } => {
                exp_contains_as_freevar(elem, v) || exp_contains_as_freevar(ty, v)
            }
            ProveCommandBy::SubsetElim {
                elem,
                subset,
                superset,
            } => {
                exp_contains_as_freevar(elem, v)
                    || exp_contains_as_freevar(subset, v)
                    || exp_contains_as_freevar(superset, v)
            }
            ProveCommandBy::IdRefl { elem } => exp_contains_as_freevar(elem, v),
            ProveCommandBy::IdElim {
                left,
                right,
                ty,
                var,
                predicate,
            } => {
                exp_contains_as_freevar(left, v)
                    || exp_contains_as_freevar(right, v)
                    || exp_contains_as_freevar(ty, v)
                    || (!var.is_eq_ptr(v) && exp_contains_as_freevar(predicate, v))
            }
            ProveCommandBy::TakeEq {
                func,
                domain,
                codomain,
                elem,
            } => {
                exp_contains_as_freevar(func, v)
                    || exp_contains_as_freevar(domain, v)
                    || exp_contains_as_freevar(codomain, v)
                    || exp_contains_as_freevar(elem, v)
            }
            ProveCommandBy::Axiom(axiom) => todo!("axiom later fix {:?}", axiom),
        },
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
        Exp::Take { map } => exp_contains_as_freevar(map, v),
    }
}

fn command_contains_as_free_var(command: &ProveCommandBy, v: &Var) -> bool {
    match command {
        ProveCommandBy::Construct(proof_term) => exp_contains_as_freevar(proof_term, v),
        ProveCommandBy::ExactElem { elem, ty } => {
            exp_contains_as_freevar(elem, v) || exp_contains_as_freevar(ty, v)
        }
        ProveCommandBy::SubsetElim {
            elem,
            subset,
            superset,
        } => {
            exp_contains_as_freevar(elem, v)
                || exp_contains_as_freevar(subset, v)
                || exp_contains_as_freevar(superset, v)
        }
        ProveCommandBy::IdRefl { elem } => exp_contains_as_freevar(elem, v),
        ProveCommandBy::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
        } => {
            exp_contains_as_freevar(left, v)
                || exp_contains_as_freevar(right, v)
                || exp_contains_as_freevar(ty, v)
                || (!var.is_eq_ptr(v) && exp_contains_as_freevar(predicate, v))
        }
        ProveCommandBy::TakeEq {
            func,
            domain,
            codomain,
            elem,
        } => {
            exp_contains_as_freevar(func, v)
                || exp_contains_as_freevar(domain, v)
                || exp_contains_as_freevar(codomain, v)
                || exp_contains_as_freevar(elem, v)
        }
        ProveCommandBy::Axiom(axiom) => todo!("axiom later fix {:?}", axiom),
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
        (Exp::Cast { exp: e1, to: t1 }, Exp::Cast { exp: e2, to: t2 }) => {
            is_alpha_eq_rec(e1, e2, env1, env2) && is_alpha_eq_rec(t1, t2, env1, env2)
        }
        (Exp::ProveLater { prop: e1 }, Exp::ProveLater { prop: e2 }) => {
            is_alpha_eq_rec(e1, e2, env1, env2)
        }
        (
            Exp::ProveHere {
                exp: exp1,
                goals: _,
            },
            Exp::ProveHere {
                exp: exp2,
                goals: _,
            },
        ) => {
            // here we ignore proof goals
            is_alpha_eq_rec(exp1, exp2, env1, env2)
        }
        (Exp::ProofTermRaw { command: _ }, Exp::ProofTermRaw { command: _ }) => {
            // here we ignore proof terms
            true
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
        (Exp::Take { map: m1 }, Exp::Take { map: m2 }) => is_alpha_eq_rec(m1, m2, env1, env2),
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
        Exp::Cast { exp, to } => Exp::Cast {
            exp: Box::new(exp_subst(exp, v, t)),
            to: Box::new(exp_subst(to, v, t)),
        },
        Exp::ProveLater { prop: exp } => Exp::ProveLater {
            prop: Box::new(exp_subst(exp, v, t)),
        },
        Exp::ProveHere { exp, goals } => Exp::ProveHere {
            exp: Box::new(exp_subst(exp, v, t)),
            goals: goals
                .iter()
                .map(|goal| ProveGoal {
                    extended_ctx: goal
                        .extended_ctx
                        .iter()
                        .map(|(var, exp)| (var.clone(), exp_subst(exp, v, t)))
                        .collect::<Vec<_>>(),
                    goal_prop: exp_subst(&goal.goal_prop, v, t),
                    command: command_subst(&goal.command, v, t),
                })
                .collect(),
        },
        Exp::ProofTermRaw { command } => Exp::ProofTermRaw {
            command: match command.as_ref() {
                ProveCommandBy::Construct(proof_term) => {
                    ProveCommandBy::Construct(exp_subst(proof_term, v, t))
                }
                ProveCommandBy::ExactElem { elem, ty } => ProveCommandBy::ExactElem {
                    elem: exp_subst(elem, v, t),
                    ty: exp_subst(ty, v, t),
                },
                ProveCommandBy::SubsetElim {
                    elem,
                    subset,
                    superset,
                } => ProveCommandBy::SubsetElim {
                    elem: exp_subst(elem, v, t),
                    subset: exp_subst(subset, v, t),
                    superset: exp_subst(superset, v, t),
                },
                ProveCommandBy::IdRefl { elem } => ProveCommandBy::IdRefl {
                    elem: exp_subst(elem, v, t),
                },
                ProveCommandBy::IdElim {
                    left,
                    right,
                    ty,
                    var,
                    predicate,
                } => ProveCommandBy::IdElim {
                    left: exp_subst(left, v, t),
                    right: exp_subst(right, v, t),
                    ty: exp_subst(ty, v, t),
                    var: var.clone(),
                    predicate: if !v.is_eq_ptr(var) {
                        exp_subst(predicate, v, t)
                    } else {
                        predicate.clone()
                    },
                },
                ProveCommandBy::TakeEq {
                    func,
                    domain,
                    codomain,
                    elem,
                } => ProveCommandBy::TakeEq {
                    func: exp_subst(func, v, t),
                    domain: exp_subst(domain, v, t),
                    codomain: exp_subst(codomain, v, t),
                    elem: exp_subst(elem, v, t),
                },
                ProveCommandBy::Axiom(_) => todo!("axiom later fix"),
            }
            .into(),
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
        Exp::Take { map } => Exp::Take {
            map: Box::new(exp_subst(map, v, t)),
        },
    }
}

pub fn command_subst(command: &ProveCommandBy, v: &Var, t: &Exp) -> ProveCommandBy {
    match command {
        ProveCommandBy::Construct(proof_term) => {
            ProveCommandBy::Construct(exp_subst(proof_term, v, t))
        }
        ProveCommandBy::ExactElem { elem, ty } => ProveCommandBy::ExactElem {
            elem: exp_subst(elem, v, t),
            ty: exp_subst(ty, v, t),
        },
        ProveCommandBy::SubsetElim {
            elem,
            subset,
            superset,
        } => ProveCommandBy::SubsetElim {
            elem: exp_subst(elem, v, t),
            subset: exp_subst(subset, v, t),
            superset: exp_subst(superset, v, t),
        },
        ProveCommandBy::IdRefl { elem } => ProveCommandBy::IdRefl {
            elem: exp_subst(elem, v, t),
        },
        ProveCommandBy::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
        } => ProveCommandBy::IdElim {
            left: exp_subst(left, v, t),
            right: exp_subst(right, v, t),
            ty: exp_subst(ty, v, t),
            var: var.clone(),
            predicate: if !v.is_eq_ptr(var) {
                exp_subst(predicate, v, t)
            } else {
                predicate.clone()
            },
        },
        ProveCommandBy::TakeEq {
            func,
            domain,
            codomain,
            elem,
        } => ProveCommandBy::TakeEq {
            func: exp_subst(func, v, t),
            domain: exp_subst(domain, v, t),
            codomain: exp_subst(codomain, v, t),
            elem: exp_subst(elem, v, t),
        },
        ProveCommandBy::Axiom(_) => todo!("axiom later fix"),
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
        Exp::Cast { exp, to } => Exp::Cast {
            exp: Box::new(exp_alpha_conversion(exp)),
            to: Box::new(exp_alpha_conversion(to)),
        },

        Exp::ProveLater { prop: exp } => Exp::ProveLater {
            prop: Box::new(exp_alpha_conversion(exp)),
        },
        Exp::ProveHere { exp, goals } => Exp::ProveHere {
            exp: Box::new(exp_alpha_conversion(exp)),
            goals: goals
                .iter()
                .map(|goal| {
                    let ProveGoal {
                        extended_ctx,
                        goal_prop,
                        command: proof_term,
                    } = goal;

                    let mut subst_map = vec![];
                    for (var, _) in extended_ctx.iter() {
                        let new_var = Var::new(var.as_str());
                        subst_map.push((var.clone(), new_var));
                    }

                    let mut new_ctx = vec![];
                    for (i, (_, e)) in extended_ctx.iter().enumerate() {
                        let mut new_e = exp_alpha_conversion(e);
                        for (old_var, new_var) in subst_map.iter() {
                            new_e = exp_subst(&new_e, old_var, &Exp::Var(new_var.clone()));
                        }
                        new_ctx.push((subst_map[i].1.clone(), new_e));
                    }

                    let goal_prop = {
                        let mut new_goal_prop = exp_alpha_conversion(goal_prop);
                        for (old_var, new_var) in subst_map.iter() {
                            new_goal_prop =
                                exp_subst(&new_goal_prop, old_var, &Exp::Var(new_var.clone()));
                        }
                        new_goal_prop
                    };

                    let proof_term = {
                        let mut new_proof_term = command_alpha_conversion(proof_term);
                        for (old_var, new_var) in subst_map.iter() {
                            new_proof_term =
                                command_subst(&new_proof_term, old_var, &Exp::Var(new_var.clone()));
                        }
                        new_proof_term
                    };

                    ProveGoal {
                        extended_ctx: new_ctx,
                        goal_prop,
                        command: proof_term,
                    }
                })
                .collect(),
        },
        Exp::ProofTermRaw { command } => Exp::ProofTermRaw {
            command: command_alpha_conversion(command).into(),
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
        Exp::Take { map } => Exp::Take {
            map: Box::new(exp_alpha_conversion(map)),
        },
    }
}

pub fn command_alpha_conversion(command: &ProveCommandBy) -> ProveCommandBy {
    match command {
        ProveCommandBy::Construct(proof_term) => {
            ProveCommandBy::Construct(exp_alpha_conversion(proof_term))
        }
        ProveCommandBy::ExactElem { elem, ty } => ProveCommandBy::ExactElem {
            elem: exp_alpha_conversion(elem),
            ty: exp_alpha_conversion(ty),
        },
        ProveCommandBy::SubsetElim {
            elem,
            subset,
            superset,
        } => ProveCommandBy::SubsetElim {
            elem: exp_alpha_conversion(elem),
            subset: exp_alpha_conversion(subset),
            superset: exp_alpha_conversion(superset),
        },
        ProveCommandBy::IdRefl { elem } => ProveCommandBy::IdRefl {
            elem: exp_alpha_conversion(elem),
        },
        ProveCommandBy::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
        } => {
            let new_var = Var::new(var.as_str());
            ProveCommandBy::IdElim {
                left: exp_alpha_conversion(left),
                right: exp_alpha_conversion(right),
                ty: exp_alpha_conversion(ty),
                var: new_var.clone(),
                predicate: exp_subst(&exp_alpha_conversion(predicate), var, &Exp::Var(new_var)),
            }
        }
        ProveCommandBy::TakeEq {
            func,
            domain,
            codomain,
            elem,
        } => ProveCommandBy::TakeEq {
            func: exp_alpha_conversion(func),
            domain: exp_alpha_conversion(domain),
            codomain: exp_alpha_conversion(codomain),
            elem: exp_alpha_conversion(elem),
        },
        ProveCommandBy::Axiom(_) => todo!("axiom later fix"),
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
        Exp::Cast { exp, to } => {
            let exp = reduce_if(exp);
            let to = reduce_if(to);

            changed.then_some(Exp::Cast {
                exp: Box::new(exp),
                to: Box::new(to),
            })
        }
        Exp::ProveLater { prop: exp } => {
            let exp = reduce_if(exp);
            changed.then_some(Exp::ProveLater {
                prop: Box::new(exp),
            })
        }
        Exp::ProveHere { exp, goals } => {
            let exp = reduce_if(exp);
            let goals = goals
                .iter()
                .map(|goal| ProveGoal {
                    extended_ctx: goal
                        .extended_ctx
                        .iter()
                        .map(|(var, exp)| (var.clone(), reduce_if(exp)))
                        .collect::<Vec<_>>(),
                    goal_prop: reduce_if(&goal.goal_prop),
                    command: goal.command.clone(),
                })
                .collect();

            changed.then_some(Exp::ProveHere {
                exp: Box::new(exp),
                goals,
            })
        }
        Exp::ProofTermRaw { command } => {
            let new_command = match command.as_ref() {
                ProveCommandBy::Construct(proof_term) => {
                    ProveCommandBy::Construct(reduce_if(proof_term))
                }
                ProveCommandBy::ExactElem { elem, ty } => ProveCommandBy::ExactElem {
                    elem: reduce_if(elem),
                    ty: reduce_if(ty),
                },
                ProveCommandBy::SubsetElim {
                    elem,
                    subset,
                    superset,
                } => ProveCommandBy::SubsetElim {
                    elem: reduce_if(elem),
                    subset: reduce_if(subset),
                    superset: reduce_if(superset),
                },
                ProveCommandBy::IdRefl { elem } => ProveCommandBy::IdRefl {
                    elem: reduce_if(elem),
                },
                ProveCommandBy::IdElim {
                    left,
                    right,
                    ty,
                    var,
                    predicate,
                } => ProveCommandBy::IdElim {
                    left: reduce_if(left),
                    right: reduce_if(right),
                    ty: reduce_if(ty),
                    var: var.clone(),
                    predicate: reduce_if(predicate),
                },
                ProveCommandBy::TakeEq {
                    func,
                    domain,
                    codomain,
                    elem,
                } => ProveCommandBy::TakeEq {
                    func: reduce_if(func),
                    domain: reduce_if(domain),
                    codomain: reduce_if(codomain),
                    elem: reduce_if(elem),
                },
                ProveCommandBy::Axiom(_) => {
                    todo!("axiom later fix")
                }
            };

            changed.then_some(Exp::ProofTermRaw {
                command: new_command.into(),
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
        Exp::Take { map } => {
            let map = reduce_if(map);

            changed.then_some(Exp::Take { map: Box::new(map) })
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

// inefficient but simple
pub fn convertible(e1: &Exp, e2: &Exp) -> bool {
    exp_is_alpha_eq(&normalize(e1), &normalize(e2))
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
    use crate::{app, lam, prod, var, var_exp};
    #[test]
    fn reduce_test() {
        // ((z: X) => z) Y)
        let ty = app!(lam!(var!("z"), var_exp!("X"), var_exp!("z")), var_exp!("Y"));
        let reduced = normalize(&ty);
        println!("reduced: {:?}", reduced);
        // (x: ty) -> y
        let e = prod!(var!("x"), ty, var_exp!("y"));
        let reduced = reduce_one(&e).unwrap();
        // (x: Y) -> y
        println!("reduced: {:?}", reduced);
    }
}
