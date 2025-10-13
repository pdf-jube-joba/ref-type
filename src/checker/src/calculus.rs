use crate::inductive::inductive_type_elim_reduce;

use super::coreexp::*;

pub fn is_alpha_eq(e1: &CoreExp, e2: &CoreExp) -> bool {
    fn is_alpha_rec(e1: &CoreExp, e2: &CoreExp, env1: &mut Vec<Var>, env2: &mut Vec<Var>) -> bool {
        match (e1, e2) {
            (CoreExp::Sort(s1), CoreExp::Sort(s2)) => s1 == s2,
            (CoreExp::Sort(_), _) => false,
            (CoreExp::Var(v1), CoreExp::Var(v2)) => {
                let pos1 = env1.iter().rposition(|v| v.is_eq_ptr(v1));
                let pos2 = env2.iter().rposition(|v| v.is_eq_ptr(v2));
                match (pos1, pos2) {
                    (Some(p1), Some(p2)) => p1 == p2,
                    (None, None) => v1.name() == v2.name(),
                    _ => false,
                }
            }
            (CoreExp::Var(_), _) => false,
            (
                CoreExp::Prod {
                    var: var1,
                    ty: ty1,
                    body: body1,
                },
                CoreExp::Prod {
                    var: var2,
                    ty: ty2,
                    body: body2,
                },
            ) => {
                is_alpha_rec(ty1, ty2, env1, env2) && {
                    env1.push(var1.clone());
                    env2.push(var2.clone());
                    let res = is_alpha_rec(body1, body2, env1, env2);
                    env1.pop();
                    env2.pop();
                    res
                }
            }
            (
                CoreExp::Prod {
                    var: _,
                    ty: _,
                    body: _,
                },
                _,
            ) => false,
            (
                CoreExp::Lam {
                    var: var1,
                    ty: ty1,
                    body: body1,
                },
                CoreExp::Lam {
                    var: var2,
                    ty: ty2,
                    body: body2,
                },
            ) => {
                is_alpha_rec(ty1, ty2, env1, env2) && {
                    env1.push(var1.clone());
                    env2.push(var2.clone());
                    let res = is_alpha_rec(body1, body2, env1, env2);
                    env1.pop();
                    env2.pop();
                    res
                }
            }
            (
                CoreExp::Lam {
                    var: _,
                    ty: _,
                    body: _,
                },
                _,
            ) => false,
            (CoreExp::App { func: f1, arg: a1 }, CoreExp::App { func: f2, arg: a2 }) => {
                is_alpha_rec(f1, f2, env1, env2) && is_alpha_rec(a1, a2, env1, env2)
            }
            (CoreExp::App { func: _, arg: _ }, _) => false,
            (
                CoreExp::IndType {
                    ty: ty1,
                    parameters: parameter1,
                    index: index1,
                },
                CoreExp::IndType {
                    ty: ty2,
                    parameters: parameter2,
                    index: index2,
                },
            ) => {
                std::rc::Rc::ptr_eq(ty1, ty2)
                    && parameter1.len() == parameter2.len()
                    && parameter1
                        .iter()
                        .zip(parameter2.iter())
                        .all(|(a1, a2)| is_alpha_rec(a1, a2, env1, env2))
                    && index1.len() == index2.len()
                    && index1
                        .iter()
                        .zip(index2.iter())
                        .all(|(a1, a2)| is_alpha_rec(a1, a2, env1, env2))
            }
            (
                CoreExp::IndType {
                    ty: _,
                    parameters: _,
                    index: _,
                },
                _,
            ) => false,
            (
                CoreExp::IndTypeCst {
                    ty: ty1,
                    idx: idx1,
                    parameter: parameter1,
                    args: args1,
                },
                CoreExp::IndTypeCst {
                    ty: ty2,
                    idx: idx2,
                    parameter: parameter2,
                    args: args2,
                },
            ) => {
                std::rc::Rc::ptr_eq(ty1, ty2)
                    && idx1 == idx2
                    && parameter1.len() == parameter2.len()
                    && parameter1
                        .iter()
                        .zip(parameter2.iter())
                        .all(|(a1, a2)| is_alpha_rec(a1, a2, env1, env2))
                    && args1.len() == args2.len()
                    && args1
                        .iter()
                        .zip(args2.iter())
                        .all(|(a1, a2)| is_alpha_rec(a1, a2, env1, env2))
            }
            (
                CoreExp::IndTypeCst {
                    ty: _,
                    idx: _,
                    parameter: _,
                    args: _,
                },
                _,
            ) => false,
            (
                CoreExp::IndTypeElim {
                    ty: ty1,
                    elim: elim1,
                    return_type: ret1,
                    cases: cases1,
                },
                CoreExp::IndTypeElim {
                    ty: ty2,
                    elim: elim2,
                    return_type: ret2,
                    cases: cases2,
                },
            ) => {
                std::rc::Rc::ptr_eq(ty1, ty2)
                    && is_alpha_rec(elim1, elim2, env1, env2)
                    && is_alpha_rec(ret1, ret2, env1, env2)
                    && cases1.len() == cases2.len()
                    && cases1
                        .iter()
                        .zip(cases2.iter())
                        .all(|(c1, c2)| is_alpha_rec(c1, c2, env1, env2))
            }
            (
                CoreExp::IndTypeElim {
                    ty: _,
                    elim: _,
                    return_type: _,
                    cases: _,
                },
                _,
            ) => false,
            (CoreExp::Cast { exp: e1, to: t1 }, CoreExp::Cast { exp: e2, to: t2 }) => {
                is_alpha_rec(e1, e2, env1, env2) && is_alpha_rec(t1, t2, env1, env2)
            }
            (CoreExp::Cast { exp: _, to: _ }, _) => false,
            (CoreExp::Proof { exp: e1 }, CoreExp::Proof { exp: e2 }) => {
                is_alpha_rec(e1, e2, env1, env2)
            }
            (CoreExp::Proof { exp: _ }, _) => false,
            (CoreExp::PowerSet { exp: e1 }, CoreExp::PowerSet { exp: e2 }) => {
                is_alpha_rec(e1, e2, env1, env2)
            }
            (CoreExp::PowerSet { exp: _ }, _) => false,
            (
                CoreExp::SubSet {
                    var: var1,
                    exp: e1,
                    predicate: p1,
                },
                CoreExp::SubSet {
                    var: var2,
                    exp: e2,
                    predicate: p2,
                },
            ) => {
                is_alpha_rec(e1, e2, env1, env2) && {
                    env1.push(var1.clone());
                    env2.push(var2.clone());
                    let res = is_alpha_rec(p1, p2, env1, env2);
                    env1.pop();
                    env2.pop();
                    res
                }
            }
            (
                CoreExp::SubSet {
                    var: _,
                    exp: _,
                    predicate: _,
                },
                _,
            ) => false,
            (
                CoreExp::Pred {
                    superset: s1,
                    subset: sub1,
                    element: e1,
                },
                CoreExp::Pred {
                    superset: s2,
                    subset: sub2,
                    element: e2,
                },
            ) => {
                is_alpha_rec(s1, s2, env1, env2)
                    && is_alpha_rec(sub1, sub2, env1, env2)
                    && is_alpha_rec(e1, e2, env1, env2)
            }
            (
                CoreExp::Pred {
                    superset: _,
                    subset: _,
                    element: _,
                },
                _,
            ) => false,
            (
                CoreExp::TypeLift {
                    superset: s1,
                    subset: sub1,
                },
                CoreExp::TypeLift {
                    superset: s2,
                    subset: sub2,
                },
            ) => is_alpha_rec(s1, s2, env1, env2) && is_alpha_rec(sub1, sub2, env1, env2),
            (
                CoreExp::TypeLift {
                    superset: _,
                    subset: _,
                },
                _,
            ) => false,
            (
                CoreExp::Equal {
                    left: l1,
                    right: r1,
                },
                CoreExp::Equal {
                    left: l2,
                    right: r2,
                },
            ) => is_alpha_rec(l1, l2, env1, env2) && is_alpha_rec(r1, r2, env1, env2),
            (CoreExp::Equal { left: _, right: _ }, _) => false,
            (CoreExp::Exists { ty: ty1 }, CoreExp::Exists { ty: ty2 }) => {
                is_alpha_rec(ty1, ty2, env1, env2)
            }
            (CoreExp::Exists { ty: _ }, _) => false,
            (
                CoreExp::Take {
                    map: m1,
                    domain: d1,
                    codomain: c1,
                },
                CoreExp::Take {
                    map: m2,
                    domain: d2,
                    codomain: c2,
                },
            ) => {
                is_alpha_rec(m1, m2, env1, env2)
                    && is_alpha_rec(d1, d2, env1, env2)
                    && is_alpha_rec(c1, c2, env1, env2)
            }
            (
                CoreExp::Take {
                    map: _,
                    domain: _,
                    codomain: _,
                },
                _,
            ) => false,
        }
    }
    is_alpha_rec(e1, e2, &mut vec![], &mut vec![])
}

pub fn subst(e: &CoreExp, v: &Var, t: &CoreExp) -> CoreExp {
    match e {
        CoreExp::Sort(sort) => CoreExp::Sort(*sort),
        CoreExp::Var(var) => {
            if var.is_eq_ptr(v) {
                t.clone()
            } else {
                e.clone()
            }
        }
        CoreExp::Prod { var, ty, body } => {
            if var.is_eq_ptr(v) {
                CoreExp::Prod {
                    var: var.clone(),
                    ty: Box::new(subst(ty, v, t)),
                    body: body.clone(),
                }
            } else {
                CoreExp::Prod {
                    var: var.clone(),
                    ty: Box::new(subst(ty, v, t)),
                    body: Box::new(subst(body, v, t)),
                }
            }
        }
        CoreExp::Lam { var, ty, body } => {
            if var.is_eq_ptr(v) {
                CoreExp::Lam {
                    var: var.clone(),
                    ty: Box::new(subst(ty, v, t)),
                    body: body.clone(),
                }
            } else {
                CoreExp::Lam {
                    var: var.clone(),
                    ty: Box::new(subst(ty, v, t)),
                    body: Box::new(subst(body, v, t)),
                }
            }
        }
        CoreExp::App { func, arg } => CoreExp::App {
            func: Box::new(subst(func, v, t)),
            arg: Box::new(subst(arg, v, t)),
        },
        CoreExp::IndType {
            ty,
            parameters,
            index,
        } => CoreExp::IndType {
            ty: ty.clone(),
            parameters: parameters.iter().map(|arg| subst(arg, v, t)).collect(),
            index: index.iter().map(|arg| subst(arg, v, t)).collect(),
        },
        CoreExp::IndTypeCst {
            ty,
            idx,
            parameter,
            args,
        } => CoreExp::IndTypeCst {
            ty: ty.clone(),
            idx: *idx,
            parameter: parameter.iter().map(|arg| subst(arg, v, t)).collect(),
            args: args.iter().map(|arg| subst(arg, v, t)).collect(),
        },
        CoreExp::IndTypeElim {
            ty,
            elim,
            return_type,
            cases,
        } => CoreExp::IndTypeElim {
            ty: ty.clone(),
            elim: Box::new(subst(elim, v, t)),
            return_type: Box::new(subst(return_type, v, t)),
            cases: cases.iter().map(|case| subst(case, v, t)).collect(),
        },
        CoreExp::Cast { exp, to } => CoreExp::Cast {
            exp: Box::new(subst(exp, v, t)),
            to: Box::new(subst(to, v, t)),
        },
        CoreExp::Proof { exp } => CoreExp::Proof {
            exp: Box::new(subst(exp, v, t)),
        },
        CoreExp::PowerSet { exp } => CoreExp::PowerSet {
            exp: Box::new(subst(exp, v, t)),
        },
        CoreExp::SubSet {
            var,
            exp,
            predicate,
        } => {
            if var.is_eq_ptr(v) {
                CoreExp::SubSet {
                    var: var.clone(),
                    exp: Box::new(subst(exp, v, t)),
                    predicate: predicate.clone(),
                }
            } else {
                CoreExp::SubSet {
                    var: var.clone(),
                    exp: Box::new(subst(exp, v, t)),
                    predicate: Box::new(subst(predicate, v, t)),
                }
            }
        }
        CoreExp::Pred {
            superset,
            subset,
            element,
        } => CoreExp::Pred {
            superset: Box::new(subst(superset, v, t)),
            subset: Box::new(subst(subset, v, t)),
            element: Box::new(subst(element, v, t)),
        },
        CoreExp::TypeLift { superset, subset } => CoreExp::TypeLift {
            superset: Box::new(subst(superset, v, t)),
            subset: Box::new(subst(subset, v, t)),
        },
        CoreExp::Equal { left, right } => CoreExp::Equal {
            left: Box::new(subst(left, v, t)),
            right: Box::new(subst(right, v, t)),
        },
        CoreExp::Exists { ty } => CoreExp::Exists {
            ty: Box::new(subst(ty, v, t)),
        },
        CoreExp::Take {
            map,
            domain,
            codomain,
        } => CoreExp::Take {
            map: Box::new(subst(map, v, t)),
            domain: Box::new(subst(domain, v, t)),
            codomain: Box::new(subst(codomain, v, t)),
        },
    }
}

pub fn reduce_if_top(e: &CoreExp) -> Option<CoreExp> {
    match e {
        CoreExp::App { func, arg } => {
            if let CoreExp::Lam { var, ty: _, body } = func.as_ref() {
                Some(subst(body, var, arg))
            } else {
                None
            }
        }
        _ => inductive_type_elim_reduce(e).ok(),
    }
}

pub fn reduce_one(e: &CoreExp) -> Option<CoreExp> {
    if let Some(e) = reduce_if_top(e) {
        return Some(e);
    }

    // challenge reduce exp if changed = true
    // return if Some(reduced) with changed := true
    // else return self
    let mut changed = false;
    let mut reduce_if = |e: &CoreExp| -> CoreExp {
        changed
            .then(|| reduce_one(e).inspect(|_| changed = true))
            .flatten()
            .unwrap_or(e.clone())
    };

    match e {
        CoreExp::Sort(_) => None,
        CoreExp::Var(_) => None,
        CoreExp::Prod { var, ty, body } => {
            let ty = reduce_if(ty);
            let body = reduce_if(body);

            changed.then_some(CoreExp::Prod {
                var: var.clone(),
                ty: Box::new(ty),
                body: Box::new(body),
            })
        }
        CoreExp::Lam { var, ty, body } => {
            let ty = reduce_if(ty);
            let body = reduce_if(body);

            changed.then_some(CoreExp::Lam {
                var: var.clone(),
                ty: Box::new(ty),
                body: Box::new(body),
            })
        }
        CoreExp::App { func, arg } => {
            let func = reduce_if(func);
            let arg = reduce_if(arg);

            changed.then_some(CoreExp::App {
                func: Box::new(func),
                arg: Box::new(arg),
            })
        }
        CoreExp::IndType {
            ty,
            parameters,
            index,
        } => {
            for (i, arg) in parameters.iter().enumerate() {
                if let Some(arg) = reduce_one(arg) {
                    let mut new_args = parameters.clone();
                    new_args[i] = arg;
                    return Some(CoreExp::IndType {
                        ty: ty.clone(),
                        parameters: new_args,
                        index: index.clone(),
                    });
                }
            }

            for (i, arg) in index.iter().enumerate() {
                if let Some(arg) = reduce_one(arg) {
                    let mut new_args = index.clone();
                    new_args[i] = arg;
                    return Some(CoreExp::IndType {
                        ty: ty.clone(),
                        parameters: parameters.clone(),
                        index: new_args,
                    });
                }
            }

            None
        }
        CoreExp::IndTypeCst {
            ty,
            idx,
            parameter,
            args,
        } => {
            for (i, arg) in parameter.iter().enumerate() {
                if let Some(arg) = reduce_one(arg) {
                    let mut new_args = parameter.clone();
                    new_args[i] = arg;
                    return Some(CoreExp::IndTypeCst {
                        ty: ty.clone(),
                        idx: *idx,
                        parameter: new_args,
                        args: args.clone(),
                    });
                }
            }

            for (i, arg) in args.iter().enumerate() {
                if let Some(arg) = reduce_one(arg) {
                    let mut new_args = args.clone();
                    new_args[i] = arg;
                    return Some(CoreExp::IndTypeCst {
                        ty: ty.clone(),
                        idx: *idx,
                        parameter: parameter.clone(),
                        args: new_args,
                    });
                }
            }

            None
        }
        CoreExp::IndTypeElim {
            ty,
            elim,
            return_type,
            cases,
        } => {
            if let Some(elim) = reduce_one(elim) {
                Some(CoreExp::IndTypeElim {
                    ty: ty.clone(),
                    elim: Box::new(elim),
                    return_type: return_type.clone(),
                    cases: cases.clone(),
                })
            } else if let Some(return_type) = reduce_one(return_type) {
                Some(CoreExp::IndTypeElim {
                    ty: ty.clone(),
                    elim: elim.clone(),
                    return_type: Box::new(return_type),
                    cases: cases.clone(),
                })
            } else {
                for (i, case) in cases.iter().enumerate() {
                    if let Some(case) = reduce_one(case) {
                        let mut new_cases = cases.clone();
                        new_cases[i] = case;
                        return Some(CoreExp::IndTypeElim {
                            ty: ty.clone(),
                            elim: elim.clone(),
                            return_type: return_type.clone(),
                            cases: new_cases,
                        });
                    }
                }
                None
            }
        }
        CoreExp::Cast { exp, to } => {
            let exp = reduce_if(exp);
            let to = reduce_if(to);

            changed.then_some(CoreExp::Cast {
                exp: Box::new(exp),
                to: Box::new(to),
            })
        }
        CoreExp::Proof { exp } => {
            let exp = reduce_if(exp);
            changed.then_some(CoreExp::Proof { exp: Box::new(exp) })
        }
        CoreExp::PowerSet { exp } => {
            let exp = reduce_if(exp);
            changed.then_some(CoreExp::PowerSet { exp: Box::new(exp) })
        }
        CoreExp::SubSet {
            var,
            exp,
            predicate,
        } => {
            let exp = reduce_if(exp);
            let predicate = reduce_if(predicate);
            changed.then_some(CoreExp::SubSet {
                var: var.clone(),
                exp: Box::new(exp),
                predicate: Box::new(predicate),
            })
        }
        CoreExp::Pred {
            superset,
            subset,
            element,
        } => {
            let superset = reduce_if(superset);
            let subset = reduce_if(subset);
            let element = reduce_if(element);
            changed.then_some(CoreExp::Pred {
                superset: Box::new(superset),
                subset: Box::new(subset),
                element: Box::new(element),
            })
        }
        CoreExp::TypeLift { superset, subset } => {
            let superset = reduce_if(superset);
            let subset = reduce_if(subset);
            changed.then_some(CoreExp::TypeLift {
                superset: Box::new(superset),
                subset: Box::new(subset),
            })
        }
        CoreExp::Equal { left, right } => {
            let left = reduce_if(left);
            let right = reduce_if(right);
            changed.then_some(CoreExp::Equal {
                left: Box::new(left),
                right: Box::new(right),
            })
        }
        CoreExp::Exists { ty } => {
            let ty = reduce_if(ty);
            changed.then_some(CoreExp::Exists { ty: Box::new(ty) })
        }
        CoreExp::Take {
            map,
            domain,
            codomain,
        } => {
            let map = reduce_if(map);
            let domain = reduce_if(domain);
            let codomain = reduce_if(codomain);
            changed.then_some(CoreExp::Take {
                map: Box::new(map),
                domain: Box::new(domain),
                codomain: Box::new(codomain),
            })
        }
    }
}

pub fn normalize(e: &CoreExp) -> CoreExp {
    let mut current = e.clone();
    while let Some(next) = reduce_one(&current) {
        current = next;
    }
    current
}

pub fn convertible(e1: &CoreExp, e2: &CoreExp) -> bool {
    is_alpha_eq(&normalize(e1), &normalize(e2))
}
