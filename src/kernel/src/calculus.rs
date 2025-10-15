use crate::inductive::inductive_type_elim_reduce;

use super::exp::*;

pub fn is_alpha_eq(e1: &Exp, e2: &Exp) -> bool {
    fn is_alpha_rec(e1: &Exp, e2: &Exp, env1: &mut Vec<Var>, env2: &mut Vec<Var>) -> bool {
        match (e1, e2) {
            (Exp::Sort(s1), Exp::Sort(s2)) => s1 == s2,
            (Exp::Sort(_), _) => false,
            (Exp::Var(v1), Exp::Var(v2)) => {
                let pos1 = env1.iter().rposition(|v| v.is_eq_ptr(v1));
                let pos2 = env2.iter().rposition(|v| v.is_eq_ptr(v2));
                match (pos1, pos2) {
                    (Some(p1), Some(p2)) => p1 == p2,
                    (None, None) => v1.name() == v2.name(),
                    _ => false,
                }
            }
            (Exp::Var(_), _) => false,
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
                Exp::Prod {
                    var: _,
                    ty: _,
                    body: _,
                },
                _,
            ) => false,
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
                Exp::Lam {
                    var: _,
                    ty: _,
                    body: _,
                },
                _,
            ) => false,
            (Exp::App { func: f1, arg: a1 }, Exp::App { func: f2, arg: a2 }) => {
                is_alpha_rec(f1, f2, env1, env2) && is_alpha_rec(a1, a2, env1, env2)
            }
            (Exp::App { func: _, arg: _ }, _) => false,
            (
                Exp::IndType {
                    ty: ty1,
                    parameters: parameter1,
                },
                Exp::IndType {
                    ty: ty2,
                    parameters: parameter2,
                },
            ) => {
                std::rc::Rc::ptr_eq(ty1, ty2)
                    && parameter1.len() == parameter2.len()
                    && parameter1
                        .iter()
                        .zip(parameter2.iter())
                        .all(|(a1, a2)| is_alpha_rec(a1, a2, env1, env2))
            }
            (
                Exp::IndType {
                    ty: _,
                    parameters: _,
                },
                _,
            ) => false,
            (
                Exp::IndCtor {
                    ty: ty1,
                    idx: idx1,
                    parameters: parameter1,
                },
                Exp::IndCtor {
                    ty: ty2,
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
                        .all(|(a1, a2)| is_alpha_rec(a1, a2, env1, env2))
            }
            (
                Exp::IndCtor {
                    ty: _,
                    idx: _,
                    parameters: _,
                },
                _,
            ) => false,
            (
                Exp::IndElim {
                    ty: ty1,
                    elim: elim1,
                    return_type: ret1,
                    sort: sort1,
                    cases: cases1,
                },
                Exp::IndElim {
                    ty: ty2,
                    elim: elim2,
                    return_type: ret2,
                    sort: sort2,
                    cases: cases2,
                },
            ) => {
                sort1 == sort2
                    && std::rc::Rc::ptr_eq(ty1, ty2)
                    && is_alpha_rec(elim1, elim2, env1, env2)
                    && is_alpha_rec(ret1, ret2, env1, env2)
                    && cases1.len() == cases2.len()
                    && cases1
                        .iter()
                        .zip(cases2.iter())
                        .all(|(c1, c2)| is_alpha_rec(c1, c2, env1, env2))
            }
            (
                Exp::IndElim {
                    ty: _,
                    elim: _,
                    return_type: _,
                    sort: _,
                    cases: _,
                },
                _,
            ) => false,
            (Exp::Cast { exp: e1, to: t1 }, Exp::Cast { exp: e2, to: t2 }) => {
                is_alpha_rec(e1, e2, env1, env2) && is_alpha_rec(t1, t2, env1, env2)
            }
            (Exp::Cast { exp: _, to: _ }, _) => false,
            (Exp::Proof { prop: e1 }, Exp::Proof { prop: e2 }) => is_alpha_rec(e1, e2, env1, env2),
            (Exp::Proof { prop: _ }, _) => false,
            (Exp::PowerSet { set: e1 }, Exp::PowerSet { set: e2 }) => {
                is_alpha_rec(e1, e2, env1, env2)
            }
            (Exp::PowerSet { set: _ }, _) => false,
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
                Exp::SubSet {
                    var: _,
                    set: _,
                    predicate: _,
                },
                _,
            ) => false,
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
                is_alpha_rec(s1, s2, env1, env2)
                    && is_alpha_rec(sub1, sub2, env1, env2)
                    && is_alpha_rec(e1, e2, env1, env2)
            }
            (
                Exp::Pred {
                    superset: _,
                    subset: _,
                    element: _,
                },
                _,
            ) => false,
            (
                Exp::TypeLift {
                    superset: s1,
                    subset: sub1,
                },
                Exp::TypeLift {
                    superset: s2,
                    subset: sub2,
                },
            ) => is_alpha_rec(s1, s2, env1, env2) && is_alpha_rec(sub1, sub2, env1, env2),
            (
                Exp::TypeLift {
                    superset: _,
                    subset: _,
                },
                _,
            ) => false,
            (
                Exp::Equal {
                    left: l1,
                    right: r1,
                },
                Exp::Equal {
                    left: l2,
                    right: r2,
                },
            ) => is_alpha_rec(l1, l2, env1, env2) && is_alpha_rec(r1, r2, env1, env2),
            (Exp::Equal { left: _, right: _ }, _) => false,
            (Exp::Exists { set: ty1 }, Exp::Exists { set: ty2 }) => {
                is_alpha_rec(ty1, ty2, env1, env2)
            }
            (Exp::Exists { set: _ }, _) => false,
            (
                Exp::Take {
                    map: m1,
                    domain: d1,
                    codomain: c1,
                },
                Exp::Take {
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
                Exp::Take {
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

pub fn subst(e: &Exp, v: &Var, t: &Exp) -> Exp {
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
                    ty: Box::new(subst(ty, v, t)),
                    body: body.clone(),
                }
            } else {
                Exp::Prod {
                    var: var.clone(),
                    ty: Box::new(subst(ty, v, t)),
                    body: Box::new(subst(body, v, t)),
                }
            }
        }
        Exp::Lam { var, ty, body } => {
            if var.is_eq_ptr(v) {
                Exp::Lam {
                    var: var.clone(),
                    ty: Box::new(subst(ty, v, t)),
                    body: body.clone(),
                }
            } else {
                Exp::Lam {
                    var: var.clone(),
                    ty: Box::new(subst(ty, v, t)),
                    body: Box::new(subst(body, v, t)),
                }
            }
        }
        Exp::App { func, arg } => Exp::App {
            func: Box::new(subst(func, v, t)),
            arg: Box::new(subst(arg, v, t)),
        },
        Exp::IndType { ty, parameters } => Exp::IndType {
            ty: ty.clone(),
            parameters: parameters.iter().map(|arg| subst(arg, v, t)).collect(),
        },
        Exp::IndCtor {
            ty,
            idx,
            parameters: parameter,
        } => Exp::IndCtor {
            ty: ty.clone(),
            idx: *idx,
            parameters: parameter.iter().map(|arg| subst(arg, v, t)).collect(),
        },
        Exp::IndElim {
            ty,
            elim,
            return_type,
            sort,
            cases,
        } => Exp::IndElim {
            ty: ty.clone(),
            elim: Box::new(subst(elim, v, t)),
            return_type: Box::new(subst(return_type, v, t)),
            sort: *sort,
            cases: cases.iter().map(|case| subst(case, v, t)).collect(),
        },
        Exp::Cast { exp, to } => Exp::Cast {
            exp: Box::new(subst(exp, v, t)),
            to: Box::new(subst(to, v, t)),
        },
        Exp::Proof { prop: exp } => Exp::Proof {
            prop: Box::new(subst(exp, v, t)),
        },
        Exp::PowerSet { set: exp } => Exp::PowerSet {
            set: Box::new(subst(exp, v, t)),
        },
        Exp::SubSet {
            var,
            set: exp,
            predicate,
        } => {
            if var.is_eq_ptr(v) {
                Exp::SubSet {
                    var: var.clone(),
                    set: Box::new(subst(exp, v, t)),
                    predicate: predicate.clone(),
                }
            } else {
                Exp::SubSet {
                    var: var.clone(),
                    set: Box::new(subst(exp, v, t)),
                    predicate: Box::new(subst(predicate, v, t)),
                }
            }
        }
        Exp::Pred {
            superset,
            subset,
            element,
        } => Exp::Pred {
            superset: Box::new(subst(superset, v, t)),
            subset: Box::new(subst(subset, v, t)),
            element: Box::new(subst(element, v, t)),
        },
        Exp::TypeLift { superset, subset } => Exp::TypeLift {
            superset: Box::new(subst(superset, v, t)),
            subset: Box::new(subst(subset, v, t)),
        },
        Exp::Equal { left, right } => Exp::Equal {
            left: Box::new(subst(left, v, t)),
            right: Box::new(subst(right, v, t)),
        },
        Exp::Exists { set: ty } => Exp::Exists {
            set: Box::new(subst(ty, v, t)),
        },
        Exp::Take {
            map,
            domain,
            codomain,
        } => Exp::Take {
            map: Box::new(subst(map, v, t)),
            domain: Box::new(subst(domain, v, t)),
            codomain: Box::new(subst(codomain, v, t)),
        },
    }
}

// any bindings in e should be renamed to avoid some problems
// free variable is not affected (ptr_copy)
pub fn alpha_conversion(e: &Exp) -> Exp {
    match e {
        Exp::Sort(sort) => Exp::Sort(*sort),
        Exp::Var(var) => Exp::Var(var.clone()),
        Exp::Prod { var, ty, body } => {
            let new_var = Var::new(var.name());
            Exp::Prod {
                var: new_var.clone(),
                ty: Box::new(alpha_conversion(ty)),
                body: Box::new(subst(&alpha_conversion(body), var, &Exp::Var(new_var))),
            }
        }
        Exp::Lam { var, ty, body } => {
            let new_var = Var::new(var.name());
            Exp::Lam {
                var: new_var.clone(),
                ty: Box::new(alpha_conversion(ty)),
                body: Box::new(subst(&alpha_conversion(body), var, &Exp::Var(new_var))),
            }
        }
        Exp::App { func, arg } => Exp::App {
            func: Box::new(alpha_conversion(func)),
            arg: Box::new(alpha_conversion(arg)),
        },
        Exp::IndType { ty, parameters } => Exp::IndType {
            ty: ty.clone(),
            parameters: parameters.iter().map(alpha_conversion).collect(),
        },
        Exp::IndCtor {
            ty,
            idx,
            parameters: parameter,
        } => Exp::IndCtor {
            ty: ty.clone(),
            idx: *idx,
            parameters: parameter.iter().map(alpha_conversion).collect(),
        },
        Exp::IndElim {
            ty,
            elim,
            return_type,
            sort,
            cases,
        } => Exp::IndElim {
            ty: ty.clone(),
            elim: Box::new(alpha_conversion(elim)),
            return_type: Box::new(alpha_conversion(return_type)),
            sort: *sort,
            cases: cases.iter().map(alpha_conversion).collect(),
        },
        Exp::Cast { exp, to } => Exp::Cast {
            exp: Box::new(alpha_conversion(exp)),
            to: Box::new(alpha_conversion(to)),
        },
        Exp::Proof { prop: exp } => Exp::Proof {
            prop: Box::new(alpha_conversion(exp)),
        },
        Exp::PowerSet { set: exp } => Exp::PowerSet {
            set: Box::new(alpha_conversion(exp)),
        },
        Exp::SubSet {
            var,
            set: exp,
            predicate,
        } => {
            let new_var = Var::new(var.name());
            Exp::SubSet {
                var: new_var.clone(),
                set: Box::new(alpha_conversion(exp)),
                predicate: Box::new(subst(&alpha_conversion(predicate), var, &Exp::Var(new_var))),
            }
        }
        Exp::Pred {
            superset,
            subset,
            element,
        } => Exp::Pred {
            superset: Box::new(alpha_conversion(superset)),
            subset: Box::new(alpha_conversion(subset)),
            element: Box::new(alpha_conversion(element)),
        },
        Exp::TypeLift { superset, subset } => Exp::TypeLift {
            superset: Box::new(alpha_conversion(superset)),
            subset: Box::new(alpha_conversion(subset)),
        },
        Exp::Equal { left, right } => Exp::Equal {
            left: Box::new(alpha_conversion(left)),
            right: Box::new(alpha_conversion(right)),
        },
        Exp::Exists { set: ty } => Exp::Exists {
            set: Box::new(alpha_conversion(ty)),
        },
        Exp::Take {
            map,
            domain,
            codomain,
        } => Exp::Take {
            map: Box::new(alpha_conversion(map)),
            domain: Box::new(alpha_conversion(domain)),
            codomain: Box::new(alpha_conversion(codomain)),
        },
    }
}

pub fn reduce_if_top(e: &Exp) -> Option<Exp> {
    match e {
        Exp::App { func, arg } => {
            if let Exp::Lam { var, ty: _, body } = func.as_ref() {
                Some(subst(body, var, arg))
            } else {
                None
            }
        }
        _ => inductive_type_elim_reduce(e).ok(),
    }
}

pub fn reduce_one(e: &Exp) -> Option<Exp> {
    if let Some(e) = reduce_if_top(e) {
        return Some(e);
    }

    // challenge reduce exp if changed == true
    // return if [Some(reduced) = reduce(exp)]
    //    then {changed := true, recude}
    //    else exp
    let mut changed = false;
    let mut reduce_if = |e: &Exp| -> Exp {
        changed
            .then(|| reduce_one(e).inspect(|_| changed = true))
            .flatten()
            .unwrap_or(e.clone())
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
        Exp::IndType { ty, parameters } => {
            let parameters = parameters.iter().map(reduce_if).collect::<Vec<_>>();

            changed.then_some(Exp::IndType {
                ty: ty.clone(),
                parameters,
            })
        }
        Exp::IndCtor {
            ty,
            idx,
            parameters: parameter,
        } => {
            let parameters = parameter.iter().map(reduce_if).collect::<Vec<_>>();

            changed.then_some(Exp::IndCtor {
                ty: ty.clone(),
                idx: *idx,
                parameters,
            })
        }
        Exp::IndElim {
            ty,
            elim,
            return_type,
            sort,
            cases,
        } => {
            let elim = reduce_if(elim);
            let return_type = reduce_if(return_type);
            let cases = cases.iter().map(reduce_if).collect::<Vec<_>>();

            changed.then_some(Exp::IndElim {
                ty: ty.clone(),
                elim: Box::new(elim),
                return_type: Box::new(return_type),
                sort: *sort,
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
        Exp::Proof { prop: exp } => {
            let exp = reduce_if(exp);
            changed.then_some(Exp::Proof {
                prop: Box::new(exp),
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
            map,
            domain,
            codomain,
        } => {
            let map = reduce_if(map);
            let domain = reduce_if(domain);
            let codomain = reduce_if(codomain);

            changed.then_some(Exp::Take {
                map: Box::new(map),
                domain: Box::new(domain),
                codomain: Box::new(codomain),
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

// inefficient but simple
pub fn convertible(e1: &Exp, e2: &Exp) -> bool {
    is_alpha_eq(&normalize(e1), &normalize(e2))
}
