use crate::inductive::inductive_type_elim_reduction;

use super::coreexp::*;

pub fn shift(term: &CoreExp, by: isize, cutoff: usize) -> CoreExp {
    match term {
        CoreExp::Sort(sort) => CoreExp::Sort(*sort),
        CoreExp::Var(index) => {
            if *index >= cutoff {
                CoreExp::Var(((*index as isize) + by) as usize)
            } else {
                CoreExp::Var(*index)
            }
        }
        CoreExp::Prod { ty, body } => CoreExp::Prod {
            ty: Box::new(shift(ty, by, cutoff)),
            body: Box::new(shift(body, by, cutoff + 1)),
        },
        CoreExp::Lam { ty, body } => CoreExp::Lam {
            ty: Box::new(shift(ty, by, cutoff)),
            body: Box::new(shift(body, by, cutoff + 1)),
        },
        CoreExp::App { func, arg } => CoreExp::App {
            func: Box::new(shift(func, by, cutoff)),
            arg: Box::new(shift(arg, by, cutoff)),
        },
        CoreExp::IndType { ty, args } => CoreExp::IndType {
            ty: ty.clone(),
            args: args.iter().map(|arg| shift(arg, by, cutoff)).collect(),
        },
        CoreExp::IndTypeCst { ty, idx, args } => CoreExp::IndTypeCst {
            ty: ty.clone(),
            idx: *idx,
            args: args.iter().map(|arg| shift(arg, by, cutoff)).collect(),
        },
        CoreExp::IndTypeElim {
            ty,
            elim,
            return_type,
            cases,
        } => CoreExp::IndTypeElim {
            ty: ty.clone(),
            elim: Box::new(shift(elim, by, cutoff)),
            return_type: Box::new(shift(return_type, by, cutoff)),
            cases: cases.iter().map(|case| shift(case, by, cutoff)).collect(),
        },
        CoreExp::Cast { exp, to } => CoreExp::Cast {
            exp: Box::new(shift(exp, by, cutoff)),
            to: Box::new(shift(to, by, cutoff)),
        },
        CoreExp::Proof { exp } => CoreExp::Proof {
            exp: Box::new(shift(exp, by, cutoff)),
        },
        CoreExp::PowerSet { exp } => CoreExp::PowerSet {
            exp: Box::new(shift(exp, by, cutoff)),
        },
        CoreExp::SubSet { exp, predicate } => CoreExp::SubSet {
            exp: Box::new(shift(exp, by, cutoff)),
            predicate: Box::new(shift(predicate, by, cutoff + 1)),
        },
        CoreExp::Pred {
            superset,
            subset,
            element,
        } => CoreExp::Pred {
            superset: Box::new(shift(superset, by, cutoff)),
            subset: Box::new(shift(subset, by, cutoff)),
            element: Box::new(shift(element, by, cutoff)),
        },
        CoreExp::TypeLift { superset, subset } => CoreExp::TypeLift {
            superset: Box::new(shift(superset, by, cutoff)),
            subset: Box::new(shift(subset, by, cutoff)),
        },
        CoreExp::Equal { left, right } => CoreExp::Equal {
            left: Box::new(shift(left, by, cutoff)),
            right: Box::new(shift(right, by, cutoff)),
        },
        CoreExp::Exists { ty } => CoreExp::Exists {
            ty: Box::new(shift(ty, by, cutoff)),
        },
        CoreExp::Take {
            map,
            domain,
            codomain,
        } => CoreExp::Take {
            map: Box::new(shift(map, by, cutoff)),
            domain: Box::new(shift(domain, by, cutoff)),
            codomain: Box::new(shift(codomain, by, cutoff)),
        },
    }
}

pub fn subst(term: &CoreExp, sub: &CoreExp, index: usize) -> CoreExp {
    match term {
        CoreExp::Sort(sort) => CoreExp::Sort(*sort),
        CoreExp::Var(usize) => {
            if *usize == index {
                shift(sub, index as isize, 0)
            } else if *usize > index {
                CoreExp::Var(usize - 1)
            } else {
                CoreExp::Var(*usize)
            }
        }
        CoreExp::Prod { ty, body } => CoreExp::Prod {
            ty: Box::new(subst(ty, sub, index)),
            body: Box::new(subst(body, sub, index + 1)),
        },
        CoreExp::Lam { ty, body } => CoreExp::Lam {
            ty: Box::new(subst(ty, sub, index)),
            body: Box::new(subst(body, sub, index + 1)),
        },
        CoreExp::App { func, arg } => CoreExp::App {
            func: Box::new(subst(func, sub, index)),
            arg: Box::new(subst(arg, sub, index)),
        },
        CoreExp::IndType { ty, args } => CoreExp::IndType {
            ty: ty.clone(),
            args: args.iter().map(|arg| subst(arg, sub, index)).collect(),
        },
        CoreExp::IndTypeCst { ty, idx, args } => CoreExp::IndTypeCst {
            ty: ty.clone(),
            idx: *idx,
            args: args.iter().map(|arg| subst(arg, sub, index)).collect(),
        },
        CoreExp::IndTypeElim {
            ty,
            elim,
            return_type,
            cases,
        } => CoreExp::IndTypeElim {
            ty: ty.clone(),
            elim: Box::new(subst(elim, sub, index)),
            return_type: Box::new(subst(return_type, sub, index)),
            cases: cases.clone(),
        },
        CoreExp::Cast { exp, to } => CoreExp::Cast {
            exp: Box::new(subst(exp, sub, index)),
            to: Box::new(subst(to, sub, index)),
        },
        CoreExp::Proof { exp } => CoreExp::Proof {
            exp: Box::new(subst(exp, sub, index)),
        },
        CoreExp::PowerSet { exp } => CoreExp::PowerSet {
            exp: Box::new(subst(exp, sub, index)),
        },
        CoreExp::SubSet { exp, predicate } => CoreExp::SubSet {
            exp: Box::new(subst(exp, sub, index)),
            predicate: Box::new(subst(predicate, sub, index + 1)),
        },
        CoreExp::Pred {
            superset,
            subset,
            element,
        } => CoreExp::Pred {
            superset: Box::new(subst(superset, sub, index)),
            subset: Box::new(subst(subset, sub, index)),
            element: Box::new(subst(element, sub, index)),
        },
        CoreExp::TypeLift { superset, subset } => CoreExp::TypeLift {
            superset: Box::new(subst(superset, sub, index)),
            subset: Box::new(subst(subset, sub, index)),
        },
        CoreExp::Equal { left, right } => CoreExp::Equal {
            left: Box::new(subst(left, sub, index)),
            right: Box::new(subst(right, sub, index)),
        },
        CoreExp::Exists { ty } => CoreExp::Exists {
            ty: Box::new(subst(ty, sub, index)),
        },
        CoreExp::Take {
            map,
            domain,
            codomain,
        } => CoreExp::Take {
            map: Box::new(subst(map, sub, index)),
            domain: Box::new(subst(map, sub, index)),
            codomain: Box::new(subst(codomain, sub, index)),
        },
    }
}

pub fn reduce_if_top(e: &CoreExp) -> Option<CoreExp> {
    match e {
        CoreExp::App { func, arg } => {
            if let CoreExp::Lam { ty: _, body } = func.as_ref() {
                Some(subst(body, arg, 0))
            } else {
                None
            }
        }
        _ => inductive_type_elim_reduction(e).ok(),
    }
}

pub fn reduce_one(e: &CoreExp) -> Option<CoreExp> {
    if let Some(e) = reduce_if_top(e) {
        return Some(e);
    }
    match e {
        CoreExp::Sort(sort) => None,
        CoreExp::Var(_) => None,
        CoreExp::Prod { ty, body } => {
            if let Some(ty) = reduce_one(ty) {
                Some(CoreExp::Prod {
                    ty: Box::new(ty),
                    body: body.clone(),
                })
            } else if let Some(body) = reduce_one(body) {
                Some(CoreExp::Prod {
                    ty: ty.clone(),
                    body: Box::new(body),
                })
            } else {
                None
            }
        }
        CoreExp::Lam { ty, body } => {
            if let Some(ty) = reduce_one(ty) {
                Some(CoreExp::Lam {
                    ty: Box::new(ty),
                    body: body.clone(),
                })
            } else if let Some(body) = reduce_one(body) {
                Some(CoreExp::Lam {
                    ty: ty.clone(),
                    body: Box::new(body),
                })
            } else {
                None
            }
        }
        CoreExp::App { func, arg } => {
            if let Some(func) = reduce_one(func) {
                Some(CoreExp::App {
                    func: Box::new(func),
                    arg: arg.clone(),
                })
            } else if let Some(arg) = reduce_one(arg) {
                Some(CoreExp::App {
                    func: func.clone(),
                    arg: Box::new(arg),
                })
            } else {
                None
            }
        }
        CoreExp::IndType { ty, args } => {
            for (i, arg) in args.iter().enumerate() {
                if let Some(arg) = reduce_one(arg) {
                    let mut new_args = args.clone();
                    new_args[i] = arg;
                    return Some(CoreExp::IndType {
                        ty: ty.clone(),
                        args: new_args,
                    });
                }
            }
            None
        }
        CoreExp::IndTypeCst { ty, idx, args } => {
            for (i, arg) in args.iter().enumerate() {
                if let Some(arg) = reduce_one(arg) {
                    let mut new_args = args.clone();
                    new_args[i] = arg;
                    return Some(CoreExp::IndTypeCst {
                        ty: ty.clone(),
                        idx: *idx,
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
            if let Some(exp) = reduce_one(exp) {
                Some(CoreExp::Cast {
                    exp: Box::new(exp),
                    to: to.clone(),
                })
            } else if let Some(to) = reduce_one(to) {
                Some(CoreExp::Cast {
                    exp: exp.clone(),
                    to: Box::new(to),
                })
            } else {
                None
            }
        }
        CoreExp::Proof { exp } => {
            if let Some(exp) = reduce_one(exp) {
                Some(CoreExp::Proof { exp: Box::new(exp) })
            } else {
                None
            }
        }
        CoreExp::PowerSet { exp } => {
            if let Some(exp) = reduce_one(exp) {
                Some(CoreExp::PowerSet { exp: Box::new(exp) })
            } else {
                None
            }
        }
        CoreExp::SubSet { exp, predicate } => {
            if let Some(exp) = reduce_one(exp) {
                Some(CoreExp::SubSet {
                    exp: Box::new(exp),
                    predicate: predicate.clone(),
                })
            } else if let Some(predicate) = reduce_one(predicate) {
                Some(CoreExp::SubSet {
                    exp: exp.clone(),
                    predicate: Box::new(predicate),
                })
            } else {
                None
            }
        }
        CoreExp::Pred {
            superset,
            subset,
            element,
        } => {
            if let Some(superset) = reduce_one(superset) {
                Some(CoreExp::Pred {
                    superset: Box::new(superset),
                    subset: subset.clone(),
                    element: element.clone(),
                })
            } else if let Some(subset) = reduce_one(subset) {
                Some(CoreExp::Pred {
                    superset: superset.clone(),
                    subset: Box::new(subset),
                    element: element.clone(),
                })
            } else if let Some(element) = reduce_one(element) {
                Some(CoreExp::Pred {
                    superset: superset.clone(),
                    subset: subset.clone(),
                    element: Box::new(element),
                })
            } else {
                None
            }
        }
        CoreExp::TypeLift { superset, subset } => {
            if let Some(superset) = reduce_one(superset) {
                Some(CoreExp::TypeLift {
                    superset: Box::new(superset),
                    subset: subset.clone(),
                })
            } else if let Some(subset) = reduce_one(subset) {
                Some(CoreExp::TypeLift {
                    superset: superset.clone(),
                    subset: Box::new(subset),
                })
            } else {
                None
            }
        }
        CoreExp::Equal { left, right } => {
            if let Some(left) = reduce_one(left) {
                Some(CoreExp::Equal {
                    left: Box::new(left),
                    right: right.clone(),
                })
            } else if let Some(right) = reduce_one(right) {
                Some(CoreExp::Equal {
                    left: left.clone(),
                    right: Box::new(right),
                })
            } else {
                None
            }
        }
        CoreExp::Exists { ty } => {
            if let Some(ty) = reduce_one(ty) {
                Some(CoreExp::Exists { ty: Box::new(ty) })
            } else {
                None
            }
        }
        CoreExp::Take {
            map,
            domain,
            codomain,
        } => {
            if let Some(map) = reduce_one(map) {
                Some(CoreExp::Take {
                    map: Box::new(map),
                    domain: domain.clone(),
                    codomain: codomain.clone(),
                })
            } else if let Some(domain) = reduce_one(domain) {
                Some(CoreExp::Take {
                    map: map.clone(),
                    domain: Box::new(domain),
                    codomain: codomain.clone(),
                })
            } else if let Some(codomain) = reduce_one(codomain) {
                Some(CoreExp::Take {
                    map: map.clone(),
                    domain: domain.clone(),
                    codomain: Box::new(codomain),
                })
            } else {
                None
            }
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
    normalize(e1) == normalize(e2)
}
