use crate::syntax::{Bind, Exp, Var};

pub mod variables {
    use super::*;

    pub fn fresh(v: &Var) -> usize {
        match v {
            Var::Str(_) => 0,
            Var::Internal(_, i) => *i + 1,
            Var::Unused => 0,
        }
    }

    pub fn fresh_var(e: &Exp) -> usize {
        let bv = binded_var(e);
        let fv = free_var(e);
        let mut max = 0;
        for v in bv.iter().chain(fv.iter()) {
            let f = fresh(v);
            if f > max {
                max = f;
            }
        }
        max
    }

    pub fn binded_var(e: &Exp) -> Vec<Var> {
        // search for binded variables in expression recursively
        let mut v = vec![];
        match e {
            Exp::Sort(_) | Exp::Var(_) => {}
            Exp::Prod(bind, a) => {
                v.push(bind.var.clone());
                v.extend(binded_var(&bind.ty));
                v.extend(binded_var(a));
            }
            Exp::Lam(bind, a) => {
                v.push(bind.var.clone());
                v.extend(binded_var(&bind.ty));
                v.extend(binded_var(a));
            }
            Exp::App(a, b) => {
                v.extend(binded_var(a));
                v.extend(binded_var(b));
            }
            Exp::IndType {
                ind_type_name: _,
                parameters,
            } => {
                v.extend(parameters.iter().flat_map(binded_var));
            }
            Exp::IndCst {
                ind_type_name: _,
                constructor_name: _,
                parameters,
            } => {
                v.extend(parameters.iter().flat_map(binded_var));
            }
            Exp::IndTypeElim {
                ind_type_name: _,
                eliminated_exp,
                return_type,
                cases,
            } => {
                v.extend(binded_var(eliminated_exp));
                v.extend(binded_var(return_type));
                for (_, args, exp) in cases {
                    v.extend(binded_var(exp));
                    v.extend(args.iter().cloned());
                }
            }
            Exp::Proof(exp) => {
                v.extend(binded_var(exp));
            }
            Exp::Pow(exp) => {
                v.extend(binded_var(exp));
            }
            Exp::Sub(bind, exp) => {
                v.push(bind.var.clone());
                v.extend(binded_var(&bind.ty));
                v.extend(binded_var(exp));
            }
            Exp::Pred(exp, exp1, exp2) => {
                v.extend(binded_var(exp));
                v.extend(binded_var(exp1));
                v.extend(binded_var(exp2));
            }
            Exp::Id(exp, exp1) => {
                v.extend(binded_var(exp));
                v.extend(binded_var(exp1));
            }
            Exp::Exists(exp) => {
                v.extend(binded_var(exp));
            }
            Exp::Take(bind, exp) => {
                v.push(bind.var.clone());
                v.extend(binded_var(&bind.ty));
                v.extend(binded_var(exp));
            }
        }
        v
    }

    pub fn free_var(e: &Exp) -> Vec<Var> {
        // search for free variables in expression recursively
        let mut v = vec![];
        match e {
            Exp::Sort(_) => {}
            Exp::Var(var) => {
                v.push(var.clone());
            }
            Exp::Prod(bind, a) => {
                v.extend(free_var(&bind.ty));
                let mut fv = free_var(a);
                fv.retain(|x| x != &bind.var);
                v.extend(fv);
            }
            Exp::Lam(bind, a) => {
                v.extend(free_var(&bind.ty));
                let mut fv = free_var(a);
                fv.retain(|x| x != &bind.var);
                v.extend(fv);
            }
            Exp::App(a, b) => {
                v.extend(free_var(a));
                v.extend(free_var(b));
            }
            Exp::IndType {
                ind_type_name: _,
                parameters,
            } => {
                for exp in parameters {
                    v.extend(free_var(exp));
                }
            }
            Exp::IndCst {
                ind_type_name: _,
                constructor_name: _,
                parameters,
            } => {
                for exp in parameters {
                    v.extend(free_var(exp));
                }
            }
            Exp::IndTypeElim {
                ind_type_name: _,
                eliminated_exp,
                return_type,
                cases,
            } => {
                v.extend(free_var(eliminated_exp));
                v.extend(free_var(return_type));
                for (_, args, exp) in cases {
                    let mut fv = free_var(exp);
                    for arg in args {
                        fv.retain(|x| x != arg);
                    }
                    v.extend(fv);
                }
            }
            Exp::Proof(exp) => {
                v.extend(free_var(exp));
            }
            Exp::Pow(exp) => {
                v.extend(free_var(exp));
            }
            Exp::Sub(bind, exp) => {
                v.extend(free_var(&bind.ty));
                let mut fv = free_var(exp);
                fv.retain(|x| x != &bind.var);
                v.extend(fv);
            }
            Exp::Pred(exp, exp1, exp2) => {
                v.extend(free_var(exp));
                v.extend(free_var(exp1));
                v.extend(free_var(exp2));
            }
            Exp::Id(exp, exp1) => {
                v.extend(free_var(exp));
                v.extend(free_var(exp1));
            }
            Exp::Exists(exp) => {
                v.extend(free_var(exp));
            }
            Exp::Take(bind, exp) => {
                v.extend(free_var(&bind.ty));
                let mut fv = free_var(exp);
                fv.retain(|x| x != &bind.var);
                v.extend(fv);
            }
        }
        v
    }
}

pub mod alpha_conversion {
    fn find_from_last(m: &Vec<(Var, Var)>, k: &Var) -> Option<Var> {
        m.iter()
            .rev()
            .find_map(|(k0, v)| if k0 == k { Some(v.clone()) } else { None })
    }

    use super::*;
    // renaming with alpha conversion
    // \x.\x. y -> \x0.\x1. y
    // \x. ((\z. x) (\z. z)) -> \x0. ((\z1. x0) (\z1. z1))
    fn alpha_conversion_rec(e: Exp, maps: &mut Vec<(Var, Var)>, new: usize) -> Exp {
        match e {
            Exp::Sort(sort) => Exp::Sort(sort),
            Exp::Var(var) => {
                if let Some(v) = find_from_last(maps, &var) {
                    Exp::Var(v.clone())
                } else {
                    Exp::Var(var)
                }
            }
            Exp::Prod(Bind { var, ty }, exp) => {
                // ty is not affected by the new variable
                let new_ty = alpha_conversion_rec(*ty, maps, new);
                let new_var = Var::Internal(format!("{}", var), new);
                maps.push((var.clone(), new_var.clone()));
                let new_exp = Exp::Prod(
                    Bind {
                        var: new_var,
                        ty: Box::new(new_ty),
                    },
                    Box::new(alpha_conversion_rec(*exp, maps, new + 1)),
                );
                maps.pop();
                new_exp
            }
            Exp::Lam(Bind { var, ty }, exp) => {
                let new_ty = alpha_conversion_rec(*ty, maps, new);
                let new_var = Var::Internal(format!("{}", var), new);
                maps.push((var.clone(), new_var.clone()));
                let new_exp = Exp::Lam(
                    Bind {
                        var: new_var,
                        ty: Box::new(new_ty),
                    },
                    Box::new(alpha_conversion_rec(*exp, maps, new + 1)),
                );
                maps.pop();
                new_exp
            }
            Exp::App(exp, exp1) => Exp::App(
                Box::new(alpha_conversion_rec(*exp, maps, new)),
                Box::new(alpha_conversion_rec(*exp1, maps, new)),
            ),
            Exp::IndType {
                ind_type_name,
                parameters,
            } => {
                let new_parameters = parameters
                    .into_iter()
                    .map(|exp| alpha_conversion_rec(exp, maps, new))
                    .collect();
                Exp::IndType {
                    ind_type_name,
                    parameters: new_parameters,
                }
            }
            Exp::IndCst {
                ind_type_name,
                constructor_name,
                parameters,
            } => {
                let new_parameters = parameters
                    .into_iter()
                    .map(|exp| alpha_conversion_rec(exp, maps, new))
                    .collect();
                Exp::IndCst {
                    ind_type_name,
                    constructor_name,
                    parameters: new_parameters,
                }
            }
            Exp::IndTypeElim {
                ind_type_name,
                eliminated_exp,
                return_type,
                cases,
            } => {
                let new_eliminated_exp = alpha_conversion_rec(*eliminated_exp, maps, new);
                let new_return_type = alpha_conversion_rec(*return_type, maps, new);
                let new_cases = cases
                    .into_iter()
                    .map(|(cst_name, args, exp)| {
                        let mut new_args = vec![];
                        let mut new_maps = maps.clone();
                        let mut current_new = new;
                        for arg in args {
                            let new_arg = Var::Internal(format!("{}", arg), current_new);
                            new_maps.push((arg.clone(), new_arg.clone()));
                            new_args.push(new_arg);
                            current_new += 1;
                        }
                        let new_exp = alpha_conversion_rec(exp, &mut new_maps, current_new);
                        (cst_name, new_args, new_exp)
                    })
                    .collect();
                Exp::IndTypeElim {
                    ind_type_name,
                    eliminated_exp: Box::new(new_eliminated_exp),
                    return_type: Box::new(new_return_type),
                    cases: new_cases,
                }
            }
            Exp::Proof(exp) => Exp::Proof(Box::new(alpha_conversion_rec(*exp, maps, new))),
            Exp::Pow(exp) => Exp::Pow(Box::new(alpha_conversion_rec(*exp, maps, new))),
            Exp::Sub(bind, exp) => {
                let new_ty = alpha_conversion_rec(*bind.ty, maps, new);
                let new_var = Var::Internal(format!("{}", bind.var), new);
                maps.push((bind.var.clone(), new_var.clone()));
                let new_exp = Exp::Sub(
                    Bind {
                        var: new_var,
                        ty: Box::new(new_ty),
                    },
                    Box::new(alpha_conversion_rec(*exp, maps, new + 1)),
                );
                maps.pop();
                new_exp
            }
            Exp::Pred(exp, exp1, exp2) => Exp::Pred(
                Box::new(alpha_conversion_rec(*exp, maps, new)),
                Box::new(alpha_conversion_rec(*exp1, maps, new)),
                Box::new(alpha_conversion_rec(*exp2, maps, new)),
            ),
            Exp::Id(exp, exp1) => Exp::Id(
                Box::new(alpha_conversion_rec(*exp, maps, new)),
                Box::new(alpha_conversion_rec(*exp1, maps, new)),
            ),
            Exp::Exists(exp) => Exp::Exists(Box::new(alpha_conversion_rec(*exp, maps, new))),
            Exp::Take(bind, exp) => {
                let new_ty = alpha_conversion_rec(*bind.ty, maps, new);
                let new_var = Var::Internal(format!("{}", bind.var), new);
                maps.push((bind.var.clone(), new_var.clone()));
                let new_exp = Exp::Take(
                    Bind {
                        var: new_var,
                        ty: Box::new(new_ty),
                    },
                    Box::new(alpha_conversion_rec(*exp, maps, new + 1)),
                );
                maps.pop();
                new_exp
            }
        }
    }

    // free variable \cap bounded variable = \emptyset
    pub fn alpha_conversion(e: Exp) -> Exp {
        let new = variables::fresh_var(&e);
        alpha_conversion_rec(e, &mut vec![], new)
    }

    pub fn alpha_eq_rec(e1: &Exp, e2: &Exp, r: &mut Vec<(Var, Var)>) -> bool {
        match (e1, e2) {
            (Exp::Sort(s1), Exp::Sort(s2)) => s1 == s2,
            (Exp::Var(v1), Exp::Var(v2)) => {
                if let Some(v) = find_from_last(r, v1) {
                    &v == v2
                } else {
                    v1 == v2
                }
            }
            (Exp::Prod(b1, e1), Exp::Prod(b2, e2)) => {
                alpha_eq_rec(&b1.ty, &b2.ty, r);
                r.push((b1.var.clone(), b2.var.clone()));
                let res = alpha_eq_rec(e1, e2, r);
                r.pop();
                res
            }
            (Exp::Lam(b1, e1), Exp::Lam(b2, e2)) => {
                alpha_eq_rec(&b1.ty, &b2.ty, r);
                r.push((b1.var.clone(), b2.var.clone()));
                let res = alpha_eq_rec(e1, e2, r);
                r.pop();
                res
            }
            (Exp::App(f1, a1), Exp::App(f2, a2)) => {
                alpha_eq_rec(f1, f2, r) && alpha_eq_rec(a1, a2, r)
            }
            (
                Exp::IndType {
                    ind_type_name: n1,
                    parameters: p1,
                },
                Exp::IndType {
                    ind_type_name: n2,
                    parameters: p2,
                },
            ) => {
                n1 == n2
                    && p1.len() == p2.len()
                    && p1.iter().zip(p2.iter()).all(|(x, y)| alpha_eq_rec(x, y, r))
            }
            (
                Exp::IndCst {
                    ind_type_name: n1,
                    constructor_name: c1,
                    parameters: p1,
                },
                Exp::IndCst {
                    ind_type_name: n2,
                    constructor_name: c2,
                    parameters: p2,
                },
            ) => {
                n1 == n2
                    && c1 == c2
                    && p1.len() == p2.len()
                    && p1.iter().zip(p2.iter()).all(|(x, y)| alpha_eq_rec(x, y, r))
            }
            (
                Exp::IndTypeElim {
                    ind_type_name: n1,
                    eliminated_exp: e1,
                    return_type: rt1,
                    cases: cs1,
                },
                Exp::IndTypeElim {
                    ind_type_name: n2,
                    eliminated_exp: e2,
                    return_type: rt2,
                    cases: cs2,
                },
            ) => {
                n1 == n2
                    && alpha_eq_rec(e1, e2, r)
                    && alpha_eq_rec(rt1, rt2, r)
                    && cs1.len() == cs2.len()
                    && cs1.iter().zip(cs2.iter()).all(|(x, y)| {
                        let (cst1, args1, exp1) = x;
                        let (cst2, args2, exp2) = y;
                        if cst1 != cst2 || args1.len() != args2.len() {
                            return false;
                        }
                        for (a1, a2) in args1.iter().zip(args2.iter()) {
                            r.push((a1.clone(), a2.clone()));
                        }
                        let res = alpha_eq_rec(exp1, exp2, r);
                        for _ in args1 {
                            r.pop();
                        }
                        res
                    })
            }
            (Exp::Proof(e1), Exp::Proof(e2)) => alpha_eq_rec(e1, e2, r),
            (Exp::Pow(e1), Exp::Pow(e2)) => alpha_eq_rec(e1, e2, r),
            (Exp::Sub(b1, e1), Exp::Sub(b2, e2)) => {
                alpha_eq_rec(&b1.ty, &b2.ty, r);
                r.push((b1.var.clone(), b2.var.clone()));
                let res = alpha_eq_rec(e1, e2, r);
                r.pop();
                res
            }
            (Exp::Pred(a1, b1, c1), Exp::Pred(a2, b2, c2)) => {
                alpha_eq_rec(a1, a2, r) && alpha_eq_rec(b1, b2, r) && alpha_eq_rec(c1, c2, r)
            }
            (Exp::Id(a1, b1), Exp::Id(a2, b2)) => {
                alpha_eq_rec(a1, a2, r) && alpha_eq_rec(b1, b2, r)
            }
            (Exp::Exists(e1), Exp::Exists(e2)) => alpha_eq_rec(e1, e2, r),
            (Exp::Take(b1, e1), Exp::Take(b2, e2)) => {
                alpha_eq_rec(&b1.ty, &b2.ty, r);
                r.push((b1.var.clone(), b2.var.clone()));
                let res = alpha_eq_rec(e1, e2, r);
                r.pop();
                res
            }
            (_, _) => false,
        }
    }

    pub fn alpha_eq(e1: &Exp, e2: &Exp) -> bool {
        alpha_eq_rec(e1, e2, &mut vec![])
    }
}

mod subst {
    use super::*;

    // subst e[x := v]
    // does not handle free variables capture
    // but care bind
    fn subst_unsafe(e: Exp, x: &Var, v: &Exp) -> Exp {
        match e {
            Exp::Sort(sort) => Exp::Sort(sort),
            Exp::Var(var) => {
                if &var == x {
                    v.clone()
                } else {
                    Exp::Var(var)
                }
            }
            Exp::Prod(bind, exp) => {
                if bind.var == *x {
                    Exp::Prod(bind, exp)
                } else {
                    Exp::Prod(
                        Bind {
                            var: bind.var,
                            ty: Box::new(subst_unsafe(*bind.ty, x, v)),
                        },
                        Box::new(subst_unsafe(*exp, x, v)),
                    )
                }
            }
            Exp::Lam(bind, exp) => todo!(),
            Exp::App(exp, exp1) => todo!(),
            Exp::IndType {
                ind_type_name,
                parameters,
            } => todo!(),
            Exp::IndCst {
                ind_type_name,
                constructor_name,
                parameters,
            } => todo!(),
            Exp::IndTypeElim {
                ind_type_name,
                eliminated_exp,
                return_type,
                cases,
            } => todo!(),
            Exp::Proof(exp) => todo!(),
            Exp::Pow(exp) => todo!(),
            Exp::Sub(bind, exp) => todo!(),
            Exp::Pred(exp, exp1, exp2) => todo!(),
            Exp::Id(exp, exp1) => todo!(),
            Exp::Exists(exp) => todo!(),
            Exp::Take(bind, exp) => todo!(),
        }
    }
}
