use crate::{ast::*, relation::*};
use std::collections::HashSet;

// 定義されていない型、存在しないコンストラクタ、網羅性のないパターンマッチなどをはじく
pub fn well_defined_inductives(gcxt: &GlobalContext, term: &Exp) -> Result<(), String> {
    todo!()
}

fn subst_rec(term1: Exp, fresh: &mut usize, mut substs: Vec<(Var, Exp)>) -> Exp {
    match term1 {
        Exp::Sort(_) => term1,
        Exp::Var(ref v) => substs
            .into_iter()
            .rev()
            .find_map(|(x, t)| if *v == x { Some(t) } else { None })
            .unwrap_or(term1),
        Exp::Prod(x, unbind, bind) => {
            let unbind = Box::new(subst_rec(*unbind, fresh, substs.clone()));
            let new_var = Var::Internal("new".to_string(), *fresh);
            *fresh += 1;
            substs.push((x, Exp::Var(new_var.clone())));
            let bind = Box::new(subst_rec(*bind, fresh, substs));
            Exp::Prod(new_var, unbind, bind)
        }
        Exp::Lam(x, unbind, bind) => {
            let unbind = Box::new(subst_rec(*unbind, fresh, substs.clone()));
            let new_var = Var::Internal("new".to_string(), *fresh);
            *fresh += 1;
            substs.push((x, Exp::Var(new_var.clone())));
            let bind = Box::new(subst_rec(*bind, fresh, substs));
            Exp::Lam(new_var, unbind, bind)
        }
        Exp::App(t1, t2) => Exp::App(
            Box::new(subst_rec(*t1, fresh, substs.clone())),
            Box::new(subst_rec(*t2, fresh, substs.clone())),
        ),
        Exp::IndTypeType { ind_type_name } => Exp::IndTypeType { ind_type_name },
        Exp::IndTypeCst {
            ind_type_name,
            constructor_name,
        } => Exp::IndTypeCst {
            ind_type_name,
            constructor_name,
        },
        Exp::IndTypeElim {
            ind_type_name,
            eliminated_exp,
            return_type,
            cases,
        } => Exp::IndTypeElim {
            ind_type_name,
            eliminated_exp: Box::new(subst_rec(*eliminated_exp, fresh, substs.clone())),
            return_type: Box::new(subst_rec(*return_type, fresh, substs.clone())),
            cases: cases
                .into_iter()
                .map(|(c, e)| (c, subst_rec(e, fresh, substs.clone())))
                .collect(),
        },
        Exp::Proof(t) => Exp::Proof(Box::new(subst_rec(*t, fresh, substs))),
        Exp::Pow(a) => Exp::Pow(Box::new(subst_rec(*a, fresh, substs))),
        Exp::Pred(a, b) => Exp::Pred(
            Box::new(subst_rec(*a, fresh, substs.clone())),
            Box::new(subst_rec(*b, fresh, substs)),
        ),
        Exp::Sub(x, unbind, bind) => {
            let unbind = Box::new(subst_rec(*unbind, fresh, substs.clone()));
            let new_var = Var::Internal("new".to_string(), *fresh);
            *fresh += 1;
            substs.push((x, Exp::Var(new_var.clone())));
            let bind = Box::new(subst_rec(*bind, fresh, substs));
            Exp::Sub(new_var, unbind, bind)
        }
    }
}

pub fn subst(term1: Exp, var: &Var, term2: &Exp) -> Exp {
    if matches!(var, Var::Unused) {
        return term1;
    }
    let mut fresh_var = std::cmp::max(fresh(&term1), fresh(term2));
    subst_rec(term1, &mut fresh_var, vec![(var.clone(), term2.clone())])
}

pub fn alpha_eq(term1: &Exp, term2: &Exp) -> bool {
    alpha_eq_rec(term1, term2, vec![])
}

fn alpha_eq_rec(term1: &Exp, term2: &Exp, mut bd: Vec<(Var, Var)>) -> bool {
    match (term1, term2) {
        (Exp::Var(v1), Exp::Var(v2)) => {
            bd.reverse();
            for (x, new_x) in bd {
                if x == *v1 && new_x == *v2 {
                    return true;
                } else if x == *v1 || new_x == *v2 {
                    return false;
                }
            }
            v1 == v2
        }
        (Exp::Sort(s1), Exp::Sort(s2)) => s1 == s2,
        (Exp::App(m1, n1), Exp::App(m2, n2)) => {
            alpha_eq_rec(m1.as_ref(), m2.as_ref(), bd.clone())
                && alpha_eq_rec(n1.as_ref(), n2.as_ref(), bd.clone())
        }
        (Exp::Prod(x1, m1, n1), Exp::Prod(x2, m2, n2)) => {
            alpha_eq_rec(m1.as_ref(), m2.as_ref(), bd.clone()) && {
                bd.push((x1.clone(), x2.clone()));
                alpha_eq_rec(n1, n2, bd)
            }
        }
        (Exp::Lam(x1, m1, n1), Exp::Lam(x2, m2, n2)) => {
            alpha_eq_rec(m1.as_ref(), m2.as_ref(), bd.clone()) && {
                bd.push((x1.clone(), x2.clone()));
                alpha_eq_rec(n1, n2, bd)
            }
        }
        (
            Exp::IndTypeType {
                ind_type_name: ind_type_1,
            },
            Exp::IndTypeType {
                ind_type_name: ind_type_2,
            },
        ) => ind_type_1 == ind_type_2,
        (
            Exp::IndTypeCst {
                ind_type_name: ind_type_name1,
                constructor_name: constructor_name1,
            },
            Exp::IndTypeCst {
                ind_type_name: ind_type_name2,
                constructor_name: constructor_name2,
            },
        ) => ind_type_name1 == ind_type_name2 && constructor_name1 == constructor_name2,
        (
            Exp::IndTypeElim {
                ind_type_name: ind_type_name1,
                eliminated_exp: exp1,
                return_type: expret1,
                cases: cases1,
            },
            Exp::IndTypeElim {
                ind_type_name: ind_type_name2,
                eliminated_exp: exp2,
                return_type: expret2,
                cases: cases2,
            },
        ) => {
            ind_type_name1 == ind_type_name2
                && exp1 == exp2
                && expret1 == expret2
                && cases1.len() == cases2.len()
                && cases1.iter().zip(cases2.iter()).all(|(e1, e2)| e1 == e2)
        }
        _ => false,
    }
}

// one_step
// (\x. t1) t2 -> t1[x := t2]
// Elim(Constructor, Q) -> ...
// (x: a := e) in Global context then x => e
pub fn top_reduction(gcxt: &GlobalContext, term: Exp) -> Option<Exp> {
    match term {
        Exp::Var(x) => gcxt.search_var_defined(x).map(|(_, e)| e.clone()),
        Exp::App(t1, t2) => match t1.as_ref() {
            Exp::Lam(x, _, m) => Some(subst(*m.clone(), x, t2.as_ref())),
            _ => None,
        },
        Exp::IndTypeElim {
            ind_type_name,
            eliminated_exp,
            return_type,
            cases,
        } => {
            let (head, argument) = utils::decompose_to_app_exps(*eliminated_exp);
            let Exp::IndTypeCst {
                ind_type_name: ind_type_name2,
                constructor_name,
            } = head
            else {
                return None;
            };
            if ind_type_name != ind_type_name2 {
                return None;
            }

            let inddefs = gcxt.indtype_defs(&ind_type_name)?;

            let constructor = inddefs.constructor(&constructor_name)?;
            let signature = inddefs.arity().signature().clone();

            let corresponding_cases = cases.iter().find_map(|(c, e)| {
                if c == &constructor_name {
                    Some(e.clone())
                } else {
                    None
                }
            })?;


            let ff_elim_q = {
                let new_var_c = Var::Internal("new_cst".to_string(), 0);

                let elim_cqf = Exp::IndTypeElim {
                    ind_type_name: ind_type_name2.clone(),
                    eliminated_exp: Box::new(Exp::Var(new_var_c.clone())),
                    return_type: return_type.clone(),
                    cases: cases.clone(),
                };

                utils::assoc_lam(
                    signature.clone(),
                    Exp::Lam(
                        new_var_c,
                        Box::new(utils::assoc_apply(
                            Exp::IndTypeType {
                                ind_type_name: ind_type_name.clone(),
                            },
                            signature.iter().map(|(x, _)| Exp::Var(x.clone())).collect(),
                        )),
                        Box::new(elim_cqf),
                    ),
                )
            };
            let t = constructor.recursor(ff_elim_q, corresponding_cases);
            Some(utils::assoc_apply(t, argument))
        }
        Exp::Pred(a, b) => {
            todo!()
        }
        _ => None,
    }
}

pub fn reduce(gcxt: &GlobalContext, term: Exp) -> Option<Exp> {
    if let Some(t) = top_reduction(gcxt, term.clone()) {
        return Some(t);
    }
    match term {
        Exp::Sort(_) | Exp::Var(_) => None,
        Exp::Prod(x, a, b) => {
            let new_a = reduce(gcxt, a.as_ref().clone());
            match new_a {
                Some(new_a) => Some(Exp::Prod(x, Box::new(new_a), b)),
                None => {
                    let new_b = reduce(gcxt, b.as_ref().clone())?;
                    Some(Exp::Prod(x, a, Box::new(new_b)))
                }
            }
        }
        Exp::Lam(x, a, b) => {
            let new_a = reduce(gcxt, a.as_ref().clone());
            match new_a {
                Some(new_a) => Some(Exp::Lam(x, Box::new(new_a), b)),
                None => {
                    let new_b = reduce(gcxt, b.as_ref().clone())?;
                    Some(Exp::Lam(x, a, Box::new(new_b)))
                }
            }
        }
        Exp::App(t1, t2) => {
            let new_t1 = reduce(gcxt, t1.as_ref().clone());
            match new_t1 {
                Some(new_t1) => Some(Exp::App(Box::new(new_t1), t2)),
                None => {
                    let new_t2 = reduce(gcxt, t2.as_ref().clone())?;
                    Some(Exp::App(t1, Box::new(new_t2)))
                }
            }
        }
        Exp::IndTypeType { ind_type_name: _ } => None,
        Exp::IndTypeCst {
            ind_type_name: _,
            constructor_name: _,
        } => None,
        Exp::IndTypeElim {
            ind_type_name,
            eliminated_exp,
            return_type,
            cases,
        } => {
            if let Some(eliminated_exp) = reduce(gcxt, *eliminated_exp.clone()) {
                return Some(Exp::IndTypeElim {
                    ind_type_name,
                    eliminated_exp: Box::new(eliminated_exp),
                    return_type,
                    cases,
                });
            }
            None
        }
        Exp::Proof(t) => Some(Exp::Proof(Box::new(reduce(gcxt, *t)?))),
        Exp::Pow(a) => Some(Exp::Pow(Box::new(reduce(gcxt, *a)?))),
        _ => todo!(),
    }
}

pub fn normalize(gcxt: &GlobalContext, mut term: Exp) -> Exp {
    while let Some(t) = reduce(gcxt, term.clone()) {
        term = t;
    }
    term
}

pub fn normalize_seq(gcxt: &GlobalContext, mut term: Exp) -> Vec<Exp> {
    let mut v = vec![term.clone()];
    while let Some(t) = reduce(gcxt, term.clone()) {
        v.push(t.clone());
        term = t;
    }
    v
}

pub fn beta_equiv(gcxt: &GlobalContext, term1: Exp, term2: Exp) -> bool {
    let term1 = normalize(gcxt, term1);
    let term2 = normalize(gcxt, term2);
    alpha_eq(&term1, &term2)
}

impl Exp {
    pub fn free_variable(&self) -> HashSet<Var> {
        match self {
            Exp::Sort(_) => HashSet::new(),
            Exp::Var(v) => vec![v.clone()].into_iter().collect(),
            Exp::Prod(x, a, b) => {
                let mut v = b.free_variable();
                v.remove(x);
                v.extend(a.free_variable());
                v
            }
            Exp::Lam(x, a, b) => {
                let mut v = b.free_variable();
                v.remove(x);
                v.extend(a.free_variable());
                v
            }
            Exp::App(e1, e2) => {
                let mut v = e1.free_variable();
                v.extend(e2.free_variable());
                v
            }
            Exp::IndTypeType { ind_type_name: _ } => HashSet::new(),
            Exp::IndTypeCst {
                ind_type_name: _,
                constructor_name: _,
            } => HashSet::new(),
            Exp::IndTypeElim {
                ind_type_name: _,
                eliminated_exp,
                return_type,
                cases,
            } => cases
                .iter()
                .map(|(_, e)| e)
                .flat_map(|e| e.free_variable())
                .chain(eliminated_exp.free_variable())
                .chain(return_type.free_variable())
                .collect(),
            Exp::Proof(a) => a.free_variable(),
            Exp::Sub(x, a, b) => {
                let mut v = b.free_variable();
                v.remove(x);
                v.extend(a.free_variable());
                v
            }
            Exp::Pow(a) => a.free_variable(),
            Exp::Pred(a, b) => {
                let mut v = a.free_variable();
                v.extend(b.free_variable());
                v
            }
        }
    }
}
