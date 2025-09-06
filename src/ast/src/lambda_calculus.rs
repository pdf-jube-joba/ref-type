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

    pub fn binded_var(e: &Exp) -> Vec<Var> {
        // search for binded variables in expression recursively
        let mut v = vec![];
        match e {
            Exp::Sort(_)
            | Exp::Var(_)
            | Exp::IndType { ind_type_name: _ }
            | Exp::IndCst {
                ind_type_name: _,
                constructor_name: _,
            } => {}
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
            Exp::IndTypeElim {
                ind_type_name: _,
                eliminated_exp,
                return_type,
                cases,
            } => {
                v.extend(binded_var(eliminated_exp));
                v.extend(binded_var(return_type));
                for (_, exp) in cases {
                    v.extend(binded_var(exp));
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
}
