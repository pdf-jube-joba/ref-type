use std::collections::HashMap;

use either::Either;

use crate::ast::*;

fn fresh_var(v: &Var) -> usize {
    match v {
        Var::Str(_) => 0,
        Var::Internal(_, i) => *i + 1,
        Var::Unused => 0,
    }
}

// term に含まれるどの変数よりも大きい数を返す
fn fresh(term: &Exp) -> usize {
    match term {
        Exp::Sort(_) => 0,
        Exp::Var(v) => fresh_var(v),
        Exp::Prod(x, t1, t2) => {
            let v1 = fresh(t1);
            let v2 = fresh(t2);
            let v = std::cmp::max(v1, v2);
            std::cmp::max(fresh_var(x), v)
        }
        Exp::Lam(x, t1, t2) => {
            let v1 = fresh(t1);
            let v2 = fresh(t2);
            let v = std::cmp::max(v1, v2);
            std::cmp::max(fresh_var(x), v)
        }
        Exp::App(t1, t2) => {
            let v1 = fresh(t1);
            let v2 = fresh(t2);
            std::cmp::max(v1, v2)
        }
        _ => {
            unimplemented!("fresh is umimplemented")
        }
    }
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
        Exp::IndTypeType {
            ind_type_def,
            argument,
        } => Exp::IndTypeType {
            ind_type_def,
            argument: argument
                .into_iter()
                .map(|exp| subst_rec(exp, fresh, substs.clone()))
                .collect(),
        },
        Exp::IndTypeCst {
            ind_type_def,
            projection,
            argument,
        } => Exp::IndTypeCst {
            ind_type_def,
            projection,
            argument: argument
                .into_iter()
                .map(|exp| subst_rec(exp, fresh, substs.clone()))
                .collect(),
        },
        Exp::IndTypeElim {
            ind_type_def,
            eliminated_exp,
            return_type,
            cases,
        } => Exp::IndTypeElim {
            ind_type_def,
            eliminated_exp: Box::new(subst_rec(*eliminated_exp, fresh, substs.clone())),
            return_type: Box::new(subst_rec(*return_type, fresh, substs.clone())),
            cases: cases
                .into_iter()
                .map(|e| subst_rec(e, fresh, substs.clone()))
                .collect(),
        },
        _ => unimplemented!("subst is unimplemented"),
    }
}

pub fn subst(term1: Exp, var: &Var, term2: &Exp) -> Exp {
    let mut fresh_var = std::cmp::max(fresh(&term1), fresh(term2));
    subst_rec(term1, &mut fresh_var, vec![(var.clone(), term2.clone())])
}

pub fn alpha_eq(term1: &Exp, term2: &Exp) -> bool {
    alpha_eq_rec(term1, term2, vec![])
}

fn alpha_eq_rec(term1: &Exp, term2: &Exp, mut bd: Vec<(Var, Var)>) -> bool {
    match (term1, term2) {
        (Exp::Var(v1), Exp::Var(v2)) => {
            for (x, new_x) in bd {
                if x == *v2 && new_x == *v1 {
                    return true;
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
        _ => false,
    }
}

// one_step
fn weak_reduction(term: Exp) -> Option<Exp> {
    match term {
        Exp::App(t1, t2) => match t1.as_ref() {
            Exp::Lam(x, _, m) => Some(subst(*m.clone(), x, t2.as_ref())),
            _ => {
                let new_t1 = weak_reduction(t1.as_ref().clone())?;
                Some(Exp::App(Box::new(new_t1), Box::new(t2.as_ref().clone())))
            }
        },
        Exp::IndTypeElim {
            ind_type_def,
            eliminated_exp,
            return_type,
            cases,
        } => {
            let Exp::IndTypeCst {
                ind_type_def: ind_type_def2,
                projection,
                argument,
            } = *eliminated_exp
            else {
                return None;
            };
            if ind_type_def != ind_type_def2 {
                return None;
            }
            let inductives::IndTypeDefs {
                variable,
                signature,
                constructor,
            } = ind_type_def.clone();

            let rec = {
                let new_var_c = Var::Internal("new_cst".to_string(), 0);

                let elim = Exp::IndTypeElim {
                    ind_type_def: ind_type_def.clone(),
                    eliminated_exp: Box::new(Exp::Var(new_var_c.clone())),
                    return_type: return_type.clone(),
                    cases: cases.clone(),
                };
                utils::assoc_lam(
                    signature.signature().to_vec(),
                    Exp::Lam(
                        new_var_c,
                        Box::new(Exp::IndTypeType {
                            ind_type_def: ind_type_def.clone(),
                            argument: signature
                                .signature()
                                .iter()
                                .map(|(x, _)| Exp::Var(x.clone()))
                                .collect(),
                        }),
                        Box::new(elim),
                    ),
                )
            };
            let t = constructor[projection].recursor(cases[projection].clone(), rec);
            Some(utils::assoc_apply(t, argument))
        }
        _ => None,
    }
}

fn reduce(term: Exp) -> Option<Exp> {
    if let Some(t) = weak_reduction(term.clone()) {
        return Some(t);
    }
    match term {
        Exp::Sort(_) | Exp::Var(_) => None,
        Exp::Prod(x, a, b) => {
            let new_a = reduce(a.as_ref().clone());
            match new_a {
                Some(new_a) => Some(Exp::Prod(x, Box::new(new_a), b)),
                None => {
                    let new_b = reduce(b.as_ref().clone())?;
                    Some(Exp::Prod(x, a, Box::new(new_b)))
                }
            }
        }
        Exp::Lam(x, a, b) => {
            let new_a = reduce(a.as_ref().clone());
            match new_a {
                Some(new_a) => Some(Exp::Lam(x, Box::new(new_a), b)),
                None => {
                    let new_b = reduce(b.as_ref().clone())?;
                    Some(Exp::Lam(x, a, Box::new(new_b)))
                }
            }
        }
        Exp::App(t1, t2) => {
            let new_t1 = reduce(t1.as_ref().clone());
            match new_t1 {
                Some(new_t1) => Some(Exp::App(Box::new(new_t1), t2)),
                None => {
                    let new_t2 = reduce(t2.as_ref().clone())?;
                    Some(Exp::App(t1, Box::new(new_t2)))
                }
            }
        }
        Exp::IndTypeType {
            ind_type_def,
            mut argument,
        } => {
            for arg in &mut argument {
                if let Some(e) = reduce(arg.clone()) {
                    *arg = e;
                    return Some(Exp::IndTypeType {
                        ind_type_def,
                        argument,
                    });
                }
            }
            None
        }
        Exp::IndTypeCst {
            ind_type_def,
            projection,
            mut argument,
        } => {
            for arg in &mut argument {
                if let Some(e) = reduce(arg.clone()) {
                    *arg = e;
                    return Some(Exp::IndTypeCst {
                        ind_type_def,
                        projection,
                        argument,
                    });
                }
            }
            None
        }
        Exp::IndTypeElim {
            ind_type_def,
            eliminated_exp,
            return_type,
            cases,
        } => {
            if let Some(eliminated_exp) = reduce(*eliminated_exp.clone()) {
                return Some(Exp::IndTypeElim {
                    ind_type_def,
                    eliminated_exp: Box::new(eliminated_exp),
                    return_type,
                    cases,
                });
            }

            None
        }
    }
}

fn normalize(mut term: Exp) -> Exp {
    while let Some(t) = reduce(term.clone()) {
        term = t;
    }
    term
}

fn beta_equiv(term1: Exp, term2: Exp) -> bool {
    let term1 = normalize(term1);
    let term2 = normalize(term2);
    alpha_eq(&term1, &term2)
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Context(Vec<(Var, Exp)>);

impl Context {
    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    fn poped(&self) -> Option<(Self, (Var, Exp))> {
        let mut s = self.clone();
        let d = s.0.pop()?;
        Some((s, d))
    }
    fn push_decl(&mut self, d: (Var, Exp)) {
        self.0.push(d);
    }
    fn search_var_exp(&self, var: &Var) -> Option<&Exp> {
        self.0.iter().find(|(v, e)| v == var).map(|e| &e.1)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum State {
    Success,
    Fail,
    Wait,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Judgement {
    // WellFormedContext(Context),
    TypeCheck(Context, Either<Exp, usize>, Either<Exp, usize>),
    TypeInfer(Context, Either<Exp, usize>),
    // Prove(Context, Either<Exp, usize>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Conditions {
    ContextHasVar(Context, Var, Either<Exp, usize>), // (x: T) in G
    Convertible(Either<Exp, usize>, Either<Exp, usize>), // t1 =^beta t2
    ReduceToSort(Either<Exp, usize>, Either<Sort, usize>), // t ->^beta* sort
    ReduceToProd(Either<Exp, usize>, Either<(Var, Exp, Exp), usize>), // t ->^beta* (x: a) -> b
}

fn cond_step(cond: Conditions) -> Result<(State, Option<SubstKind>), ()> {
    match cond {
        Conditions::ContextHasVar(cxt, x, t) => {
            let Some(t2) = cxt.search_var_exp(&x) else {
                return Ok((State::Fail, None));
            };
            match t {
                Either::Left(t1) => {
                    if alpha_eq(&t1, t2) {
                        Ok((State::Success, None))
                    } else {
                        Ok((State::Fail, None))
                    }
                },
                Either::Right(n) => {
                    Ok((State::Success, Some(SubstKind::NumToExp(n, t2.clone()))))
                },
            }
        },
        Conditions::Convertible(t1, t2) => {
            let (Either::Left(t1), Either::Left(t2)) = (t1, t2) else {
                return Err(());
            };
            if beta_equiv(t1, t2) {
                Ok((State::Success, None))
            } else {
                Ok((State::Fail, None))
            }
        },
        Conditions::ReduceToSort(_, _) => todo!(),
        Conditions::ReduceToProd(_, _) => todo!(),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Leaf {
    Judge(Judgement, State),
    Cond(Conditions, State),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DerivationLabel {
    EmptyContext,
    VariableContext,
    Variable,
    Axiom,
    Conv,
    ProdForm,
    ProdIntro,
    ProdElim,
}

fn step(judgement: Judgement) -> Option<(DerivationLabel, Vec<Judgement>)> {
    match judgement {
        Judgement::TypeCheck(_, _, _) => todo!(),
        Judgement::TypeInfer(_, _) => todo!(),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PartialDerivationTree {
    LeafEnd(Leaf),
    Node {
        head: Judgement,
        rel: DerivationLabel,
        child: Vec<PartialDerivationTree>,
    },
}

impl PartialDerivationTree {
    pub fn is_complete(&self) -> bool {
        todo!()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SubstKind {
    NumToExp(usize, Exp), // ?n <- e
    Prod(usize, (Var, Exp, Either<Exp, usize>)),
    Subst(usize, (Either<Exp, usize>, Either<Var, usize>, Exp)),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Subst(HashMap<usize, Exp>);

impl Subst {
    fn no() -> Self {
        Subst(HashMap::new())
    }
}

pub mod make_tree {
    use super::*;

    fn subst(der_tree: &mut PartialDerivationTree, subst: &Subst) {
        todo!()
    }

    // Some を返すのは進展があったとき
    fn step_tree(der_tree: &mut PartialDerivationTree) -> Option<Subst> {
        match der_tree {
            PartialDerivationTree::LeafEnd(Leaf::Cond(cond, state)) => {
                if *state == State::Success || *state == State::Fail {
                    return None;
                }
                match cond {
                    Conditions::ContextHasVar(cxt, x, s) => {
                        let Some(t) = cxt.search_var_exp(x) else {
                            *state = State::Fail;
                            return Some(Subst::no());
                        };
                        match s {
                            Either::Left(expected_t) => {
                                if t == expected_t {
                                    *state = State::Fail;
                                    Some(Subst::no())
                                } else {
                                    *state = State::Success;
                                    Some(Subst::no())
                                }
                            }
                            Either::Right(unspec) => {
                                *state = State::Success;
                                let m = HashMap::from_iter(vec![(*unspec, t.clone())]);
                                Some(Subst(m))
                            }
                        }
                    }
                    Conditions::Convertible(t1, t2) => match (t1, t2) {
                        (Either::Left(t1), Either::Left(t2)) => {
                            if beta_equiv(t1.clone(), t2.clone()) {
                                *state = State::Success;
                                Some(Subst::no())
                            } else {
                                *state = State::Fail;
                                Some(Subst::no())
                            }
                        }
                        _ => None,
                    },
                    Conditions::ReduceToSort(Either::Left(t), s) => {
                        let t = normalize(t.clone());
                        let Exp::Sort(s_t) = t else {
                            *state = State::Fail;
                            return Some(Subst::no());
                        };
                        match s {
                            Either::Left(s) => {
                                if *s == s_t {
                                    *state = State::Success;
                                } else {
                                    *state = State::Fail;
                                }
                                Some(Subst::no())
                            }
                            Either::Right(i) => {
                                *state = State::Success;
                                let m = HashMap::from_iter(vec![(*i, Exp::Sort(s_t.clone()))]);
                                Some(Subst(m))
                            }
                        }
                    }
                    Conditions::ReduceToSort(Either::Right(t), s) => None,
                    Conditions::ReduceToProd(Either::Left(t), p) => {
                        let t = normalize(t.clone());
                        let Exp::Prod(xt, at, bt) = t else {
                            *state == State::Fail;
                            return Some(Subst::no());
                        };
                        match p {
                            Either::Left(p) => {
                                // if beta_equiv(p.clone(), t.clone()) {
                                //     *state = State::Success;
                                // } else {
                                //     *state = State::Fail;
                                // }
                                // Some(Subst::no())
                                todo!()
                            }
                            Either::Right(_) => todo!(),
                        }
                    }
                    Conditions::ReduceToProd(Either::Right(_), _) => None,
                }
            }
            PartialDerivationTree::LeafEnd(Leaf::Judge(judge, cond)) => match judge {
                // Judgement::WellFormedContext(cxt) => {
                //     if let Some(d) = cxt.poped() {
                //         let leaf: Leaf = Leaf::Judge({
                //             todo!()
                //         }, State::Wait);
                //         *der_tree = PartialDerivationTree::Node {
                //             head: judge.clone(),
                //             rel: DerivationLabel::VariableContext,
                //             child: vec![PartialDerivationTree::LeafEnd(leaf)],
                //         };
                //         Some(Subst::no())
                //     } else {
                //         *der_tree = PartialDerivationTree::Node {
                //             head: judge.clone(),
                //             rel: DerivationLabel::EmptyContext,
                //             child: vec![],
                //         };
                //         Some(Subst::no())
                //     }
                // }
                Judgement::TypeCheck(_, _, _) => todo!(),
                Judgement::TypeInfer(_, _) => todo!(),
                // Judgement::Prove(_, _) => todo!(),
            },
            PartialDerivationTree::Node { head, rel, child } => {
                for c in child {
                    if let Some(a) = step_tree(c) {
                        return Some(a);
                    }
                }
                None
            }
        }
    }
}

// pub fn type_check(
//     gcxt: &GlobalContext,
//     cxt: Context,
//     term1: Exp,
//     term2: Exp,
// ) -> Result<(), String> {
//     let t = type_infer(gcxt, cxt, term1)?;
//     if beta_equiv(gcxt, t.clone(), term2.clone()) {
//         Ok(())
//     } else {
//         Err(format!("infered {t:?} but is not equivalent to {term2:?}"))
//     }
// }

// // Γ |- t |> (s in S) かどうか
// fn type_infered_to_sort(gcxt: &GlobalContext, cxt: Context, term: Exp) -> Result<Sort, String> {
//     let mut sort_of_term = type_infer(gcxt, cxt, term.clone())?;
//     while let Some(t) = weak_reduction(gcxt, sort_of_term.clone()) {
//         sort_of_term = t;
//     }
//     match sort_of_term {
//         Exp::Sort(s) => Ok(s),
//         _ => Err(format!("type {term:?} has type not in sort")),
//     }
// }

// fn type_infered_to_prod(
//     gcxt: &GlobalContext,
//     cxt: Context,
//     term: Exp,
// ) -> Result<(Var, Exp, Exp), String> {
//     let mut sort_of_term = type_infer(gcxt, cxt, term.clone())?;
//     while let Some(t) = weak_reduction(gcxt, sort_of_term.clone()) {
//         sort_of_term = t;
//     }
//     match sort_of_term {
//         Exp::Prod(x, a, b) => Ok((x, *a, *b)),
//         _ => Err(format!("type {term:?} has type not in sort")),
//     }
// }

// pub fn type_infer(gcxt: &GlobalContext, mut cxt: Context, term1: Exp) -> Result<Exp, String> {
//     match term1 {
//         Exp::Sort(sort) => match sort.type_of_sort() {
//             Some(s) => Ok(Exp::Sort(s)),
//             None => Err(format!("sort {sort:?} has no type")),
//         },
//         Exp::Var(x) => {
//             let res = find_var(&cxt, &x);
//             match res {
//                 Some(t) => Ok(t.clone()),
//                 None => Err(format!("not found variable {x:?}")),
//             }
//         }
//         Exp::Prod(x, t, t2) => {
//             // sort of t
//             let sort_of_t = type_infered_to_sort(gcxt, cxt.clone(), *t.clone())?;
//             // sort of t2
//             cxt.push((x, *t));
//             let sort_of_t2 = type_infered_to_sort(gcxt, cxt, *t2.clone())?;

//             match sort_of_t.relation_of_sort(sort_of_t2) {
//                 Some(s) => Ok(Exp::Sort(s)),
//                 None => Err(format!("sort {sort_of_t} {sort_of_t2} has no rel")),
//             }
//         }
//         Exp::Lam(x, t, m) => {
//             let _sort = type_infered_to_sort(gcxt, cxt.clone(), *t.clone())?;
//             cxt.push((x.clone(), *t.clone()));

//             let type_m = type_infer(gcxt, cxt, *m.clone())?;

//             Ok(Exp::Prod(x, t, Box::new(type_m)))
//         }
//         Exp::App(t1, t2) => {
//             let (x, a, b) = type_infered_to_prod(gcxt, cxt.clone(), *t1.clone())?;
//             type_check(gcxt, cxt.clone(), *t2.clone(), a)?;
//             Ok(subst(b, &x, &t2))
//         }
//         _ => todo!("not implemented"),
//     }
// }

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn subst_test() {}
}
