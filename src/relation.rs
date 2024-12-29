use std::{collections::HashMap, fmt::Display};

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
    fn pretty_print(&self) -> String {
        self.0.iter().fold(String::new(), |s1, (v, t)| {
            format!("{s1} ({v}: {}", t.pretty_print())
        })
    }
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

impl Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                State::Success => "Success",
                State::Fail => "Fail",
                State::Wait => "Wait",
            }
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Judgement {
    // WellFormedContext(Context),
    TypeCheck(Context, Either<Exp, usize>, Either<Exp, usize>),
    TypeInfer(Context, Either<Exp, usize>),
    // Prove(Context, Either<Exp, usize>),
}

impl Display for Judgement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Judgement::TypeCheck(context, either, either1) => format!(
                "{} |- {}: {}",
                context.pretty_print(),
                eitexp_to(either),
                eitexp_to(either1)
            ),
            Judgement::TypeInfer(context, either) => {
                format!("{} |- {}: ?", context.pretty_print(), eitexp_to(either),)
            }
        };
        write!(f, "{}", s)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Conditions {
    ContextHasVar(Context, Var, Either<Exp, usize>), // (x: T) in G
    Convertible(Either<Exp, usize>, Either<Exp, usize>), // t1 =^beta t2
    ReduceToSort(Either<Exp, usize>, Either<Sort, usize>), // t ->^beta* sort
    ReduceToProd(Either<Exp, usize>, Either<(Var, Exp, Exp), usize>), // t ->^beta* (x: a) -> b
    AxiomSort(Sort, Sort),                           // (s1: s2) in A
    RelationSort(Sort, Sort, Sort),                  // (s1, s2, s3) in A
}

fn eitexp_to(e: &Either<Exp, usize>) -> String {
    match e {
        Either::Left(l) => l.pretty_print(),
        Either::Right(r) => format!("?{r}"),
    }
}

fn eitsort_to(e: &Either<Sort, usize>) -> String {
    match e {
        Either::Left(l) => format!("{l}"),
        Either::Right(r) => format!("?{r}"),
    }
}

fn eitprod_to(e: &Either<(Var, Exp, Exp), usize>) -> String {
    match e {
        Either::Left((x, a, b)) => format!("({x}: {}) -> {}", a.pretty_print(), b.pretty_print()),
        Either::Right(r) => format!("?{r}"),
    }
}

impl Conditions {
    fn pretty_print(&self) -> String {
        match self {
            Conditions::ContextHasVar(context, var, either) => format!(
                "({var}: {}) in {}",
                eitexp_to(either),
                context.pretty_print()
            ),
            Conditions::Convertible(either, either1) => {
                format!("{} =~ {}", eitexp_to(either), eitexp_to(either1))
            }
            Conditions::ReduceToSort(either, either1) => {
                format!("{} ->*_sort {}", eitexp_to(either), eitsort_to(either1))
            }
            Conditions::ReduceToProd(either, either1) => {
                format!("{} ->*_prod {}", eitexp_to(either), eitprod_to(either1))
            }
            Conditions::AxiomSort(sort, sort1) => {
                format!("{sort}: {sort1} in Axm")
            }
            Conditions::RelationSort(sort, sort1, sort2) => {
                format!("({sort}, {sort1}, {sort2}) in Rel")
            }
        }
    }
}

// fn cond_step(cond: Conditions) -> Result<(State, Option<SubstKind>), ()> {
//     match cond {
//         Conditions::ContextHasVar(cxt, x, t) => {
//             let Some(t2) = cxt.search_var_exp(&x) else {
//                 return Ok((State::Fail, None));
//             };
//             match t {
//                 Either::Left(t1) => {
//                     if alpha_eq(&t1, t2) {
//                         Ok((State::Success, None))
//                     } else {
//                         Ok((State::Fail, None))
//                     }
//                 }
//                 Either::Right(n) => Ok((State::Success, Some(SubstKind::NumToExp(n, t2.clone())))),
//             }
//         }
//         Conditions::Convertible(t1, t2) => {
//             let (Either::Left(t1), Either::Left(t2)) = (t1, t2) else {
//                 return Err(());
//             };
//             if beta_equiv(t1, t2) {
//                 Ok((State::Success, None))
//             } else {
//                 Ok((State::Fail, None))
//             }
//         }
//         Conditions::ReduceToSort(_, _) => todo!(),
//         Conditions::ReduceToProd(_, _) => todo!(),
//     }
// }

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
    ConvToSort,
    ConvToProd,
    ProdForm,
    ProdIntro,
    ProdElim,
}

impl Display for DerivationLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            DerivationLabel::EmptyContext => "Empty(cxt)",
            DerivationLabel::VariableContext => "Var(cxt)",
            DerivationLabel::Variable => "Var",
            DerivationLabel::Axiom => "Axm",
            DerivationLabel::Conv => "Cnv",
            DerivationLabel::ConvToSort => "Cnv(->Sort)",
            DerivationLabel::ConvToProd => "Cnv(->Prod)",
            DerivationLabel::ProdForm => "Prod(Form)",
            DerivationLabel::ProdIntro => "Prod(Intr)",
            DerivationLabel::ProdElim => "Prof(Elim)",
        };
        write!(f, "{}", s)
    }
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

fn indent_string(n: usize) -> String {
    (0..2 * n).map(|_| ' ').collect()
}

impl PartialDerivationTree {
    fn child_mut(&mut self) -> Option<&mut Vec<PartialDerivationTree>> {
        match self {
            PartialDerivationTree::LeafEnd(_) => None,
            PartialDerivationTree::Node {
                head: _,
                rel: _,
                child,
            } => Some(child),
        }
    }
    pub fn is_complete(&self) -> bool {
        todo!()
    }
    pub fn pretty_print(&self, indent: usize) -> String {
        match self {
            PartialDerivationTree::LeafEnd(leaf) => {
                let s = match leaf {
                    Leaf::Judge(judgement, _) => {
                        format!("{}\n", judgement)
                    }
                    Leaf::Cond(conditions, state) => {
                        format!("{} {}\n", conditions.pretty_print(), state)
                    }
                };
                format!("{}@{}", indent_string(indent), s)
            }
            PartialDerivationTree::Node { head, rel, child } => {
                let fst = format!("{}@{head} ... {rel} \n", indent_string(indent));
                child.iter().fold(fst, |rem, child| {
                    format!("{rem}{}", child.pretty_print(indent + 1))
                })
            }
        }
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

pub fn type_check(cxt: Context, term1: Exp, term2: Exp) -> PartialDerivationTree {
    let mut der_tree = PartialDerivationTree::Node {
        head: Judgement::TypeCheck(
            cxt.clone(),
            Either::Left(term1.clone()),
            Either::Left(term2.clone()),
        ),
        rel: DerivationLabel::Conv,
        child: vec![],
    };
    let child = der_tree.child_mut().unwrap();

    let (der_tree_of_term1, t) = type_infer(cxt.clone(), term1.clone());

    child.push(der_tree_of_term1);
    let Some(t) = t else {
        return der_tree;
    };

    let convertibility_tree = {
        let c = Conditions::Convertible(Either::Left(t.clone()), Either::Left(term2.clone()));
        let s = if beta_equiv(t.clone(), term2.clone()) {
            State::Success
        } else {
            State::Fail
        };
        PartialDerivationTree::LeafEnd(Leaf::Cond(c, s))
    };

    child.push(convertibility_tree);

    der_tree
}

// Γ |- t |> (s in S) かどうか
fn type_infered_to_sort(cxt: Context, term: Exp) -> (PartialDerivationTree, Option<Sort>) {
    let mut der_tree = PartialDerivationTree::Node {
        head: Judgement::TypeInfer(cxt.clone(), Either::Left(term.clone())),
        rel: DerivationLabel::ConvToSort,
        child: vec![],
    };
    let child = der_tree.child_mut().unwrap();

    let (der_tree_of_term, sort_of_term) = type_infer(cxt.clone(), term.clone());
    child.push(der_tree_of_term);
    let Some(sort_of_term) = sort_of_term else {
        return (der_tree, None);
    };

    let (reduce_to_sort_tree, maybe_sort) = {
        let mut s = sort_of_term.clone();
        while let Some(t) = weak_reduction(s.clone()) {
            s = t;
        }

        match s {
            Exp::Sort(s) => {
                let cond = Conditions::ReduceToSort(Either::Left(sort_of_term), Either::Left(s));
                let state = State::Success;
                (
                    PartialDerivationTree::LeafEnd(Leaf::Cond(cond, state)),
                    Some(s),
                )
            }
            _ => {
                let cond = Conditions::ReduceToSort(Either::Left(sort_of_term), Either::Right(0));
                let state = State::Fail;
                (
                    PartialDerivationTree::LeafEnd(Leaf::Cond(cond, state)),
                    None,
                )
            }
        }
    };
    child.push(reduce_to_sort_tree);
    (der_tree, maybe_sort)
}

fn type_infered_to_prod(
    cxt: Context,
    term: Exp,
) -> (PartialDerivationTree, Option<(Var, Exp, Exp)>) {
    let mut der_tree = PartialDerivationTree::Node {
        head: Judgement::TypeInfer(cxt.clone(), Either::Left(term.clone())),
        rel: DerivationLabel::ConvToProd,
        child: vec![],
    };
    let child = der_tree.child_mut().unwrap();

    let (der_tree_of_term, sort_of_term) = type_infer(cxt.clone(), term.clone());

    child.push(der_tree_of_term);
    let Some(sort_of_term) = sort_of_term else {
        return (der_tree, None);
    };

    let (reduce_to_prod, abstract_body) = {
        let mut s = sort_of_term.clone();
        while let Some(t) = weak_reduction(s.clone()) {
            s = t;
        }
        match s {
            Exp::Prod(x, a, b) => {
                let cond = Conditions::ReduceToProd(
                    Either::Left(sort_of_term),
                    Either::Left((x.clone(), *a.clone(), *b.clone())),
                );
                let state = State::Success;
                (
                    PartialDerivationTree::LeafEnd(Leaf::Cond(cond, state)),
                    Some((x, *a, *b)),
                )
            }
            _ => {
                let cond = Conditions::ReduceToProd(Either::Left(sort_of_term), Either::Right(0));
                let state = State::Fail;
                (
                    PartialDerivationTree::LeafEnd(Leaf::Cond(cond, state)),
                    None,
                )
            }
        }
    };
    child.push(reduce_to_prod);
    (der_tree, abstract_body)
}

pub fn type_infer(mut cxt: Context, term1: Exp) -> (PartialDerivationTree, Option<Exp>) {
    let head = Judgement::TypeInfer(cxt.clone(), Either::Left(term1.clone()));
    match term1 {
        Exp::Sort(sort) => {
            let mut der_tree = PartialDerivationTree::Node {
                head,
                rel: DerivationLabel::Axiom,
                child: vec![],
            };
            let child = der_tree.child_mut().unwrap();
            let res = match sort.type_of_sort() {
                Some(s) => {
                    let cond = Conditions::AxiomSort(sort, s);
                    let leaf = PartialDerivationTree::LeafEnd(Leaf::Cond(cond, State::Success));
                    child.push(leaf);
                    Some(Exp::Sort(s))
                }
                None => None,
            };
            (der_tree, res)
        }
        Exp::Var(x) => {
            let mut der_tree = PartialDerivationTree::Node {
                head,
                rel: DerivationLabel::Variable,
                child: vec![],
            };
            let child = der_tree.child_mut().unwrap();
            let res = match cxt.search_var_exp(&x) {
                Some(t) => {
                    let cond =
                        Conditions::ContextHasVar(cxt.clone(), x.clone(), Either::Left(t.clone()));
                    let leaf = PartialDerivationTree::LeafEnd(Leaf::Cond(cond, State::Success));
                    child.push(leaf);
                    Some(t.clone())
                }
                None => None,
            };
            (der_tree, res)
        }
        Exp::Prod(x, t, t2) => {
            let mut der_tree = PartialDerivationTree::Node {
                head,
                rel: DerivationLabel::ProdForm,
                child: vec![],
            };
            let child = der_tree.child_mut().unwrap();
            // sort of t
            let (der_tree_t, sort_of_t) = type_infered_to_sort(cxt.clone(), *t.clone());
            child.push(der_tree_t);
            let Some(sort_of_t) = sort_of_t else {
                return (der_tree, None);
            };

            // sort of t2
            cxt.push_decl((x, *t));
            let (der_tree_t2, sort_of_t2) = type_infered_to_sort(cxt, *t2.clone());
            child.push(der_tree_t2);
            let Some(sort_of_t2) = sort_of_t2 else {
                return (der_tree, None);
            };

            // (s1, s2, ?3) in R or not
            let Some(s3) = sort_of_t.relation_of_sort(sort_of_t2) else {
                return (der_tree, None);
            };

            let cond = Conditions::RelationSort(sort_of_t, sort_of_t2, s3);
            let leaf = PartialDerivationTree::LeafEnd(Leaf::Cond(cond, State::Success));

            child.push(leaf);

            (der_tree, Some(Exp::Sort(s3)))
        }
        Exp::Lam(x, t, m) => {
            let mut der_tree = PartialDerivationTree::Node {
                head,
                rel: DerivationLabel::ProdIntro,
                child: vec![],
            };
            let child = der_tree.child_mut().unwrap();

            let (der_tree_a, _sort) = type_infered_to_sort(cxt.clone(), *t.clone());
            child.push(der_tree_a);
            let Some(_sort) = _sort else {
                return (der_tree, None);
            };

            cxt.push_decl((x.clone(), *t.clone()));
            let (der_tree_m, type_m) = type_infer(cxt, *m.clone());
            child.push(der_tree_m);
            let Some(type_m) = type_m else {
                return (der_tree, None);
            };

            (der_tree, Some(Exp::Prod(x, t, Box::new(type_m))))
        }
        Exp::App(t1, t2) => {
            let mut der_tree = PartialDerivationTree::Node {
                head,
                rel: DerivationLabel::ProdElim,
                child: vec![],
            };
            let child = der_tree.child_mut().unwrap();

            let (der_tree_t1, xab) = type_infered_to_prod(cxt.clone(), *t1.clone());

            child.push(der_tree_t1);
            let Some((x, a, b)) = xab else {
                return (der_tree, None);
            };

            let der_tree_t2 = type_check(cxt.clone(), *t2.clone(), a);
            child.push(der_tree_t2);

            let res = subst(b, &x, &t2);

            (der_tree, Some(res))
        }
        _ => todo!("not implemented"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn subst_test() {}
}
