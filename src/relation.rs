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
            format!("{s1}({v}: {})", t.pretty_print())
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
pub enum Judgement {
    // WellFormedContext(Context),
    TypeCheck(Context, Exp, Exp),
    TypeInfer(Context, Exp, Option<Exp>),
}

impl Display for Judgement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Judgement::TypeCheck(context, either, either1) => format!(
                "{} |- {}:  {}",
                context.pretty_print(),
                either.pretty_print(),
                either1.pretty_print()
            ),
            Judgement::TypeInfer(context, either, maybe) => {
                format!(
                    "{} |- {}:? {}",
                    context.pretty_print(),
                    either.pretty_print(),
                    match maybe {
                        Some(e) => e.pretty_print(),
                        None => "".to_string(),
                    }
                )
            }
        };
        write!(f, "{}", s)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Conditions {
    ContextHasVar(Context, Var, Option<Exp>), // x in G -> T where (x: T) in G
    Convertible(Exp, Exp, Option<()>),        // t1 =^beta t2
    ReduceToSort(Exp, Option<Sort>),          // t ->^beta* sort
    ReduceToProd(Exp, Option<(Var, Exp, Exp)>), // t ->^beta* (x: a) -> b
    AxiomSort(Sort, Option<Sort>),            // (s1: s2) in A
    RelationSort(Sort, Sort, Option<Sort>),   // (s1, s2, s3) in A
    ProofNeeded(Context, Exp),                // provable? G |= P
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ConditionsState {
    Success,
    Fail,
    Wait(Context, Exp),
}

impl Conditions {
    fn context_has_var(cxt: Context, var: Var) -> (Self, Option<Exp>) {
        match cxt.search_var_exp(&var) {
            Some(e) => {
                let e = e.clone();
                (
                    Conditions::ContextHasVar(cxt, var, Some(e.clone())),
                    Some(e.clone()),
                )
            }
            None => (Conditions::ContextHasVar(cxt, var, None), None),
        }
    }
    fn convertible(term1: Exp, term2: Exp) -> (Self, Option<()>) {
        let s = if beta_equiv(term1.clone(), term2.clone()) {
            Some(())
        } else {
            None
        };
        let c = Conditions::Convertible(term1.clone(), term2.clone(), s);
        (c, s)
    }
    fn reduce_to_sort(term: Exp) -> (Self, Option<Sort>) {
        let term_sort = normalize(term.clone());
        let s = match term_sort {
            Exp::Sort(s) => Some(s),
            _ => None,
        };
        (Conditions::ReduceToSort(term, s.clone()), s)
    }
    fn reduce_to_prod(term: Exp) -> (Self, Option<(Var, Exp, Exp)>) {
        let term_sort = normalize(term.clone());
        let s = match term_sort {
            Exp::Prod(x, a, b) => Some((x, *a, *b)),
            _ => None,
        };
        (Conditions::ReduceToProd(term, s.clone()), s)
    }
    fn axiom_sort(s: Sort) -> (Self, Option<Sort>) {
        match s.type_of_sort() {
            Some(s2) => (Conditions::AxiomSort(s, Some(s2)), Some(s2)),
            None => (Conditions::AxiomSort(s, None), None),
        }
    }
    fn relation_sort(s1: Sort, s2: Sort) -> (Self, Option<Sort>) {
        match s1.relation_of_sort(s2) {
            Some(s3) => (Conditions::RelationSort(s1, s2, Some(s3)), Some(s3)),
            None => (Conditions::RelationSort(s1, s2, None), None),
        }
    }
    fn is_success(&self) -> ConditionsState {
        let opt = match self {
            Conditions::ContextHasVar(_, _, exp) => exp.is_some(),
            Conditions::Convertible(_, _, a) => a.is_some(),
            Conditions::ReduceToSort(_, sort) => sort.is_some(),
            Conditions::ReduceToProd(_, a) => a.is_some(),
            Conditions::AxiomSort(_, sort) => sort.is_some(),
            Conditions::RelationSort(_, _, sort2) => sort2.is_some(),
            Conditions::ProofNeeded(cxt, exp) => {
                return ConditionsState::Wait(cxt.clone(), exp.clone());
            }
        };
        if opt {
            ConditionsState::Success
        } else {
            ConditionsState::Fail
        }
    }
    fn pretty_print(&self) -> String {
        match self {
            Conditions::ContextHasVar(context, var, either) => format!(
                "{var} in {} -> {}",
                context.pretty_print(),
                match either {
                    Some(e) => e.pretty_print(),
                    None => "!".to_string(),
                }
            ),
            Conditions::Convertible(either, either1, res) => {
                format!(
                    "{} =~ {} .. {}",
                    either.pretty_print(),
                    either1.pretty_print(),
                    match res {
                        Some(_) => "ok",
                        None => "!",
                    }
                )
            }
            Conditions::ReduceToSort(either, either1) => {
                format!(
                    "{} ->*_sort {}",
                    either.pretty_print(),
                    match either1 {
                        Some(s) => format!("{s}"),
                        None => "!".to_string(),
                    }
                )
            }
            Conditions::ReduceToProd(either, either1) => {
                format!(
                    "{} ->*_prod {}",
                    either.pretty_print(),
                    match either1 {
                        Some((x, a, b)) =>
                            format!("({x}: {}) -> {}", a.pretty_print(), b.pretty_print()),
                        None => "!".to_string(),
                    }
                )
            }
            Conditions::AxiomSort(sort, sort1) => {
                format!(
                    "type of {sort} -> {}",
                    match sort1 {
                        Some(s) => format!("{s}"),
                        None => "!".to_string(),
                    }
                )
            }
            Conditions::RelationSort(sort, sort1, sort2) => {
                format!(
                    "rel of ({sort}, {sort1}) -> {}",
                    match sort2 {
                        Some(s) => format!("{s}"),
                        None => "!".to_string(),
                    }
                )
            }
            Conditions::ProofNeeded(cxt, exp) => {
                format!("Provable? {} |- {}", cxt.pretty_print(), exp.pretty_print())
            }
        }
    }
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PartialDerivationTree {
    LeafEnd(Conditions),
    Node {
        head: Judgement,
        rel: DerivationLabel,
        child: Vec<PartialDerivationTree>,
    },
}

fn indent_string(n: usize) -> String {
    (0..2 * n).map(|_| ' ').collect()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StatePartialTree {
    Fail,
    Wait(Vec<(Context, Exp)>),
}

impl PartialDerivationTree {
    pub fn result_of_tree(&self) -> StatePartialTree {
        match self {
            PartialDerivationTree::LeafEnd(conditions) => match conditions.is_success() {
                ConditionsState::Fail => StatePartialTree::Fail,
                ConditionsState::Success => StatePartialTree::Wait(vec![]),
                ConditionsState::Wait(cxt, a) => StatePartialTree::Wait(vec![(cxt, a)]),
            },
            PartialDerivationTree::Node { head, rel, child } => {
                let mut v = vec![];
                for child in child {
                    let res = child.result_of_tree();
                    let StatePartialTree::Wait(res) = res else {
                        return StatePartialTree::Fail;
                    };
                    v.extend(res);
                }
                StatePartialTree::Wait(v)
            }
        }
    }
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
    fn of_type_mut(&mut self) -> Option<&mut Option<Exp>> {
        match self {
            PartialDerivationTree::LeafEnd(conditions) => None,
            PartialDerivationTree::Node { head, rel, child } => match head {
                Judgement::TypeCheck(context, exp, exp1) => None,
                Judgement::TypeInfer(context, exp, exp1) => Some(exp1),
            },
        }
    }
    pub fn pretty_print(&self, indent: usize) -> String {
        match self {
            PartialDerivationTree::LeafEnd(conditions) => {
                let s = format!("{} \n", conditions.pretty_print());
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

pub fn type_check(cxt: Context, term1: Exp, term2: Exp) -> PartialDerivationTree {
    let mut der_tree = PartialDerivationTree::Node {
        head: Judgement::TypeCheck(cxt.clone(), term1.clone(), term2.clone()),
        rel: DerivationLabel::Conv,
        child: vec![],
    };
    let child = der_tree.child_mut().unwrap();

    let (der_tree_of_term1, t) = type_infer(cxt.clone(), term1.clone());

    child.push(der_tree_of_term1);
    let Some(t) = t else {
        return der_tree;
    };

    let convertibility_tree =
        { PartialDerivationTree::LeafEnd(Conditions::convertible(term2, t).0) };

    child.push(convertibility_tree);

    der_tree
}

// Γ |- t |> (s in S) かどうか
fn type_infered_to_sort(cxt: Context, term: Exp) -> (PartialDerivationTree, Option<Sort>) {
    let mut der_tree = PartialDerivationTree::Node {
        head: Judgement::TypeInfer(cxt.clone(), term.clone(), None),
        rel: DerivationLabel::ConvToSort,
        child: vec![],
    };

    let child = der_tree.child_mut().unwrap();

    let (der_tree_of_term, sort_of_term) = type_infer(cxt.clone(), term.clone());
    child.push(der_tree_of_term);
    let Some(sort_of_term) = sort_of_term else {
        return (der_tree, None);
    };

    let (reduce_to_sort_tree, sort) = {
        let (cond, sort) = Conditions::reduce_to_sort(sort_of_term);
        (PartialDerivationTree::LeafEnd(cond), sort)
    };

    child.push(reduce_to_sort_tree);

    *der_tree.of_type_mut().unwrap() = sort.map(|s| Exp::Sort(s));

    (der_tree, sort)
}

fn type_infered_to_prod(
    cxt: Context,
    term: Exp,
) -> (PartialDerivationTree, Option<(Var, Exp, Exp)>) {
    let mut der_tree = PartialDerivationTree::Node {
        head: Judgement::TypeInfer(cxt.clone(), term.clone(), None),
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
        let (c, abs) = Conditions::reduce_to_prod(sort_of_term);
        (PartialDerivationTree::LeafEnd(c), abs)
    };
    child.push(reduce_to_prod);

    *der_tree.of_type_mut().unwrap() = abstract_body.clone().map(|(x, a, b)| Exp::prod(x, a, b));

    (der_tree, abstract_body)
}

pub fn type_infer(mut cxt: Context, term1: Exp) -> (PartialDerivationTree, Option<Exp>) {
    let head = Judgement::TypeInfer(cxt.clone(), term1.clone(), None);
    match term1 {
        Exp::Sort(sort) => {
            let mut der_tree = PartialDerivationTree::Node {
                head,
                rel: DerivationLabel::Axiom,
                child: vec![],
            };
            let (cond, s) = Conditions::axiom_sort(sort);
            let child = der_tree.child_mut().unwrap();
            child.push(PartialDerivationTree::LeafEnd(cond));
            let s = s.map(|s| Exp::Sort(s));
            *der_tree.of_type_mut().unwrap() = s.clone();
            (der_tree, s)
        }
        Exp::Var(x) => {
            let mut der_tree = PartialDerivationTree::Node {
                head,
                rel: DerivationLabel::Variable,
                child: vec![],
            };
            let (cond, type_of_x) = Conditions::context_has_var(cxt.clone(), x.clone());
            let child = der_tree.child_mut().unwrap();
            child.push(PartialDerivationTree::LeafEnd(cond));
            *der_tree.of_type_mut().unwrap() = type_of_x.clone();
            (der_tree, type_of_x)
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

            let (cond, rel_res) = Conditions::relation_sort(sort_of_t, sort_of_t2);
            child.push(PartialDerivationTree::LeafEnd(cond));

            let s3 = rel_res.map(|s3| Exp::Sort(s3));

            *der_tree.of_type_mut().unwrap() = s3.clone();

            (der_tree, s3)
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

            let res = Some(Exp::Prod(x, t, Box::new(type_m)));

            der_tree.of_type_mut().unwrap().clone_from(&res);

            (der_tree, res)
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
