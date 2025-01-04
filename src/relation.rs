use std::{collections::HashMap, fmt::Display};

use either::Either;

use crate::ast::*;

use self::utils::decompose_to_app_exps;

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
                .map(|e| subst_rec(e, fresh, substs.clone()))
                .collect(),
        },
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
                // x1 |-> x2
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
            let Exp::IndTypeCst {
                ind_type_name: ind_type_name2,
                constructor_name,
            } = *eliminated_exp
            else {
                return None;
            };
            if ind_type_name != ind_type_name2 {
                return None;
            }

            let (projection, constructor) =
                gcxt.indtype_constructor(&ind_type_name, &constructor_name)?;

            let signature = gcxt
                .indtype_defs(&ind_type_name)?
                .arity()
                .signature()
                .clone();

            let argument = constructor.arg_end().clone();

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
            let t = constructor.recursor(ff_elim_q, cases[projection].clone());
            Some(utils::assoc_apply(t, argument))
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

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Context(Vec<(Var, Exp)>);

impl Display for Context {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: String = self
            .0
            .iter()
            .fold(String::new(), |s1, (v, t)| format!("{s1}, {v}: {t}"));
        write!(f, "({s})")
    }
}

impl Context {
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn poped(&self) -> Option<(Self, (Var, Exp))> {
        let mut s = self.clone();
        let d = s.0.pop()?;
        Some((s, d))
    }
    pub fn push_decl(&mut self, d: (Var, Exp)) {
        self.0.push(d);
    }
    pub fn search_var_exp(&self, var: &Var) -> Option<&Exp> {
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
            Judgement::TypeCheck(context, exp1, exp2) => format!("{context} |- {exp1}:  {exp2}",),
            Judgement::TypeInfer(context, exp, maybe) => {
                format!(
                    "{context} |- {exp}:? {}",
                    match maybe {
                        Some(e) => e.to_string(),
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
    ReduceToIndType(Exp, Option<(String, Vec<Exp>)>), // t ->^*beta I a1 ... an
    ReduceToCstr(Exp, Option<(String, String, Vec<Exp>)>), // t ->* C a1 ... al
    ReduceToReturnType(Exp, Option<(Vec<(Var, Exp)>, Sort)>),
    AxiomSort(Sort, Option<Sort>),          // (s1: s2) in A
    RelationSort(Sort, Sort, Option<Sort>), // (s1, s2, s3) in R
    IndRelSort(Sort, Sort, Option<()>),     // (s1, s2) in R_elim
    ProofNeeded(Context, Exp),              // provable? G |= P
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
    fn convertible(gcxt: &GlobalContext, term1: Exp, term2: Exp) -> (Self, Option<()>) {
        let s = if beta_equiv(gcxt, term1.clone(), term2.clone()) {
            Some(())
        } else {
            None
        };
        let c = Conditions::Convertible(term1.clone(), term2.clone(), s);
        (c, s)
    }
    fn reduce_to_sort(gcxt: &GlobalContext, term: Exp) -> (Self, Option<Sort>) {
        let type_term = normalize(gcxt, term.clone());
        let s = match type_term {
            Exp::Sort(s) => Some(s),
            _ => None,
        };
        (Conditions::ReduceToSort(term, s.clone()), s)
    }
    fn reduce_to_prod(gcxt: &GlobalContext, term: Exp) -> (Self, Option<(Var, Exp, Exp)>) {
        let type_term = normalize(gcxt, term.clone());
        let s = match type_term {
            Exp::Prod(x, a, b) => Some((x, *a, *b)),
            _ => None,
        };
        (Conditions::ReduceToProd(term, s.clone()), s)
    }
    fn reduce_to_indtype(gcxt: &GlobalContext, term: Exp) -> (Self, Option<(String, Vec<Exp>)>) {
        let type_term = normalize(gcxt, term.clone());
        let type_term_decompose = decompose_to_app_exps(type_term);
        let head = type_term_decompose[0].clone();
        let argument = type_term_decompose[1..].to_vec();
        let s = match head {
            Exp::IndTypeType { ind_type_name } => Some((ind_type_name, argument)),
            _ => None,
        };
        (Conditions::ReduceToIndType(term, s.clone()), s)
    }
    fn reduce_to_indcst(
        gcxt: &GlobalContext,
        term: Exp,
    ) -> (Self, Option<(String, String, Vec<Exp>)>) {
        let type_term = normalize(gcxt, term.clone());
        let type_term_decompose = decompose_to_app_exps(type_term);
        let head = type_term_decompose[0].clone();
        let argument = type_term_decompose[1..].to_vec();
        let s = match head {
            Exp::IndTypeCst {
                ind_type_name,
                constructor_name,
            } => Some((ind_type_name, constructor_name, argument)),
            _ => None,
        };
        (Conditions::ReduceToCstr(term, s.clone()), s)
    }
    // e ->* (x_1: A_1) -> ...-> (x_n: A_n) -> (_: type_name x_1 ... x_n) -> s' for some s'
    fn reduce_to_returntype(
        gcxt: &GlobalContext,
        term: Exp,
        type_name: String,
    ) -> (Self, Option<(Vec<(Var, Exp)>, Sort)>) {
        println!("reduce to return type {term}");
        let type_term = normalize(gcxt, term.clone());
        let mut v = vec![];
        let mut term2 = type_term.clone();
        let s = loop {
            println!("  {term2}");
            match term2 {
                Exp::Prod(x, a, b) => {
                    v.push((x, *a));
                    term2 = *b;
                }
                Exp::Sort(s) => {
                    break s;
                }
                _ => {
                    return (Conditions::ReduceToReturnType(term2, None), None);
                }
            }
        };
        let expected = {
            let Some(inddefs) = gcxt.indtype_defs(&type_name) else {
                return (Conditions::ReduceToReturnType(term, None), None);
            };
            let vars: Vec<Exp> = inddefs
                .arity()
                .signature()
                .iter()
                .map(|(x, _)| Exp::Var(x.clone()))
                .collect();
            let arg = utils::assoc_apply(
                Exp::IndTypeType {
                    ind_type_name: type_name.clone(),
                },
                vars,
            );
            let mut e = Exp::prod(Var::Unused, arg, Exp::Sort(s));
            for (x, a) in inddefs.arity().signature().iter().rev() {
                e = Exp::prod(x.clone(), a.clone(), e);
            }
            e
        };
        if alpha_eq(&expected, &type_term) {
            v.pop();
            (
                Conditions::ReduceToReturnType(term, Some((v.clone(), s))),
                Some((v, s)),
            )
        } else {
            eprintln!("{expected} {type_term}");
            (Conditions::ReduceToReturnType(term2, None), None)
        }
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
    fn indrel_sort(s1: Sort, s2: Sort) -> (Self, Option<()>) {
        match s1.ind_type_rel(s2) {
            Some(()) => (Conditions::IndRelSort(s1, s2, Some(())), Some(())),
            None => (Conditions::IndRelSort(s1, s2, None), None),
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
            Conditions::IndRelSort(_, _, a) => a.is_some(),
            Conditions::ReduceToIndType(_, a) => a.is_some(),
            Conditions::ReduceToCstr(_, a) => a.is_some(),
            Conditions::ReduceToReturnType(_, a) => a.is_some(),
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
            Conditions::ContextHasVar(context, var, maybe) => format!(
                "{var} in {context} -> {}",
                match maybe {
                    Some(e) => e.to_string(),
                    None => "!".to_string(),
                }
            ),
            Conditions::Convertible(e1, e2, res) => {
                format!(
                    "{e1} =~ {e2} .. {}",
                    match res {
                        Some(_) => "o",
                        None => "!",
                    }
                )
            }
            Conditions::ReduceToSort(e, s) => {
                format!(
                    "{e} ->*_sort {}",
                    match s {
                        Some(s) => format!("{s}"),
                        None => "!".to_string(),
                    }
                )
            }
            Conditions::ReduceToProd(e, abs) => {
                format!(
                    "{e} ->*_prod {}",
                    match abs {
                        Some((x, a, b)) => format!("({x}: {a}) -> {b}"),
                        None => "!".to_string(),
                    }
                )
            }
            Conditions::ReduceToIndType(e, arg) => {
                format!(
                    "{e} ->*_indtype {}",
                    match arg {
                        None => "!".to_string(),
                        Some((name, arg)) => format!(
                            "{name}({})",
                            arg.iter().fold(String::new(), |s, e| format!("{s} {e}"))
                        ),
                    }
                )
            }
            Conditions::ReduceToCstr(e, arg) => {
                format!(
                    "{e} ->*_indtype {}",
                    match arg {
                        None => "!".to_string(),
                        Some((name, cst, arg)) => format!(
                            "{name}::{cst}({})",
                            arg.iter().fold(String::new(), |s, e| format!("{s} {e}"))
                        ),
                    }
                )
            }
            Conditions::ReduceToReturnType(e, r) => {
                format!(
                    "{e} ->*_returntype {}",
                    match r {
                        None => format!("!"),
                        Some(e) => format!("{e:?}"),
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
            Conditions::IndRelSort(s1, s2, s3) => {
                format!(
                    "rel(ind) of sort {s1} {s2} -> {}",
                    if s3.is_some() { "o" } else { "x" }
                )
            }
            Conditions::ProofNeeded(cxt, exp) => {
                format!("Provable? {cxt} |- {exp}")
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
    ConvToInd,
    ConvToCst,
    ProdForm,
    ProdIntro,
    ProdElim,
    IndForm,
    IndIntro,
    IndElim,
    GlobalDefinition,
    GlobalAssumption,
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
            DerivationLabel::ConvToInd => "Cnv(->Ind)",
            DerivationLabel::ConvToCst => "Cnv(->Cst)",
            DerivationLabel::ProdForm => "Prod(Form)",
            DerivationLabel::ProdIntro => "Prod(Intr)",
            DerivationLabel::ProdElim => "Prof(Elim)",
            DerivationLabel::IndForm => "Ind(Form)",
            DerivationLabel::IndIntro => "Ind(Intr)",
            DerivationLabel::IndElim => "Ind(Elim)",
            DerivationLabel::GlobalDefinition => "GlobalDef",
            DerivationLabel::GlobalAssumption => "GlobalAssum",
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

impl StatePartialTree {
    pub fn is_success(&self) -> bool {
        *self == StatePartialTree::Wait(vec![])
    }
    pub fn is_fail(&self) -> bool {
        *self == StatePartialTree::Fail
    }
    pub fn is_wait(&self) -> Option<&Vec<(Context, Exp)>> {
        match self {
            StatePartialTree::Fail => None,
            StatePartialTree::Wait(vec) => Some(vec),
        }
    }
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
                if let Judgement::TypeInfer(_, _, None) = head {
                    return StatePartialTree::Fail;
                }
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

pub fn type_check(
    gcxt: &GlobalContext,
    cxt: Context,
    term1: Exp,
    term2: Exp,
) -> PartialDerivationTree {
    let mut der_tree = PartialDerivationTree::Node {
        head: Judgement::TypeCheck(cxt.clone(), term1.clone(), term2.clone()),
        rel: DerivationLabel::Conv,
        child: vec![],
    };
    let child = der_tree.child_mut().unwrap();

    let (der_tree_of_term1, t) = type_infer(gcxt, cxt.clone(), term1.clone());

    child.push(der_tree_of_term1);
    let Some(t) = t else {
        return der_tree;
    };

    let convertibility_tree =
        { PartialDerivationTree::LeafEnd(Conditions::convertible(gcxt, term2, t).0) };

    child.push(convertibility_tree);

    der_tree
}

// Γ |- t |> (s in S) かどうか
pub fn type_infered_to_sort(
    gcxt: &GlobalContext,
    cxt: Context,
    term: Exp,
) -> (PartialDerivationTree, Option<Sort>) {
    let mut der_tree = PartialDerivationTree::Node {
        head: Judgement::TypeInfer(cxt.clone(), term.clone(), None),
        rel: DerivationLabel::ConvToSort,
        child: vec![],
    };

    let child = der_tree.child_mut().unwrap();

    let (der_tree_of_term, sort_of_term) = type_infer(gcxt, cxt.clone(), term.clone());
    child.push(der_tree_of_term);
    let Some(sort_of_term) = sort_of_term else {
        return (der_tree, None);
    };

    let (reduce_to_sort_tree, sort) = {
        let (cond, sort) = Conditions::reduce_to_sort(gcxt, sort_of_term);
        (PartialDerivationTree::LeafEnd(cond), sort)
    };

    child.push(reduce_to_sort_tree);

    *der_tree.of_type_mut().unwrap() = sort.map(|s| Exp::Sort(s));

    (der_tree, sort)
}

// Γ |- t |> (x: a) -> b
pub fn type_infered_to_prod(
    gcxt: &GlobalContext,
    cxt: Context,
    term: Exp,
) -> (PartialDerivationTree, Option<(Var, Exp, Exp)>) {
    let mut der_tree = PartialDerivationTree::Node {
        head: Judgement::TypeInfer(cxt.clone(), term.clone(), None),
        rel: DerivationLabel::ConvToProd,
        child: vec![],
    };
    let child = der_tree.child_mut().unwrap();

    let (der_tree_of_term, sort_of_term) = type_infer(gcxt, cxt.clone(), term.clone());

    child.push(der_tree_of_term);
    let Some(sort_of_term) = sort_of_term else {
        return (der_tree, None);
    };

    let (reduce_to_prod, abstract_body) = {
        let (c, abs) = Conditions::reduce_to_prod(gcxt, sort_of_term);
        (PartialDerivationTree::LeafEnd(c), abs)
    };
    child.push(reduce_to_prod);

    *der_tree.of_type_mut().unwrap() = abstract_body.clone().map(|(x, a, b)| Exp::prod(x, a, b));

    (der_tree, abstract_body)
}

// Γ |- t |> I a1 ... an
pub fn type_infered_to_ind(
    gcxt: &GlobalContext,
    cxt: Context,
    term: Exp,
) -> (PartialDerivationTree, Option<(String, Vec<Exp>)>) {
    let mut der_tree = PartialDerivationTree::Node {
        head: Judgement::TypeInfer(cxt.clone(), term.clone(), None),
        rel: DerivationLabel::ConvToInd,
        child: vec![],
    };

    let child = der_tree.child_mut().unwrap();

    let (der_tree_of_term, type_term) = type_infer(gcxt, cxt.clone(), term.clone());
    child.push(der_tree_of_term);
    let Some(type_term) = type_term else {
        return (der_tree, None);
    };

    let (reduce_to_ind, body) = {
        let (c, body) = Conditions::reduce_to_indtype(gcxt, type_term);
        (PartialDerivationTree::LeafEnd(c), body)
    };
    child.push(reduce_to_ind);

    *der_tree.of_type_mut().unwrap() = body.clone().map(|body| {
        utils::assoc_apply(
            Exp::IndTypeType {
                ind_type_name: body.0,
            },
            body.1,
        )
    });

    (der_tree, body)
}

// exists s' s.t.  |- t |> (x_1: A_1) -> ... (x_k: A_k) -> (_: I x_1 ... x_k) -> s'
// where (x_1: A_1) -> ... -> (x_k A_k) = arity of I
pub fn type_infered_to_ind_return_type(
    gcxt: &GlobalContext,
    mut cxt: Context,
    term: Exp,
    type_name: String,
) -> (PartialDerivationTree, Option<Sort>) {
    let mut der_tree = PartialDerivationTree::Node {
        head: Judgement::TypeInfer(cxt.clone(), term.clone(), None),
        rel: DerivationLabel::Conv,
        child: vec![],
    };

    let child = der_tree.child_mut().unwrap();

    let (der_tree_of_term, type_term) = type_infer(gcxt, cxt.clone(), term.clone());
    child.push(der_tree_of_term);
    let Some(type_term) = type_term else {
        return (der_tree, None);
    };

    let (der_tree_of_type_term, type_of_term) = {
        let (c, body) =
            Conditions::reduce_to_returntype(gcxt, type_term.clone(), type_name.clone());
        (PartialDerivationTree::LeafEnd(c), body)
    };
    child.push(der_tree_of_type_term);

    // let inddef = gcxt.indtype_defs(&type_name).unwrap();

    let Some(type_of_term) = type_of_term else {
        return (der_tree, None);
    };

    println!("hello");

    let end_sort = type_of_term.1;

    (der_tree, Some(end_sort))
}

pub fn type_infer(
    gcxt: &GlobalContext,
    mut cxt: Context,
    term1: Exp,
) -> (PartialDerivationTree, Option<Exp>) {
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
            // definition is in global context
            if let Some((a, _)) = gcxt.search_var_defined(x.clone()) {
                let mut der_tree = PartialDerivationTree::Node {
                    head,
                    rel: DerivationLabel::GlobalDefinition,
                    child: vec![],
                };
                *der_tree.of_type_mut().unwrap() = Some(a.clone());
                return (der_tree, Some(a.clone()));
            }

            // assumption is in global context
            if let Some(a) = gcxt.search_var_assum(x.clone()) {
                let mut der_tree = PartialDerivationTree::Node {
                    head,
                    rel: DerivationLabel::GlobalDefinition,
                    child: vec![],
                };
                *der_tree.of_type_mut().unwrap() = Some(a.clone());
                return (der_tree, Some(a.clone()));
            }

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
            let (der_tree_t, sort_of_t) = type_infered_to_sort(gcxt, cxt.clone(), *t.clone());
            child.push(der_tree_t);
            let Some(sort_of_t) = sort_of_t else {
                return (der_tree, None);
            };

            // sort of t2
            cxt.push_decl((x, *t));
            let (der_tree_t2, sort_of_t2) = type_infered_to_sort(gcxt, cxt, *t2.clone());
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

            let (der_tree_a, _sort) = type_infered_to_sort(gcxt, cxt.clone(), *t.clone());
            child.push(der_tree_a);
            let Some(_sort) = _sort else {
                return (der_tree, None);
            };

            cxt.push_decl((x.clone(), *t.clone()));
            let (der_tree_m, type_m) = type_infer(gcxt, cxt, *m.clone());
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

            let (der_tree_t1, xab) = type_infered_to_prod(gcxt, cxt.clone(), *t1.clone());

            child.push(der_tree_t1);
            let Some((x, a, b)) = xab else {
                return (der_tree, None);
            };

            let der_tree_t2 = type_check(gcxt, cxt.clone(), *t2.clone(), a);
            child.push(der_tree_t2);

            let res = Some(subst(b, &x, &t2));
            der_tree.of_type_mut().unwrap().clone_from(&res);

            (der_tree, res)
        }
        Exp::IndTypeType { ind_type_name } => {
            let type_of_indtype = gcxt.type_of_indtype(&ind_type_name);
            let mut der_tree = PartialDerivationTree::Node {
                head,
                rel: DerivationLabel::IndForm,
                child: vec![],
            };
            *der_tree.of_type_mut().unwrap() = type_of_indtype.clone();
            (der_tree, type_of_indtype)
        }
        Exp::IndTypeCst {
            ind_type_name,
            constructor_name,
        } => {
            let type_of_constructor = gcxt.type_of_cst(&ind_type_name, &constructor_name).unwrap();
            let mut der_tree = PartialDerivationTree::Node {
                head,
                rel: DerivationLabel::IndIntro,
                child: vec![],
            };
            *der_tree.of_type_mut().unwrap() = Some(type_of_constructor.clone());
            (der_tree, Some(type_of_constructor))
        }
        Exp::IndTypeElim {
            ind_type_name,
            eliminated_exp,
            return_type,
            cases,
        } => {
            let mut der_tree = PartialDerivationTree::Node {
                head,
                rel: DerivationLabel::IndElim,
                child: vec![],
            };
            let child = der_tree.child_mut().unwrap();

            // |- return_type |> nice form
            let (return_type_der, sort_of_return_type) = type_infered_to_ind_return_type(
                gcxt,
                cxt.clone(),
                *return_type.clone(),
                ind_type_name.clone(),
            );

            child.push(return_type_der);
            let Some(sort_of_return_type) = sort_of_return_type else {
                return (der_tree, None);
            };

            // (sort of indtype, sort of return type) in rel
            let ind_defs = gcxt.indtype_defs(&ind_type_name).unwrap();
            let sort_indtype = *ind_defs.arity().sort();
            let (cond, a) = {
                let (cond, a) = Conditions::indrel_sort(sort_indtype, sort_of_return_type);
                (PartialDerivationTree::LeafEnd(cond), a)
            };
            child.push(cond);
            if a.is_none() {
                return (der_tree, None);
            }

            // |- eliminated_exp: I a1 ... an
            let (elim_der_tree, res) =
                type_infered_to_ind(gcxt, cxt.clone(), *eliminated_exp.clone());
            child.push(elim_der_tree);
            let Some(res) = res else {
                return (der_tree, None);
            };

            if res.0 != ind_type_name {
                return (der_tree, None);
            }

            let args_of_term_ind = res.1.clone();

            // |- I a1 ... an : sort_indtype
            let ind_well_dertree = type_check(
                gcxt,
                cxt.clone(),
                utils::assoc_apply(
                    Exp::IndTypeType {
                        ind_type_name: ind_type_name.clone(),
                    },
                    args_of_term_ind.clone(),
                ),
                Exp::Sort(sort_indtype),
            );
            let b = ind_well_dertree.result_of_tree() == StatePartialTree::Fail;
            child.push(ind_well_dertree);
            if b {
                return (der_tree, None);
            }

            // f[i]: eliminator_type
            for (i, c) in ind_defs.constructors().iter().enumerate() {
                let cname = gcxt.name_of_cst(&ind_type_name, i).unwrap();
                let expected = c.eliminator_type(
                    *return_type.clone(),
                    Exp::IndTypeCst {
                        ind_type_name: ind_type_name.clone(),
                        constructor_name: cname.clone(),
                    },
                );
                let expected = subst(
                    expected,
                    c.variable(),
                    &Exp::IndTypeType {
                        ind_type_name: ind_type_name.clone(),
                    },
                );
                let der_tree_fi = type_check(gcxt, cxt.clone(), cases[i].clone(), expected);
                let b = der_tree_fi.result_of_tree() == StatePartialTree::Fail;
                child.push(der_tree_fi);
                if b {
                    return (der_tree, None);
                }
            }

            println!("here ok");

            let type_of_term = Exp::App(
                Box::new(utils::assoc_apply(*return_type, args_of_term_ind)),
                Box::new(*eliminated_exp),
            );

            *der_tree.of_type_mut().unwrap() = Some(type_of_term.clone());

            (der_tree, Some(type_of_term))
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
