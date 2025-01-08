use crate::{ast::*, lambda_calculus::*};
use either::Either;
use std::{collections::HashMap, fmt::Display};

use self::utils::decompose_to_app_exps;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GlobalContext {
    definitions: Vec<(Var, Exp, Exp)>,                   // x := v
    parameters: Vec<(Var, Exp)>,                         // x: t
    inductive_definitions: Vec<inductives::IndTypeDefs>, // inductive defs
}

impl GlobalContext {
    // pub fn push_newind(&mut self, defs: inductives::IndTypeDefs) -> Result<(), String> {
    //     use crate::relation::{type_check, type_infered_to_sort, Context, StatePartialTree};
    //     if self
    //         .inductive_definitions
    //         .iter()
    //         .find(|inddefs| inddefs.name() == defs.name())
    //         .is_some()
    //     {
    //         return Err(format!("already defined {}", defs.name()));
    //     }

    //     // arity の well defined
    //     let arity_exp: Exp = defs.arity().clone().into();
    //     let check = type_infered_to_sort(self, Context::default(), arity_exp);
    //     if check.1.is_none() {
    //         let arity: Exp = defs.arity().clone().into();
    //         return Err(format!(
    //             "arity {} is not well formed \n{}",
    //             arity,
    //             check.0.pretty_print(0),
    //         ));
    //     }

    //     // 各 constructor の well defined
    //     for (_, c) in defs.constructors() {
    //         let sort = *defs.arity().sort();
    //         let mut cxt = Context::default();
    //         let (x, a) = (defs.variable().clone(), defs.arity().clone().into());
    //         cxt.push_decl((x, a));
    //         let constructor: Exp = c.clone().into();
    //         let check = type_check(self, cxt, constructor, Exp::Sort(sort));
    //         if check.result_of_tree() == StatePartialTree::Fail {
    //             let c: Exp = c.clone().into();
    //             return Err(format!(
    //                 "constructor {} is not well formed \n{}",
    //                 c,
    //                 check.pretty_print(0),
    //             ));
    //         }
    //     }

    //     self.inductive_definitions.push(defs);
    //     Ok(())
    // }
    pub fn type_of_indtype(&self, ind_type_name: &TypeName) -> Option<Exp> {
        let indtype_def = self.indtype_defs(ind_type_name)?;
        let arity = indtype_def.arity().clone();
        Some(arity.into())
    }
    pub fn type_of_cst(
        &self,
        ind_type_name: &TypeName,
        constructor_name: &ConstructorName,
    ) -> Option<Exp> {
        let defs = self.indtype_defs(ind_type_name)?;
        let constructor_def = defs.constructor(constructor_name)?;
        let constructor_exp: Exp = constructor_def.clone().into();
        let constructor_exp = subst(
            constructor_exp,
            constructor_def.variable(),
            &Exp::IndTypeType {
                ind_type_name: ind_type_name.clone(),
            },
        );
        Some(constructor_exp)
    }
    pub fn ind_type_return_type(&self, ind_type_name: &TypeName, sort: Sort) -> Option<Exp> {
        let indtype_def = self.indtype_defs(ind_type_name)?;
        let arity = indtype_def.arity().clone();
        let vars = arity
            .signature()
            .iter()
            .map(|(x, _)| Exp::Var(x.clone()))
            .collect();
        let end = Exp::prod(
            Var::Unused,
            utils::assoc_apply(
                Exp::IndTypeType {
                    ind_type_name: ind_type_name.clone(),
                },
                vars,
            ),
            Exp::Sort(sort),
        );
        Some(utils::assoc_prod(arity.signature().clone(), end))
    }
    pub fn type_of_eliminator(&self, ind_type_name: &TypeName, sort: Sort) -> Option<Exp> {
        let indtype_def = self.indtype_defs(ind_type_name)?;
        let arity = indtype_def.arity().clone();
        // (x1: A1) -> ... -> (xn: An) -> (_: I x1 ... xn) -> s
        let return_type: Exp = {
            let vars = arity
                .signature()
                .iter()
                .map(|(x, _)| Exp::Var(x.clone()))
                .collect();
            let end = Exp::lambda(
                Var::Unused,
                utils::assoc_apply(
                    Exp::IndTypeType {
                        ind_type_name: ind_type_name.clone(),
                    },
                    vars,
                ),
                Exp::Sort(sort),
            );
            utils::assoc_prod(arity.signature().clone(), end)
        };
        let q_exp = Exp::Var("Q".into());
        // (fi: xi(I, Q, I::i, C_i)) -> ... ->
        let type_cases: Vec<(Var, Exp)> = {
            let mut v = vec![];
            for (cname, c) in indtype_def.constructors() {
                // xi_X(Q, c, C[i])
                let pre = c.eliminator_type(
                    q_exp.clone(),
                    Exp::IndTypeCst {
                        ind_type_name: ind_type_name.clone(),
                        constructor_name: cname.clone(),
                    },
                );
                let exact = subst(
                    pre,
                    indtype_def.variable(),
                    &Exp::IndTypeType {
                        ind_type_name: ind_type_name.clone(),
                    },
                );
                v.push((cname.to_string().into(), exact));
            }
            v
        };
        // (x1: A1) -> ... -> (xn: An) -> (x: I x1... xn) -> Q x1 ... xn x
        let end: Exp = {
            let vars: Vec<Exp> = arity
                .signature()
                .iter()
                .map(|(x, _)| Exp::Var(x.clone()))
                .collect();
            let new_x: Var = "x".into();
            let end = Exp::lambda(
                new_x.clone(),
                utils::assoc_apply(
                    Exp::IndTypeType {
                        ind_type_name: ind_type_name.clone(),
                    },
                    vars.clone(),
                ),
                utils::assoc_apply(
                    utils::assoc_apply(q_exp.clone(), vars),
                    vec![Exp::Var(new_x)],
                ),
            );
            utils::assoc_prod(arity.signature().clone(), end)
        };
        Some(Exp::prod(
            "Q".into(),
            return_type,
            utils::assoc_prod(type_cases, end),
        ))
    }
    pub fn search_var_defined(&self, y: Var) -> Option<(&Exp, &Exp)> {
        self.definitions
            .iter()
            .find_map(|(x, a, e)| if *x == y { Some((a, e)) } else { None })
    }
    pub fn search_var_assum(&self, y: Var) -> Option<&Exp> {
        self.parameters
            .iter()
            .find_map(|(x, a)| if *x == y { Some(a) } else { None })
    }
    // pub fn push_new_defs(
    //     &mut self,
    //     (x, a, v): (Var, Exp, Exp),
    // ) -> (PartialDerivationTree, Result<(), String>) {
    //     let der_tree = type_check(self, Context::default(), v.clone(), a.clone());
    //     if der_tree.result_of_tree().is_success() {
    //         self.definitions.push((x, a, v));
    //         (der_tree, Ok(()))
    //     } else if der_tree.result_of_tree().is_fail() {
    //         (der_tree, Err("fail".to_string()))
    //     } else {
    //         todo!()
    //     }
    // }
    // pub fn push_new_assum(
    //     &mut self,
    //     (x, a): (Var, Exp),
    // ) -> (PartialDerivationTree, Result<(), String>) {
    //     let (der_tree, _) = type_infered_to_sort(self, Context::default(), a.clone());
    //     if der_tree.result_of_tree().is_success() {
    //         self.parameters.push((x, a));
    //         (der_tree, Ok(()))
    //     } else if der_tree.result_of_tree().is_fail() {
    //         (der_tree, Err("fail".to_string()))
    //     } else {
    //         todo!()
    //     }
    // }
    pub fn indtype_defs(&self, type_name: &TypeName) -> Option<&inductives::IndTypeDefs> {
        self.inductive_definitions
            .iter()
            .find(|defs| defs.name() == type_name)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LocalContext(Vec<(Var, Exp)>);

impl Display for LocalContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: String = self
            .0
            .iter()
            .fold(String::new(), |s1, (v, t)| format!("{s1}, {v}: {t}"));
        write!(f, "({s})")
    }
}

impl LocalContext {
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
    pub fn search_var_exp(&self, var: &Var) -> Option<&(Var, Exp)> {
        self.0.iter().find(|(v, e)| v == var)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvableJudgement {
    context: LocalContext,
    proposition: Exp,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeCheckJudgement {
    context: LocalContext,
    term: Exp,
    type_of_term: Exp,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Judgement {
    Proof(ProvableJudgement),
    Type(TypeCheckJudgement),
}

impl Display for Judgement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Judgement::Type(TypeCheckJudgement {
                context,
                term,
                type_of_term,
            }) => format!("{context} |- {term}:  {type_of_term}",),
            Judgement::Proof(ProvableJudgement {
                context,
                proposition,
            }) => {
                format!("{context} |= {proposition}")
            }
        };
        write!(f, "{}", s)
    }
}

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub enum Judgement {
//     TypeCheck(LocalContext, Exp, Exp),
//     TypeInfer(LocalContext, Exp, Option<Exp>),
// }

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub enum Condition {
//     ContextHasVar(LocalContext, Var, Option<Exp>), // x in G -> T where (x: T) in G
//     Convertible(Exp, Exp, Option<()>),             // t1 =^beta t2
//     ReduceToSort(Exp, Option<Sort>),               // t ->^beta* sort
//     ReduceToProd(Exp, Option<(Var, Exp, Exp)>),    // t ->^beta* (x: a) -> b
//     ReduceToIndType(Exp, Option<(String, Vec<Exp>)>), // t ->^*beta I a1 ... an
//     ReduceToCstr(Exp, Option<(String, String, Vec<Exp>)>), // t ->* C a1 ... al
//     ReduceToReturnType(Exp, Option<(Vec<(Var, Exp)>, Sort)>),
//     AxiomSort(Sort, Option<Sort>),          // (s1: s2) in A
//     RelationSort(Sort, Sort, Option<Sort>), // (s1, s2, s3) in R
//     IndRelSort(Sort, Sort, Option<()>),     // (s1, s2) in R_elim
//     ProofNeeded(LocalContext, Exp),         // provable? G |= P
// }

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Condition {
    VariableinContext(LocalContext, (Var, Exp)),
    Convertible(Exp, Exp),
    SortAxiom(Sort, Sort),
    SortRelation(Sort, Sort, Sort),
    SortInductive(Sort, Sort),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ErrOnCondition {
    err: String,
}

impl<S> From<S> for ErrOnCondition
where
    S: AsRef<str>,
{
    fn from(value: S) -> Self {
        ErrOnCondition {
            err: value.as_ref().to_string(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExtraInfo {
    ErrOnCondition(ErrOnCondition),
    ErrNotInfered(DerivationFailed),
    GeneratedBy(String),
}

impl Condition {
    fn context_has_var(cxt: LocalContext, var: Var) -> Result<(Self, Exp), ErrOnCondition> {
        // (Self, Option<Exp>) {
        match cxt.search_var_exp(&var) {
            Some(e) => {
                let e = e.clone();
                let cond = Condition::VariableinContext(cxt, e.clone());
                Ok((cond, e.1))
            }
            None => Err(format!("{cxt} has no var {var}").into()),
        }
    }
    fn convertible(gcxt: &GlobalContext, term1: Exp, term2: Exp) -> Result<Self, ErrOnCondition> {
        if beta_equiv(gcxt, term1.clone(), term2.clone()) {
            Ok(Condition::Convertible(term1, term2))
        } else {
            Err(format!("{term1} !=~ {term2}").into())
        }
    }
    fn reduce_to_sort(gcxt: &GlobalContext, term: Exp) -> Result<(Self, Sort), ErrOnCondition> {
        let term2 = normalize(gcxt, term.clone());
        match term2 {
            Exp::Sort(s) => Ok((Condition::Convertible(term, Exp::Sort(s)), s)),
            _ => Err(format!("{term} !->* sort").into()),
        }
    }
    fn reduce_to_prod(
        gcxt: &GlobalContext,
        term: Exp,
    ) -> Result<(Self, (Var, Exp, Exp)), ErrOnCondition> {
        let term2 = normalize(gcxt, term.clone());
        match term2 {
            Exp::Prod(x, a, b) => {
                let (x, a, b) = (x, *a.clone(), *b.clone());
                Ok((
                    Condition::Convertible(term, Exp::prod(x.clone(), a.clone(), b.clone())),
                    (x, a, b),
                ))
            }
            other => Err(format!("{term} !->* prod but ->* {other}").into()),
        }
    }
    fn reduce_to_indtype(
        gcxt: &GlobalContext,
        term: Exp,
    ) -> Result<(Self, (TypeName, Vec<Exp>)), ErrOnCondition> {
        let term2 = normalize(gcxt, term.clone());
        let (head, argument) = decompose_to_app_exps(term2.clone());
        match head {
            Exp::IndTypeType { ind_type_name } => {
                let cond = Condition::Convertible(term, term2.clone());
                Ok((cond, (ind_type_name, argument)))
            }
            other => Err(format!("{term} !->* Ind a1 ... an but ->* {other}").into()),
        }
    }
    // e ->* (x_1: A_1) -> ...-> (x_n: A_n) -> (_: type_name x_1 ... x_n) -> s' for some s'
    fn reduce_to_returntype(
        gcxt: &GlobalContext,
        term: Exp,
        type_name: TypeName,
    ) -> Result<(Self, (Vec<(Var, Exp)>, Sort)), ErrOnCondition> {
        let term2 = normalize(gcxt, term.clone());
        let (mut args, expected_to_sort) = utils::decompose_to_prod_exps(term2.clone());
        let sort_end = match expected_to_sort {
            Exp::Sort(s) => s,
            _ => {
                return Err(format!("end of exp {term2} is not sort").into());
            }
        };

        let expected = gcxt.ind_type_return_type(&type_name, sort_end);
        let Some(expected) = expected else {
            return Err(format!("inductive type {type_name} is not found").into());
        };

        println!("comp:{expected} & {term2}");
        if alpha_eq(&expected, &term2) {
            println!("ok !!");
            args.pop();
            let cond = Condition::Convertible(term, term2);
            Ok((cond, (args, sort_end)))
        } else {
            Err(format!("{term2} is not form of {expected}").into())
        }
    }
    fn axiom_sort(s: Sort) -> Result<(Self, Sort), ErrOnCondition> {
        match s.type_of_sort() {
            Some(s2) => Ok((Condition::SortAxiom(s, s2), s2)),
            None => Err(format!("sort {s} has not type").into()),
        }
    }
    fn relation_sort(s1: Sort, s2: Sort) -> Result<(Self, Sort), ErrOnCondition> {
        match s1.relation_of_sort(s2) {
            Some(s3) => Ok((Condition::SortRelation(s1, s2, s3), s3)),
            None => Err(format!("({s1}, {s2}) is not in rel").into()),
        }
    }
    fn indrel_sort(s1: Sort, s2: Sort) -> Result<Self, ErrOnCondition> {
        match s1.ind_type_rel(s2) {
            Some(()) => Ok(Condition::SortInductive(s1, s2)),
            None => Err(format!("({s1}, {s2}) not in indrel").into()),
        }
    }
    fn pretty_print(&self) -> String {
        match self {
            Condition::VariableinContext(context, (var, exp)) => {
                format!("({var}: {exp} in {context}",)
            }
            Condition::Convertible(e1, e2) => {
                format!("{e1} =~ {e2}",)
            }
            Condition::SortAxiom(sort, sort1) => {
                format!("{sort}: {sort1}")
            }
            Condition::SortRelation(sort, sort1, sort2) => {
                format!("({sort}, {sort1}, {sort2}) in rel")
            }
            Condition::SortInductive(s1, s2) => {
                format!("({s1}, {s2}) in rel",)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DerivationLabel {
    Variable,
    Axiom,
    Conv,
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
            DerivationLabel::Variable => "Var",
            DerivationLabel::Axiom => "Axm",
            DerivationLabel::Conv => "Cnv",
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

type DerChild = Either<PartialDerivationTree, Condition>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartialDerivationTreeTypeCheck {
    head: TypeCheckJudgement,
    rel: DerivationLabel,
    child: Vec<DerChild>,
    extra: Vec<ExtraInfo>,
}

impl PartialDerivationTreeTypeCheck {
    fn of_type(&self) -> &Exp {
        &self.head.type_of_term
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartialDerivationTreeProof {
    head: ProvableJudgement,
    rel: DerivationLabel,
    child: Vec<DerChild>,
    extra: Vec<ExtraInfo>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PartialDerivationTree {
    TypeCheck(PartialDerivationTreeTypeCheck),
    Proof(PartialDerivationTreeProof),
}

impl PartialDerivationTree {
    fn state(&self) -> Option<Vec<ProvableJudgement>> {
        todo!()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DerivationFailed {
    context: LocalContext,
    term: Exp,
    label: DerivationLabel,
    child: Vec<DerChild>,
}

// fn indent_string(n: usize) -> String {
//     (0..2 * n).map(|_| ' ').collect()
// }

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StatePartialTree {
    Fail,
    Wait(Vec<(LocalContext, Exp)>),
}

impl StatePartialTree {
    pub fn is_success(&self) -> bool {
        *self == StatePartialTree::Wait(vec![])
    }
    pub fn is_fail(&self) -> bool {
        *self == StatePartialTree::Fail
    }
    pub fn is_wait(&self) -> Option<&Vec<(LocalContext, Exp)>> {
        match self {
            StatePartialTree::Fail => None,
            StatePartialTree::Wait(vec) => Some(vec),
        }
    }
}

impl PartialDerivationTree {
    // pub fn pretty_print(&self, indent: usize) -> String {
    //     match self {
    //         PartialDerivationTree::LeafEnd(conditions) => {
    //             let s = format!("{} \n", conditions.pretty_print());
    //             format!("{}@{}", indent_string(indent), s)
    //         }
    //         PartialDerivationTree::Node { head, rel, child } => {
    //             let fst = format!("{}@{head} ... {rel} \n", indent_string(indent));
    //             child.iter().fold(fst, |rem, child| {
    //                 format!("{rem}{}", child.pretty_print(indent + 1))
    //             })
    //         }
    //     }
    // }
}

pub fn type_check(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    term1: Exp,
    term2: Exp,
) -> (PartialDerivationTreeTypeCheck, Option<()>) {
    let head = TypeCheckJudgement {
        context: cxt.clone(),
        term: term1.clone(),
        type_of_term: term2.clone(),
    };

    let der_tree_infered = match type_infer(gcxt, cxt.clone(), term1.clone()) {
        Either::Left(der_tree_check) => der_tree_check,
        Either::Right(derivation_failed) => {
            let extra = ExtraInfo::ErrNotInfered(derivation_failed);
            return (
                PartialDerivationTreeTypeCheck {
                    head,
                    rel: DerivationLabel::Conv,
                    child: vec![],
                    extra: vec![extra],
                },
                None,
            );
        }
    };

    let infered_type = der_tree_infered.of_type().clone();

    let mut child = vec![Either::Left(PartialDerivationTree::TypeCheck(
        der_tree_infered,
    ))];
    let mut extra = vec![ExtraInfo::GeneratedBy("type check".to_string())];

    match Condition::convertible(gcxt, infered_type, term2) {
        Ok(cond) => {
            child.push(Either::Right(cond));
            (
                PartialDerivationTreeTypeCheck {
                    head,
                    rel: DerivationLabel::Conv,
                    child,
                    extra,
                },
                Some(()),
            )
        }
        Err(err) => {
            extra.push(ExtraInfo::ErrOnCondition(err));
            (
                PartialDerivationTreeTypeCheck {
                    head,
                    rel: DerivationLabel::Conv,
                    child,
                    extra,
                },
                None,
            )
        }
    }
}

// Γ |- t |> (s in S) かどうか
pub fn type_infered_to_sort(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    term: Exp,
) -> (PartialDerivationTree, Option<Sort>) {
    // let mut der_tree = PartialDerivationTree {
    //     head: Judgement::TypeInfer(cxt.clone(), term.clone(), None),
    //     rel: DerivationLabel::ConvToSort,
    //     child: vec![],
    // };

    // let child = der_tree.child_mut().unwrap();

    // let (der_tree_of_term, sort_of_term) = type_infer(gcxt, cxt.clone(), term.clone());
    // child.push(der_tree_of_term);
    // let Some(sort_of_term) = sort_of_term else {
    //     return (der_tree, None);
    // };

    // let (reduce_to_sort_tree, sort) = {
    //     let (cond, sort) = Condition::reduce_to_sort(gcxt, sort_of_term);
    //     (PartialDerivationTree::LeafEnd(cond), sort)
    // };

    // child.push(reduce_to_sort_tree);

    // *der_tree.of_type_mut().unwrap() = sort.map(|s| Exp::Sort(s));

    // (der_tree, sort)
}

// Γ |- t |> (x: a) -> b
pub fn type_infered_to_prod(
    gcxt: &GlobalContext,
    cxt: LocalContext,
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
        let (c, abs) = Condition::reduce_to_prod(gcxt, sort_of_term);
        (PartialDerivationTree::LeafEnd(c), abs)
    };
    child.push(reduce_to_prod);

    *der_tree.of_type_mut().unwrap() = abstract_body.clone().map(|(x, a, b)| Exp::prod(x, a, b));

    (der_tree, abstract_body)
}

// Γ |- t |> I a1 ... an
pub fn type_infered_to_ind(
    gcxt: &GlobalContext,
    cxt: LocalContext,
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
        let (c, body) = Condition::reduce_to_indtype(gcxt, type_term);
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
    mut cxt: LocalContext,
    term: Exp,
    type_name: String,
) -> (PartialDerivationTree, Option<Sort>) {
    let mut der_tree = PartialDerivationTree::Node {
        head: Judgement::TypeInfer(cxt.clone(), term.clone(), None),
        rel: DerivationLabel::ConvToRet,
        child: vec![],
    };

    let child = der_tree.child_mut().unwrap();

    let (der_tree_of_term, type_term) = type_infer(gcxt, cxt.clone(), term.clone());
    child.push(der_tree_of_term);
    let Some(type_term) = type_term else {
        return (der_tree, None);
    };

    let (der_tree_of_type_term, type_of_term) = {
        let (c, body) = Condition::reduce_to_returntype(gcxt, type_term, type_name.clone());
        (PartialDerivationTree::LeafEnd(c), body)
    };
    child.push(der_tree_of_type_term);
    let Some(type_of_term) = type_of_term else {
        return (der_tree, None);
    };

    let end_sort = type_of_term.1;

    der_tree
        .of_type_mut()
        .unwrap()
        .clone_from(&Some(Exp::Sort(end_sort)));

    (der_tree, Some(end_sort))
}

pub fn type_infer(
    gcxt: &GlobalContext,
    mut cxt: LocalContext,
    term1: Exp,
) -> Either<PartialDerivationTreeTypeCheck, DerivationFailed> {
    let head = Judgement::TypeInfer(cxt.clone(), term1.clone(), None);
    match term1 {
        Exp::Sort(sort) => {
            let mut der_tree = PartialDerivationTree::Node {
                head,
                rel: DerivationLabel::Axiom,
                child: vec![],
            };
            let (cond, s) = Condition::axiom_sort(sort);
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
            let (cond, type_of_x) = Condition::context_has_var(cxt.clone(), x.clone());
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

            let (cond, rel_res) = Condition::relation_sort(sort_of_t, sort_of_t2);
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
                let (cond, a) = Condition::indrel_sort(sort_indtype, sort_of_return_type);
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
            for (cname, c) in ind_defs.constructors() {
                let corresponding_case = cases
                    .iter()
                    .find_map(|(c, e)| if c == cname { Some(e.clone()) } else { None })
                    .unwrap();
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
                let der_tree_fi = type_check(gcxt, cxt.clone(), corresponding_case, expected);
                let b = der_tree_fi.result_of_tree() == StatePartialTree::Fail;
                child.push(der_tree_fi);
                if b {
                    return (der_tree, None);
                }
            }

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
