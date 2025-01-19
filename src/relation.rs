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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResIndDefs {
    pub single: bool,
    pub arity_well_formed: Option<Result<PartialDerivationTreeTypeCheck, DerivationFailed>>,
    pub constructor_well_formed:
        Option<Vec<Result<PartialDerivationTreeTypeCheck, DerivationFailed>>>,
}

impl GlobalContext {
    pub fn push_new_ind(&mut self, defs: inductives::IndTypeDefs) -> ResIndDefs {
        if self
            .inductive_definitions
            .iter()
            .any(|inddefs| inddefs.name() == defs.name())
        {
            return ResIndDefs {
                single: false,
                arity_well_formed: None,
                constructor_well_formed: None,
            };
        }

        // arity の well defined
        let arity_exp: Exp = defs.arity().clone().into();
        let arity_well_formed = match type_infered_to_sort(self, LocalContext::default(), arity_exp)
        {
            Ok((der_tree, sort)) => Ok(der_tree),
            Err(err) => {
                return ResIndDefs {
                    single: true,
                    arity_well_formed: Some(Err(err)),
                    constructor_well_formed: None,
                }
            }
        };

        let mut constructor_well_formed = vec![];
        let mut flag = true;

        // 各 constructor の well defined
        for (_, c) in defs.constructors() {
            let sort = *defs.arity().sort();
            let mut cxt = LocalContext::default();
            let (x, a) = (defs.variable().clone(), defs.arity().clone().into());
            cxt.push_decl((x, a));
            let constructor: Exp = c.clone().into();
            match type_check(self, cxt, constructor, Exp::Sort(sort)) {
                Ok(der_tree) => {
                    constructor_well_formed.push(Ok(der_tree));
                }
                Err(err) => {
                    flag = false;
                    constructor_well_formed.push(Err(err));
                }
            };
        }

        if flag {
            self.inductive_definitions.push(defs);
        }

        ResIndDefs {
            single: true,
            arity_well_formed: Some(arity_well_formed),
            constructor_well_formed: Some(constructor_well_formed),
        }
    }

    pub fn push_new_defs(
        &mut self,
        (x, a, v): (Var, Exp, Exp),
    ) -> Result<PartialDerivationTreeTypeCheck, DerivationFailed> {
        match type_check(self, LocalContext::default(), v.clone(), a.clone()) {
            Ok(der_tree) => {
                self.definitions.push((x, a, v));
                Ok(der_tree)
            }
            Err(err) => Err(err),
        }
    }
    pub fn push_new_assum(
        &mut self,
        (x, a): (Var, Exp),
    ) -> Result<(PartialDerivationTreeTypeCheck, Sort), DerivationFailed> {
        match type_infered_to_sort(self, LocalContext::default(), a.clone()) {
            Ok((der_tree, sort)) => {
                self.parameters.push((x, a));
                Ok((der_tree, sort))
            }
            Err(err) => Err(err),
        }
    }
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
        let inddefs = self.indtype_defs(ind_type_name)?;
        Some(inddefs.return_type(sort))
    }
    pub fn induction_principal(&self, ind_type_name: &TypeName, sort: Sort) -> Option<Exp> {
        let inddefs = self.indtype_defs(ind_type_name)?;
        Some(inddefs.induction_scheme(sort))
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
    pub context: LocalContext,
    pub proposition: Exp,
}

impl Display for ProvableJudgement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ProvableJudgement {
            context,
            proposition,
        } = self;
        write!(f, "{}", format!("{context} |= {proposition}"))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeCheckJudgement {
    pub context: LocalContext,
    pub term: Exp,
    pub type_of_term: Exp,
}

impl Display for TypeCheckJudgement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let TypeCheckJudgement {
            context,
            term,
            type_of_term,
        } = self;
        write!(f, "{}", format!("{context} |- {term}:  {type_of_term}"))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Judgement {
    Proof(ProvableJudgement),
    Type(TypeCheckJudgement),
}

impl Display for Judgement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Judgement::Type(judgement) => format!("{judgement}"),
                Judgement::Proof(judgement) => format!("{judgement}"),
            }
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Condition {
    VariableinContext(LocalContext, (Var, Exp)),
    Convertible(Exp, Exp),
    SortAxiom(Sort, Sort),
    SortRelation(Sort, Sort, Sort),
    SortInductive(Sort, Sort),
}

impl Display for Condition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
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
        };
        write!(f, "{}", str)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ErrOnCondition {
    pub err: String,
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
    fn reduce_to_pow(gcxt: &GlobalContext, term: Exp) -> Result<(Self, Exp), ErrOnCondition> {
        let term2 = normalize(gcxt, term.clone());
        match term2 {
            Exp::Pow(a) => {
                let a = *a.clone();
                Ok((
                    Condition::Convertible(term, Exp::Pow(Box::new(a.clone()))),
                    a,
                ))
            }
            other => Err(format!("{term} !->* pow but ->* {other}").into()),
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

        if alpha_eq(&expected, &term2) {
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DerivationLabel {
    Variable,
    Axiom,
    Conv,
    ProdForm,
    ProdIntro,
    ProdElim,
    Proof,
    PowerSetForm,
    PowerSetWeak,
    SubsetForm,
    SubsetIntro,
    SubsetElimSet,
    SubsetElimProp,
    PredForm,
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
            DerivationLabel::Proof => "Proof",
            DerivationLabel::PowerSetForm => "Pow(Form)",
            DerivationLabel::PowerSetWeak => "Pow(Weak)",
            DerivationLabel::SubsetForm => "Sub(Form)",
            DerivationLabel::SubsetIntro => "Sub(Intro)",
            DerivationLabel::SubsetElimSet => "Sub(ElimSet)",
            DerivationLabel::SubsetElimProp => "Sub(ElimProp)",
            DerivationLabel::PredForm => "Pred(Form)",
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
pub enum ExtraInfo {
    GeneratedBy(String),
    OtherInfo(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ErrInfo {
    ErrOnCondition(ErrOnCondition),
    ErrOnTree(Box<DerivationFailed>),
}

type DerChild = Either<PartialDerivationTree, Condition>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartialDerivationTreeTypeCheck {
    pub head: TypeCheckJudgement,
    pub label: DerivationLabel,
    pub child: Vec<DerChild>,
    pub extra: Vec<ExtraInfo>,
}

impl PartialDerivationTreeTypeCheck {
    fn of_type(&self) -> &Exp {
        &self.head.type_of_term
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartialDerivationTreeProof {
    pub head: ProvableJudgement,
    pub label: DerivationLabel,
    pub child: Vec<DerChild>,
    pub extra: Vec<ExtraInfo>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PartialDerivationTree {
    TypeCheck(PartialDerivationTreeTypeCheck),
    Proof(PartialDerivationTreeProof),
    Unproved(ProvableJudgement),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FailHead {
    InferFail(LocalContext, Exp),
    CheckFail(TypeCheckJudgement),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DerivationFailed {
    head: FailHead,
    label: DerivationLabel,
    child: Vec<DerChild>,
    err: ErrInfo,
    extra: Vec<ExtraInfo>,
}

pub fn type_check(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    term1: Exp,
    term2: Exp,
) -> Result<PartialDerivationTreeTypeCheck, DerivationFailed> {
    let head = TypeCheckJudgement {
        context: cxt.clone(),
        term: term1.clone(),
        type_of_term: term2.clone(),
    };

    let mut child = vec![];
    let mut extra = vec![ExtraInfo::GeneratedBy("type check".to_string())];

    let der_tree_infered = match type_infer(gcxt, cxt.clone(), term1.clone()) {
        Ok(der_tree_check) => der_tree_check,
        Err(derivation_failed) => {
            return Err(DerivationFailed {
                head: FailHead::CheckFail(head),
                label: DerivationLabel::Conv,
                child,
                extra,
                err: ErrInfo::ErrOnTree(Box::new(derivation_failed)),
            });
        }
    };

    let infered_type = der_tree_infered.of_type().clone();

    child.push(Either::Left(PartialDerivationTree::TypeCheck(
        der_tree_infered,
    )));

    match Condition::convertible(gcxt, infered_type.clone(), term2.clone()) {
        Ok(cond) => {
            child.push(Either::Right(cond));
            Ok(PartialDerivationTreeTypeCheck {
                head,
                label: DerivationLabel::Conv,
                child,
                extra,
            })
        }
        Err(err) => {
            extra.push(ExtraInfo::GeneratedBy(format!("not conv Err({err:?})")));
            let (der_tree_inf, sort_of_infered_type) =
                type_infered_to_sort(gcxt, cxt.clone(), infered_type).unwrap();
            let (der_tree_sort_t2, sort_of_term2) =
                type_infered_to_sort(gcxt, cxt.clone(), term2.clone()).unwrap();
            if sort_of_infered_type == sort_of_term2 && sort_of_term2 == Sort::Set {
                todo!()
            } else {
                Err(DerivationFailed {
                    head: FailHead::CheckFail(head),
                    label: DerivationLabel::Conv,
                    child,
                    extra,
                    err: ErrInfo::ErrOnCondition(err),
                })
            }
        }
    }
}

// Γ |- t |> (s in S) かどうか
pub fn type_infered_to_sort(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    term: Exp,
) -> Result<(PartialDerivationTreeTypeCheck, Sort), DerivationFailed> {
    let mut child = vec![];
    let mut extra = vec![ExtraInfo::GeneratedBy("type infered to sort".to_string())];

    let der_tree_infered = match type_infer(gcxt, cxt.clone(), term.clone()) {
        Ok(der_tree_check) => der_tree_check,
        Err(derivation_failed) => {
            return Err(DerivationFailed {
                head: FailHead::InferFail(cxt, term),
                label: DerivationLabel::Conv,
                child,
                extra,
                err: ErrInfo::ErrOnTree(Box::new(derivation_failed)),
            });
        }
    };

    let infered_term = der_tree_infered.head.type_of_term.clone();

    child.push(Either::Left(PartialDerivationTree::TypeCheck(
        der_tree_infered,
    )));

    match Condition::reduce_to_sort(gcxt, infered_term.clone()) {
        Ok((cond, sort)) => {
            child.push(Either::Right(cond));
            Ok((
                PartialDerivationTreeTypeCheck {
                    head: TypeCheckJudgement {
                        context: cxt,
                        term,
                        type_of_term: Exp::Sort(sort),
                    },
                    label: DerivationLabel::Conv,
                    child,
                    extra,
                },
                sort,
            ))
        }
        Err(err) => {
            extra.push(ExtraInfo::GeneratedBy(format!(
                "!->* sort Err({err:?}) so check pow"
            )));
            match Condition::reduce_to_pow(gcxt, infered_term) {
                Ok((cond, a)) => {
                    child.push(Either::Right(cond));
                    let der_tree_up = PartialDerivationTreeTypeCheck {
                        head: TypeCheckJudgement {
                            context: cxt.clone(),
                            term: term.clone(),
                            type_of_term: Exp::Pow(Box::new(a.clone())),
                        },
                        label: DerivationLabel::Conv,
                        child,
                        extra: vec![],
                    };
                    Ok((
                        PartialDerivationTreeTypeCheck {
                            head: TypeCheckJudgement {
                                context: cxt,
                                term,
                                type_of_term: Exp::Sort(Sort::Set),
                            },
                            label: DerivationLabel::PowerSetForm,
                            child: vec![Either::Left(PartialDerivationTree::TypeCheck(
                                der_tree_up,
                            ))],
                            extra,
                        },
                        Sort::Set,
                    ))
                }
                Err(err) => Err(DerivationFailed {
                    head: FailHead::InferFail(cxt, term),
                    label: DerivationLabel::Conv,
                    child,
                    extra,
                    err: ErrInfo::ErrOnCondition(err),
                }),
            }
        }
    }
}

// Γ |- t |> (x: a) -> b
pub fn type_infered_to_prod(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    term: Exp,
) -> Result<(PartialDerivationTreeTypeCheck, (Var, Exp, Exp)), DerivationFailed> {
    let mut child = vec![];
    let extra = vec![ExtraInfo::GeneratedBy("type infered to prod".to_string())];

    let der_tree_infered = match type_infer(gcxt, cxt.clone(), term.clone()) {
        Ok(der_tree_check) => der_tree_check,
        Err(derivation_failed) => {
            return Err(DerivationFailed {
                head: FailHead::InferFail(cxt, term),

                label: DerivationLabel::Conv,
                child,
                extra,
                err: ErrInfo::ErrOnTree(Box::new(derivation_failed)),
            });
        }
    };

    let infered_term = der_tree_infered.head.type_of_term.clone();

    child.push(Either::Left(PartialDerivationTree::TypeCheck(
        der_tree_infered,
    )));

    match Condition::reduce_to_prod(gcxt, infered_term) {
        Ok((cond, (x, a, b))) => {
            child.push(Either::Right(cond));
            Ok((
                PartialDerivationTreeTypeCheck {
                    head: TypeCheckJudgement {
                        context: cxt,
                        term,
                        type_of_term: Exp::prod(x.clone(), a.clone(), b.clone()),
                    },
                    label: DerivationLabel::Conv,
                    child,
                    extra,
                },
                (x, a, b),
            ))
        }
        Err(err) => Err(DerivationFailed {
            head: FailHead::InferFail(cxt, term),
            label: DerivationLabel::Conv,
            child,
            extra,
            err: ErrInfo::ErrOnCondition(err),
        }),
    }
}

// Γ |- t |> I a1 ... an
pub fn type_infered_to_ind(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    term: Exp,
) -> Result<(PartialDerivationTreeTypeCheck, (TypeName, Vec<Exp>)), DerivationFailed> {
    let mut child = vec![];
    let mut extra = vec![ExtraInfo::GeneratedBy("type infered to sort".to_string())];

    let der_tree_infered = match type_infer(gcxt, cxt.clone(), term.clone()) {
        Ok(der_tree_check) => der_tree_check,
        Err(derivation_failed) => {
            return Err(DerivationFailed {
                head: FailHead::InferFail(cxt, term),
                label: DerivationLabel::Conv,
                child,
                extra,
                err: ErrInfo::ErrOnTree(Box::new(derivation_failed)),
            });
        }
    };

    let infered_term = der_tree_infered.head.type_of_term.clone();

    child.push(Either::Left(PartialDerivationTree::TypeCheck(
        der_tree_infered,
    )));

    match Condition::reduce_to_indtype(gcxt, infered_term) {
        Ok((cond, (type_name, args))) => {
            child.push(Either::Right(cond));
            Ok((
                PartialDerivationTreeTypeCheck {
                    head: TypeCheckJudgement {
                        context: cxt,
                        term,
                        type_of_term: utils::assoc_apply(
                            Exp::IndTypeType {
                                ind_type_name: type_name.clone(),
                            },
                            args.clone(),
                        ),
                    },
                    label: DerivationLabel::Conv,
                    child,
                    extra,
                },
                (type_name, args),
            ))
        }
        Err(err) => Err(DerivationFailed {
            head: FailHead::InferFail(cxt, term),
            label: DerivationLabel::Conv,
            child,
            extra,
            err: ErrInfo::ErrOnCondition(err),
        }),
    }
}

// exists s' s.t.  |- t |> (x_1: A_1) -> ... (x_k: A_k) -> (_: I x_1 ... x_k) -> s'
// where (x_1: A_1) -> ... -> (x_k A_k) = arity of I
pub fn type_infered_to_ind_return_type(
    gcxt: &GlobalContext,
    mut cxt: LocalContext,
    term: Exp,
    type_name: TypeName,
) -> Result<(PartialDerivationTreeTypeCheck, Sort), DerivationFailed> {
    let mut child = vec![];
    let mut extra = vec![ExtraInfo::GeneratedBy(format!(
        "type infered to {type_name} return type"
    ))];

    let der_tree_infered = match type_infer(gcxt, cxt.clone(), term.clone()) {
        Ok(der_tree_check) => der_tree_check,
        Err(derivation_failed) => {
            return Err(DerivationFailed {
                head: FailHead::InferFail(cxt, term),
                label: DerivationLabel::Conv,
                child,
                extra,
                err: ErrInfo::ErrOnTree(Box::new(derivation_failed)),
            });
        }
    };

    let infered_term = der_tree_infered.head.type_of_term.clone();

    child.push(Either::Left(PartialDerivationTree::TypeCheck(
        der_tree_infered,
    )));

    match Condition::reduce_to_returntype(gcxt, infered_term, type_name) {
        Ok((cond, (_params, sort))) => {
            child.push(Either::Right(cond));
            Ok((
                PartialDerivationTreeTypeCheck {
                    head: TypeCheckJudgement {
                        context: cxt,
                        term,
                        type_of_term: Exp::Sort(sort),
                    },
                    label: DerivationLabel::Conv,
                    child,
                    extra,
                },
                sort,
            ))
        }
        Err(err) => Err(DerivationFailed {
            head: FailHead::InferFail(cxt, term),
            label: DerivationLabel::Conv,
            child,
            extra,
            err: ErrInfo::ErrOnCondition(err),
        }),
    }
}

pub fn type_infer(
    gcxt: &GlobalContext,
    mut cxt: LocalContext,
    term1: Exp,
) -> Result<PartialDerivationTreeTypeCheck, DerivationFailed> {
    let make_head = {
        let cxt = cxt.clone();
        let term1 = term1.clone();
        |type_of_term| TypeCheckJudgement {
            context: cxt,
            term: term1,
            type_of_term,
        }
    };

    let fail_head = FailHead::InferFail(cxt.clone(), term1.clone());
    let mut child = vec![];
    let mut extra = vec![];

    match term1 {
        Exp::Sort(sort) => {
            let label = DerivationLabel::Axiom;
            extra.push(ExtraInfo::GeneratedBy("infer sort".into()));

            match Condition::axiom_sort(sort) {
                Ok((cond, sort)) => {
                    child.push(Either::Right(cond));
                    let head = make_head(Exp::Sort(sort));
                    Ok(PartialDerivationTreeTypeCheck {
                        head,
                        label,
                        child,
                        extra,
                    })
                }
                Err(err) => Err(DerivationFailed {
                    head: fail_head,
                    label: DerivationLabel::Conv,
                    child,
                    extra,
                    err: ErrInfo::ErrOnCondition(err),
                }),
            }
        }
        Exp::Var(x) => {
            extra.push(ExtraInfo::GeneratedBy("infer var".into()));

            // global definition
            if let Some(e) = gcxt.search_var_defined(x.clone()) {
                return Ok(PartialDerivationTreeTypeCheck {
                    head: make_head(e.0.clone()),
                    label: DerivationLabel::GlobalDefinition,
                    child,
                    extra,
                });
            }

            // global assumption
            if let Some(e) = gcxt.search_var_assum(x.clone()) {
                return Ok(PartialDerivationTreeTypeCheck {
                    head: make_head(e.clone()),
                    label: DerivationLabel::GlobalAssumption,
                    child,
                    extra,
                });
            }

            match Condition::context_has_var(cxt, x.clone()) {
                Ok((cond, e)) => Ok(PartialDerivationTreeTypeCheck {
                    head: make_head(e),
                    label: DerivationLabel::Variable,
                    child,
                    extra,
                }),
                Err(err) => Err(DerivationFailed {
                    head: fail_head,
                    label: DerivationLabel::Variable,
                    child,
                    extra,
                    err: ErrInfo::ErrOnCondition(err),
                }),
            }
        }
        Exp::Prod(x, t, t2) => {
            let label = DerivationLabel::ProdForm;
            extra.push(ExtraInfo::GeneratedBy("ProdForm".into()));

            // sort of t
            let sort_of_t = match type_infered_to_sort(gcxt, cxt.clone(), *t.clone()) {
                Ok((der_tree, sort)) => {
                    child.push(Either::Left(PartialDerivationTree::TypeCheck(der_tree)));
                    sort
                }
                Err(err) => {
                    return Err(DerivationFailed {
                        head: fail_head,
                        label,
                        child,
                        extra,
                        err: ErrInfo::ErrOnTree(Box::new(err)),
                    });
                }
            };

            cxt.push_decl((x, *t));

            let sort_of_t2 = match type_infered_to_sort(gcxt, cxt, *t2.clone()) {
                Ok((der_tree, sort)) => {
                    child.push(Either::Left(PartialDerivationTree::TypeCheck(der_tree)));
                    sort
                }
                Err(err) => {
                    return Err(DerivationFailed {
                        head: fail_head,
                        label,
                        child,
                        extra,
                        err: ErrInfo::ErrOnTree(Box::new(err)),
                    });
                }
            };

            match Condition::relation_sort(sort_of_t, sort_of_t2) {
                Ok((cond, s3)) => {
                    child.push(Either::Right(cond));
                    Ok(PartialDerivationTreeTypeCheck {
                        head: make_head(Exp::Sort(s3)),
                        label,
                        child,
                        extra,
                    })
                }
                Err(err) => Err(DerivationFailed {
                    head: fail_head,
                    label,
                    child,
                    extra,
                    err: ErrInfo::ErrOnCondition(err),
                }),
            }
        }
        Exp::Lam(x, t, m) => {
            extra.push(ExtraInfo::GeneratedBy("ProdIntro".into()));

            let label = DerivationLabel::ProdIntro;

            // sort of t
            let _sort = match type_infered_to_sort(gcxt, cxt.clone(), *t.clone()) {
                Ok((der_tree, sort)) => {
                    child.push(Either::Left(PartialDerivationTree::TypeCheck(der_tree)));
                    sort
                }
                Err(err) => {
                    return Err(DerivationFailed {
                        head: fail_head,
                        label,
                        child,
                        extra,
                        err: ErrInfo::ErrOnTree(Box::new(err)),
                    });
                }
            };

            cxt.push_decl((x.clone(), *t.clone()));

            let type_m = match type_infer(gcxt, cxt.clone(), *m.clone()) {
                Ok(der_tree) => {
                    let type_of_m = der_tree.head.type_of_term.clone();
                    child.push(Either::Left(PartialDerivationTree::TypeCheck(der_tree)));
                    type_of_m
                }
                Err(err) => {
                    return Err(DerivationFailed {
                        head: fail_head,
                        label,
                        child,
                        extra,
                        err: ErrInfo::ErrOnTree(Box::new(err)),
                    });
                }
            };

            let infered_type = Exp::prod(x, *t, type_m);

            Ok(PartialDerivationTreeTypeCheck {
                head: make_head(infered_type),
                label,
                child,
                extra,
            })
        }
        Exp::App(t1, t2) => {
            extra.push(ExtraInfo::GeneratedBy("ProdElim".into()));

            let label = DerivationLabel::ProdElim;
            let (x, a, b) = match type_infered_to_prod(gcxt, cxt.clone(), *t1.clone()) {
                Ok((der_tree, (x, a, b))) => {
                    child.push(Either::Left(PartialDerivationTree::TypeCheck(der_tree)));
                    (x, a, b)
                }
                Err(err) => {
                    return Err(DerivationFailed {
                        head: fail_head,
                        label,
                        child,
                        extra,
                        err: ErrInfo::ErrOnTree(Box::new(err)),
                    });
                }
            };

            match type_check(gcxt, cxt.clone(), *t2.clone(), a.clone()) {
                Ok(der_tree) => {
                    child.push(Either::Left(PartialDerivationTree::TypeCheck(der_tree)));
                    let substed_type = subst(b, &x, &t2);
                    Ok(PartialDerivationTreeTypeCheck {
                        head: make_head(substed_type),
                        label,
                        child,
                        extra,
                    })
                }
                Err(err) => Err(DerivationFailed {
                    head: fail_head,
                    label,
                    child,
                    extra,
                    err: ErrInfo::ErrOnTree(Box::new(err)),
                }),
            }
        }
        Exp::IndTypeType { ind_type_name } => {
            extra.push(ExtraInfo::GeneratedBy("IndForm".into()));
            let label = DerivationLabel::IndForm;
            let type_of_ind_type = match gcxt.type_of_indtype(&ind_type_name) {
                Some(e) => e,
                None => {
                    return Err(DerivationFailed {
                        head: fail_head,
                        label,
                        child,
                        extra,
                        err: ErrInfo::ErrOnCondition(ErrOnCondition {
                            err: format!("inductive type {ind_type_name} is not found"),
                        }),
                    });
                }
            };

            Ok(PartialDerivationTreeTypeCheck {
                head: make_head(type_of_ind_type),
                label,
                child,
                extra,
            })
        }
        Exp::IndTypeCst {
            ind_type_name,
            constructor_name,
        } => {
            extra.push(ExtraInfo::GeneratedBy("IndIntro".into()));
            let label = DerivationLabel::IndIntro;
            let type_of_cst_type = match gcxt.type_of_cst(&ind_type_name, &constructor_name) {
                Some(e) => e,
                None => {
                    return Err(DerivationFailed {
                        head: fail_head,
                        label,
                        child,
                        extra,
                        err: ErrInfo::ErrOnCondition(ErrOnCondition {
                            err: format!("inductive type {ind_type_name} is not found"),
                        }),
                    });
                }
            };

            Ok(PartialDerivationTreeTypeCheck {
                head: make_head(type_of_cst_type),
                label,
                child,
                extra,
            })
        }
        Exp::IndTypeElim {
            ind_type_name,
            eliminated_exp,
            return_type,
            cases,
        } => {
            extra.push(ExtraInfo::GeneratedBy("IndElim".into()));
            let label = DerivationLabel::IndElim;

            // find ind type
            let inddefs = match gcxt.indtype_defs(&ind_type_name) {
                Some(inddefs) => inddefs,
                None => {
                    return Err(DerivationFailed {
                        head: fail_head,
                        label,
                        child,
                        extra,
                        err: ErrInfo::ErrOnCondition(ErrOnCondition {
                            err: format!("inductive type {ind_type_name} is not found"),
                        }),
                    });
                }
            };

            // return type infered to nice form
            let end_sort = match type_infered_to_ind_return_type(
                gcxt,
                cxt.clone(),
                *return_type.clone(),
                ind_type_name.clone(),
            ) {
                Ok((der_tree, end_sort)) => {
                    child.push(Either::Left(PartialDerivationTree::TypeCheck(der_tree)));
                    end_sort
                }
                Err(err) => {
                    return Err(DerivationFailed {
                        head: fail_head,
                        label,
                        child,
                        extra,
                        err: ErrInfo::ErrOnTree(Box::new(err)),
                    });
                }
            };

            // (sort of ind type, sort of return type) in rel
            match Condition::indrel_sort(*inddefs.arity().sort(), end_sort) {
                Ok(cond) => {
                    child.push(Either::Right(cond));
                }
                Err(err) => {
                    return Err(DerivationFailed {
                        head: fail_head,
                        label,
                        child,
                        extra,
                        err: ErrInfo::ErrOnCondition(err),
                    });
                }
            }

            // |- eliminated_exp: I a1 ... an where I == ind_type
            let arg_of_type = match type_infered_to_ind(gcxt, cxt.clone(), *eliminated_exp.clone())
            {
                Ok((der_tree, (type_name, args))) => {
                    child.push(Either::Left(PartialDerivationTree::TypeCheck(der_tree)));
                    if type_name != *inddefs.name() {
                        return Err(DerivationFailed {
                            head: fail_head,
                            label,
                            child,
                            extra,
                            err: ErrInfo::ErrOnCondition(ErrOnCondition {
                                err: format!(
                                    "type of {eliminated_exp} expected {} found {type_name}",
                                    { inddefs.name() }
                                ),
                            }),
                        });
                    }
                    args
                }
                Err(err) => {
                    return Err(DerivationFailed {
                        head: fail_head,
                        label,
                        child,
                        extra,
                        err: ErrInfo::ErrOnTree(Box::new(err)),
                    });
                }
            };

            // for each f[i],  |- f[i]: eliminator_type
            for (cname, c) in inddefs.constructors() {
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

                match type_check(gcxt, cxt.clone(), corresponding_case, expected) {
                    Ok(der_tree) => {
                        child.push(Either::Left(PartialDerivationTree::TypeCheck(der_tree)));
                    }
                    Err(err) => {
                        return Err(DerivationFailed {
                            head: fail_head,
                            label,
                            child,
                            extra,
                            err: ErrInfo::ErrOnTree(Box::new(err)),
                        });
                    }
                };
            }

            let type_of_term = Exp::App(
                Box::new(utils::assoc_apply(
                    *return_type.clone(),
                    arg_of_type.clone(),
                )),
                Box::new(*eliminated_exp.clone()),
            );

            Ok(PartialDerivationTreeTypeCheck {
                head: make_head(type_of_term),
                label,
                child,
                extra,
            })
        }
        Exp::Proof(t) => {
            let label = DerivationLabel::Proof;
            extra.push(ExtraInfo::GeneratedBy("Proof".into()));
            let provablejudgement = ProvableJudgement {
                context: cxt.clone(),
                proposition: *t.clone(),
            };
            let child = vec![Either::Left(PartialDerivationTree::Unproved(
                provablejudgement,
            ))];
            Ok(PartialDerivationTreeTypeCheck {
                head: make_head(*t.clone()),
                label,
                child,
                extra,
            })
        }
        Exp::Sub(x, a, p) => {
            extra.push(ExtraInfo::GeneratedBy("SubForm".into()));
            let label = DerivationLabel::SubsetForm;
            let mut child = vec![];
            match type_check(gcxt, cxt.clone(), *a.clone(), Exp::Sort(Sort::Set)) {
                Ok(der_tree) => {
                    child.push(Either::Left(PartialDerivationTree::TypeCheck(der_tree)))
                }
                Err(err) => {
                    return Err(DerivationFailed {
                        head: fail_head,
                        label,
                        child,
                        err: ErrInfo::ErrOnTree(Box::new(err)),
                        extra,
                    })
                }
            };

            cxt.push_decl((x, *a.clone()));
            match type_check(gcxt, cxt.clone(), *p.clone(), Exp::Sort(Sort::Prop)) {
                Ok(der_tree) => {
                    child.push(Either::Left(PartialDerivationTree::TypeCheck(der_tree)));
                }
                Err(err) => {
                    return Err(DerivationFailed {
                        head: fail_head,
                        label,
                        child,
                        err: ErrInfo::ErrOnTree(Box::new(err)),
                        extra,
                    })
                }
            }
            Ok(PartialDerivationTreeTypeCheck {
                head: make_head(Exp::Pow(a)),
                label,
                child,
                extra,
            })
        }
        Exp::Pow(a) => {
            extra.push(ExtraInfo::GeneratedBy("PowForm".into()));
            let label = DerivationLabel::PowerSetForm;
            match type_check(gcxt, cxt.clone(), *a.clone(), Exp::Sort(Sort::Set)) {
                Ok(der_tree) => {
                    child.push(Either::Left(PartialDerivationTree::TypeCheck(der_tree)));
                }
                Err(err) => {
                    return Err(DerivationFailed {
                        head: fail_head,
                        label,
                        child,
                        err: ErrInfo::ErrOnTree(Box::new(err)),
                        extra,
                    });
                }
            }
            Ok(PartialDerivationTreeTypeCheck {
                head: make_head(Exp::Sort(Sort::Set)),
                label,
                child,
                extra,
            })
        }
        Exp::Pred(a, b) => {
            extra.push(ExtraInfo::GeneratedBy("Pred".into()));
            let label = DerivationLabel::PredForm;
            match type_check(gcxt, cxt.clone(), *a.clone(), Exp::Sort(Sort::Set)) {
                Ok(der_tree) => {
                    child.push(Either::Left(PartialDerivationTree::TypeCheck(der_tree)));
                }
                Err(err) => {
                    return Err(DerivationFailed {
                        head: fail_head,
                        label,
                        child,
                        err: ErrInfo::ErrOnTree(Box::new(err)),
                        extra,
                    });
                }
            }
            match type_check(gcxt, cxt.clone(), *b.clone(), Exp::Pow(a.clone())) {
                Ok(der_tree) => {
                    child.push(Either::Left(PartialDerivationTree::TypeCheck(der_tree)));
                }
                Err(err) => {
                    return Err(DerivationFailed {
                        head: fail_head,
                        label,
                        child,
                        err: ErrInfo::ErrOnTree(Box::new(err)),
                        extra,
                    });
                }
            }
            Ok(PartialDerivationTreeTypeCheck {
                head: make_head(Exp::prod(Var::Unused, *a.clone(), Exp::Sort(Sort::Prop))),
                label,
                child,
                extra,
            })
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UserLabel {}

pub fn proof_tree(
    gcxt: &GlobalContext,
    mut cxt: LocalContext,
    term1: Exp,
    user_label: UserLabel,
) -> PartialDerivationTreeProof {
    todo!()
}

pub mod printing {
    use super::*;
    use colored::Colorize;
    fn indent_size(indent: usize) -> String {
        (0..indent).map(|_| "  ").collect()
    }
    pub fn print_tree_type_check(tree: PartialDerivationTreeTypeCheck) -> String {
        print_tree_type_check_rec(PartialDerivationTree::TypeCheck(tree), 0)
            .into_iter()
            .map(|s| format!("{s}\n"))
            .collect()
    }
    fn print_tree_type_check_rec(tree: PartialDerivationTree, indent: usize) -> Vec<String> {
        let mut v = vec![];
        let (child, extra) = match tree {
            PartialDerivationTree::TypeCheck(tree) => {
                let PartialDerivationTreeTypeCheck {
                    head,
                    label,
                    child,
                    extra,
                } = tree;
                v.push(format!("{}{head}({label})", indent_size(indent)));
                (child, extra)
            }
            PartialDerivationTree::Proof(tree) => {
                let PartialDerivationTreeProof {
                    head,
                    label,
                    child,
                    extra,
                } = tree;
                v.push(format!("{}{head}({label})", indent_size(indent)));
                (child, extra)
            }
            PartialDerivationTree::Unproved(judgement) => {
                v.push(format!("{judgement}"));
                (vec![], vec![])
            }
        };
        for e in extra {
            match e {
                ExtraInfo::GeneratedBy(string) => {
                    v.push(format!("{}{string}", indent_size(indent)));
                }
                ExtraInfo::OtherInfo(string) => {
                    v.push(format!("{}{string}", indent_size(indent)));
                }
            }
        }
        for c in child {
            match c {
                Either::Left(tree) => {
                    v.extend(print_tree_type_check_rec(tree, indent + 1));
                }
                Either::Right(cond) => v.push(format!("{}{cond}", indent_size(indent + 1))),
            }
        }
        v
    }
    pub fn print_fail_tree_rec(tree: DerivationFailed, indent: usize) -> Vec<String> {
        let mut v = vec![];
        let DerivationFailed {
            head,
            label,
            child,
            extra,
            err,
        } = tree;
        match head {
            FailHead::InferFail(cxt, term) => {
                let colered = format!("!{cxt} |- {term}",).red();
                v.push(format!("{}{colered}({label})", indent_size(indent)));
            }
            FailHead::CheckFail(judgement) => {
                let colered = format!("!{judgement}",).red();
                v.push(format!("{}{colered}({label})", indent_size(indent)));
            }
        }
        for e in extra {
            match e {
                ExtraInfo::GeneratedBy(string) => {
                    v.push(format!("{}{string}", indent_size(indent)));
                }
                ExtraInfo::OtherInfo(string) => {
                    v.push(format!("{}{string}", indent_size(indent)));
                }
            }
        }
        for c in child {
            match c {
                Either::Left(tree) => v.extend(print_tree_type_check_rec(tree, indent + 1)),
                Either::Right(cond) => v.push(format!("{}{cond}", indent_size(indent + 1))),
            }
        }
        match err {
            ErrInfo::ErrOnCondition(err_cond) => {
                let colered = format!("{}", err_cond.err).red();
                v.push(format!("{}{colered}", indent_size(indent + 1)))
            }
            ErrInfo::ErrOnTree(tree) => {
                v.extend(print_fail_tree_rec(*tree, indent + 1));
            }
        }
        v
    }
    pub fn print_fail_tree(tree: DerivationFailed) -> String {
        print_fail_tree_rec(tree, 0)
            .into_iter()
            .map(|s| format!("{s}\n"))
            .collect()
    }
}
