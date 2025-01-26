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
pub enum ResIndDefsError {
    AlreadyDefinedType,
    ArityNotWellformed(DerivationFailed),
    ConstructorNotWellFormed(Vec<Result<PartialDerivationTreeTypeCheck, DerivationFailed>>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResIndDefsOk {
    pub arity_well_formed: PartialDerivationTreeTypeCheck,
    pub constructor_wellformed: Vec<PartialDerivationTreeTypeCheck>,
}

impl GlobalContext {
    pub fn push_new_ind(
        &mut self,
        defs: inductives::IndTypeDefs,
    ) -> Result<ResIndDefsOk, ResIndDefsError> {
        if self
            .inductive_definitions
            .iter()
            .any(|inddefs| inddefs.name() == defs.name())
        {
            return Err(ResIndDefsError::AlreadyDefinedType);
        }

        // arity の well defined
        let arity_exp: Exp = defs.arity().clone().into();
        let arity_well_formed = match type_infered_to_sort(self, LocalContext::default(), arity_exp)
        {
            Ok((der_tree, sort)) => der_tree,
            Err(err) => return Err(ResIndDefsError::ArityNotWellformed(err)),
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

        if !flag {
            Err(ResIndDefsError::ConstructorNotWellFormed(
                constructor_well_formed,
            ))
        } else {
            self.inductive_definitions.push(defs);
            Ok(ResIndDefsOk {
                arity_well_formed,
                constructor_wellformed: constructor_well_formed
                    .into_iter()
                    .map(|res| res.unwrap())
                    .collect(),
            })
        }

        // ResIndDefs {
        //     single: true,
        //     arity_well_formed: Some(arity_well_formed),
        //     constructor_well_formed: Some(constructor_well_formed),
        // }
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

impl ProvableJudgement {
    fn predicate_element(context: LocalContext, large: Exp, sub: Exp, element: Exp) -> Self {
        let proposition = {
            let pred = Exp::Pred(Box::new(large), Box::new(sub));
            Exp::App(Box::new(pred), Box::new(element))
        };
        ProvableJudgement {
            context,
            proposition,
        }
    }
}

impl Display for ProvableJudgement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ProvableJudgement {
            context,
            proposition,
        } = self;
        write!(f, "{context} |= {proposition}")
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
        write!(f, "{context} |- {term}:  {type_of_term}")
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
        let s2 = s.type_of_sort();
        Ok((Condition::SortAxiom(s, s2), s2))
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
    PowerSetForm,   // A: SET => Pow(A): SET
    PowerSetWeak,   // A: Pow(B) => A: SET
    SubsetForm,     // {x: A | P}: SET
    SubsetIntro,    // t: A, B: Pow(A), Pred(A, B) t => t: B
    SubsetElimSet,  // t: B, B: Pow(A) => t: A
    SubsetElimProp, // t: B, B:Pow(A) => Pred(A, B) t
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
pub enum DerivationLabelProof {}

impl Display for DerivationLabelProof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: &str = match self {
            _ => todo!(),
        };
        write!(f, "{}", s)
    }
}

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub enum ExtraInfo {
//     GeneratedBy(String),
//     OtherInfo(String),
// }

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub enum ErrInfo {
//     ErrOnCondition(ErrOnCondition),
//     ErrOnTree(Box<DerivationFailed>),
// }

// impl From<ErrOnCondition> for ErrInfo {
//     fn from(value: ErrOnCondition) -> Self {
//         ErrInfo::ErrOnCondition(value)
//     }
// }

// impl From<DerivationFailed> for ErrInfo {
//     fn from(value: DerivationFailed) -> Self {
//         ErrInfo::ErrOnTree(Box::new(value))
//     }
// }

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DerChild {
    PartialDerivationTree(PartialDerivationTreeTypeCheck),
    Condition(Condition),
    NeedProve(ProvableJudgement),
    Label(DerivationLabel),
    Info(Info),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Info {
    Context(String),
    ErrCond(ErrOnCondition),
    ErrDer(Box<DerivationFailed>),
}

impl From<PartialDerivationTreeTypeCheck> for DerChild {
    fn from(value: PartialDerivationTreeTypeCheck) -> Self {
        DerChild::PartialDerivationTree(value)
    }
}

impl From<Condition> for DerChild {
    fn from(value: Condition) -> Self {
        DerChild::Condition(value)
    }
}

impl From<ProvableJudgement> for DerChild {
    fn from(value: ProvableJudgement) -> Self {
        DerChild::NeedProve(value)
    }
}

impl From<DerivationLabel> for DerChild {
    fn from(value: DerivationLabel) -> Self {
        DerChild::Label(value)
    }
}

impl From<Info> for DerChild {
    fn from(value: Info) -> Self {
        DerChild::Info(value)
    }
}

impl From<String> for DerChild {
    fn from(value: String) -> Self {
        DerChild::Info(Info::Context(value))
    }
}

impl From<ErrOnCondition> for DerChild {
    fn from(value: ErrOnCondition) -> Self {
        DerChild::Info(Info::ErrCond(value))
    }
}

impl From<DerivationFailed> for DerChild {
    fn from(value: DerivationFailed) -> Self {
        DerChild::Info(Info::ErrDer(Box::new(value)))
    }
}

// impl From<ExtraInfo> for DerChild {
//     fn from(value: ExtraInfo) -> Self {
//         DerChild::Info(Either::Left(value))
//     }
// }

// impl From<ErrInfo> for DerChild {
//     fn from(value: ErrInfo) -> Self {
//         DerChild::Info(Either::Right(value))
//     }
// }

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub struct TreeBuilder {
//     pub head: Either<TypeCheckJudgement, TypeUnSetted>,
//     pub label: Option<DerivationLabel>,
//     pub child: Vec<DerChild>,
//     pub context: Vec<DerChild>,
// }

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub struct TypeUnSetted {
//     context: LocalContext,
//     term: Exp,
// }

// impl TreeBuilder {
//     fn build(self) -> Result<PartialDerivationTreeTypeCheck, String> {
//         let TreeBuilder {
//             head,
//             label,
//             child,
//             context,
//         } = self;
//         let Some(label) = label else {
//             return Err(format!("label is not setted"));
//         };
//         todo!()
//     }
//     fn next(&mut self) {
//         let label = self.label.take();
//         let child: Vec<_> = self.child.drain(..).collect();
//         self.context.push();
//     }
//     fn failed_tree(self) -> DerivationFailed {
//         todo!()
//     }
// }

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartialDerivationTreeTypeCheck {
    pub head: TypeCheckJudgement,
    pub info: Vec<DerChild>,
    // pub child: Vec<DerChild>,
    // pub extra: Vec<ExtraInfo>,
}

impl PartialDerivationTreeTypeCheck {
    pub fn get_goals(&self) -> Vec<ProvableJudgement> {
        let mut v = vec![];
        for der_child in &self.info {
            match der_child {
                DerChild::PartialDerivationTree(partial_derivation_tree_type_check) => {
                    v.extend(partial_derivation_tree_type_check.get_goals());
                }
                DerChild::Condition(_) => {}
                DerChild::NeedProve(provable_judgement) => {
                    v.push(provable_judgement.clone());
                }
                DerChild::Label(_) => {}
                DerChild::Info(_) => {}
            }
        }
        v
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartialDerivationTreeProof {
    pub head: ProvableJudgement,
    pub info: Vec<DerChild>,
    pub label: DerivationLabel,
    // pub child: Vec<DerChild>,
    // pub extra: Vec<ExtraInfo>,
}

impl PartialDerivationTreeProof {
    fn add_child<T>(&mut self, t: T)
    where
        DerChild: From<T>,
    {
        self.info.push(t.into());
    }
}

impl PartialDerivationTreeTypeCheck {
    fn of_type(&self) -> &Exp {
        &self.head.type_of_term
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FailHead {
    InferFail(LocalContext, Exp),
    CheckFail(TypeCheckJudgement),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DerivationFailed {
    pub head: FailHead,
    pub info: Vec<DerChild>,
    // label: DerivationLabel,
    // child: Vec<DerChild>,
    // err: ErrInfo,
    // extra: Vec<ExtraInfo>,
}

pub fn type_check(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    term1: Exp,
    expected: Exp,
) -> Result<PartialDerivationTreeTypeCheck, DerivationFailed> {
    let head = TypeCheckJudgement {
        context: cxt.clone(),
        term: term1.clone(),
        type_of_term: expected.clone(),
    };
    let fail_head = FailHead::CheckFail(head.clone());

    let mut info: Vec<DerChild> = vec![];
    info.push(format!("infer {term1} |> {expected}").into());

    // get infered type of term1
    let infered_tree = match type_infer(gcxt, cxt.clone(), term1.clone()) {
        Ok(ok) => ok,
        Err(err) => {
            // term1 should infered type
            return Err(DerivationFailed {
                head: fail_head,
                info,
            });
        }
    };

    // get infered sort of expected
    let (sort_of_expected_tree, sort_of_expected) =
        match type_infered_to_sort(gcxt, cxt.clone(), expected.clone()) {
            Ok(ok) => ok,
            Err(err) => {
                // expected should have infered sort
                return Err(DerivationFailed {
                    head: fail_head,
                    info,
                });
            }
        };

    // 1. if infered =^beta expected => OK (by Conv Rule)
    info.push("conv ?".to_string().into());
    let err = match Condition::convertible(gcxt, expected.clone(), infered_tree.of_type().clone()) {
        Ok(cond) => {
            // ok by conv
            info.push(cond.into());
            info.push(DerivationLabel::Conv.into());
            return Ok(PartialDerivationTreeTypeCheck { head, info });
        }
        Err(err) => err,
    };
    info.push(err.into());

    // 2. if infered ->* Pow(A), expected ->* SET => Ok (by PowWeak)
    info.push("pow weak ?".to_string().into());
    let err: DerChild = 'pow_weak: {
        // 1. check expected ->* SET
        let (cond_expected_set, sort) = match Condition::reduce_to_sort(gcxt, expected.clone()) {
            Ok(cond) => cond,
            Err(err) => {
                break 'pow_weak err.into();
            }
        };
        if sort != Sort::Set {
            break 'pow_weak format!("expected ->*! SET but {sort}").into();
        }

        // 2. infered ->* Pow(A)
        let (cond_infered_pow, pow) =
            match Condition::reduce_to_pow(gcxt, infered_tree.of_type().clone()) {
                Ok(ok) => ok,
                Err(err) => {
                    break 'pow_weak format!("infered ->*! Pow").into();
                }
            };

        // ok by powersetweak
        info.push(cond_expected_set.into());
        info.push(cond_infered_pow.into());
        info.push(DerivationLabel::PowerSetWeak.into());

        return Ok(PartialDerivationTreeTypeCheck { head, info });
    };
    info.push(err.into());

    // 3. if expected ->* Pow(super_expected)
    // check cxt |- term1 <| super_expected ask cxt |= Pred(super_expected, expected) term1

    let err: DerChild = 'sub_intro: loop {
        // 1. check expected ->* Pow(A)
        let (cond_expected_pow, super_expected) =
            match Condition::reduce_to_pow(gcxt, expected.clone()) {
                Ok(cond) => cond,
                Err(err) => {
                    break 'sub_intro err.into();
                }
            };

        // 2. check term1 <| A
        let term1_weak_tree =
            match type_check(gcxt, cxt.clone(), term1.clone(), super_expected.clone()) {
                Ok(ok) => ok,
                Err(err) => {
                    break 'sub_intro err.into();
                }
            };

        // let prop := cxt |= Pred(A, expected) term1
        let proposition = Exp::pred_of_element(super_expected, expected, term1);

        info.push(cond_expected_pow.into());
        info.push(term1_weak_tree.into());
        info.push(
            ProvableJudgement {
                context: cxt.clone(),
                proposition,
            }
            .into(),
        );
        info.push(DerivationLabel::SubsetIntro.into());

        return Ok(PartialDerivationTreeTypeCheck { head, info });
    };
    info.push(err);

    // 4. otherwise
    // expected has no super set .. so outermost super set should equal to expected
    // check cxt |- infered <= A_1 <= ... <= A_n !<= term with expected =~ A_n
    let err = 'subset_elim_set: loop {
        let mut set = infered_tree.of_type().clone();
        while let Ok((super_set_tree, super_set)) =
            type_infered_to_pow(gcxt, cxt.clone(), set.clone())
        {
            info.push(super_set_tree.into());
            set = super_set;
        }

        let cond = match Condition::convertible(gcxt, expected.clone(), set) {
            Ok(cond) => cond,
            Err(err) => {
                break 'subset_elim_set err.into();
            }
        };

        info.push(cond.into());
        info.push(DerivationLabel::SubsetElimSet.into());
        return Ok(PartialDerivationTreeTypeCheck { head, info });
    };
    info.push(err);

    Err(DerivationFailed {
        head: FailHead::CheckFail(head),
        info,
    })
}

// Γ |- t |>_s (s in S) かどうか
pub fn type_infered_to_sort(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    term: Exp,
) -> Result<(PartialDerivationTreeTypeCheck, Sort), DerivationFailed> {
    let mut info = vec!["infered sort".to_string().into()];

    // get T of G |- t |> infered
    let der_tree_infered = match type_infer(gcxt, cxt.clone(), term.clone()) {
        Ok(der_tree_check) => der_tree_check,
        Err(derivation_failed) => {
            info.push("no infered type".to_string().into());
            info.push(derivation_failed.into());
            // t should have type
            return Err(DerivationFailed {
                head: FailHead::InferFail(cxt, term),
                info,
            });
        }
    };

    // 1. if infered =~ sort => ok
    let err: DerChild = 'conv_to_sort: loop {
        // 1. infered ->* sort ?
        let (cond, infered_sort) =
            match Condition::reduce_to_sort(gcxt, der_tree_infered.of_type().clone()) {
                Ok(cond) => cond,
                Err(err) => {
                    break 'conv_to_sort err.into();
                }
            };

        info.push(cond.into());
        info.push(DerivationLabel::Conv.into());

        // ok
        return Ok((
            PartialDerivationTreeTypeCheck {
                head: TypeCheckJudgement {
                    context: cxt,
                    term,
                    type_of_term: Exp::Sort(infered_sort),
                },
                info,
            },
            infered_sort,
        ));
    };
    info.push(err);

    match Condition::reduce_to_sort(gcxt, infered_term.clone()) {
        Ok((cond, sort)) => {
            child.push(cond.into());
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
                    child.push(cond.into());
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
                            child: vec![der_tree_up.into()],
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
                err: derivation_failed.into(),
            });
        }
    };

    let mut weak_infered_type = der_tree_infered.head.type_of_term.clone();
    child.push(der_tree_infered.clone().into());
    let mut der_tree_weak_infered = der_tree_infered;

    // Γ |- infered <= ... <= max_infered: SET
    let weak_infered_type = loop {
        match type_infered_to_pow(gcxt, cxt.clone(), weak_infered_type.clone()) {
            Ok((der_tree_pow, weak_infered_next)) => {
                let der_tree_pow = PartialDerivationTreeTypeCheck {
                    head: TypeCheckJudgement {
                        context: cxt.clone(),
                        term: term.clone(),
                        type_of_term: weak_infered_type,
                    },
                    label: DerivationLabel::SubsetElimSet,
                    child: vec![der_tree_pow.into(), der_tree_weak_infered.into()],
                    extra: vec![ExtraInfo::GeneratedBy("pow weak".into())],
                };
                weak_infered_type = weak_infered_next;
                der_tree_weak_infered = der_tree_pow;
            }
            Err(_) => {
                break weak_infered_type;
            }
        }
    };

    match Condition::reduce_to_prod(gcxt, weak_infered_type) {
        Ok((cond, (x, a, b))) => {
            child.push(cond.into());
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

// Γ |- t1 |> P(t2) かどうか
pub fn type_infered_to_pow(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    term: Exp,
) -> Result<(PartialDerivationTreeTypeCheck, Exp), DerivationFailed> {
    let mut child = vec![];
    let extra = vec![ExtraInfo::GeneratedBy("type infered to cal".to_string())];

    let der_tree_infered = match type_infer(gcxt, cxt.clone(), term.clone()) {
        Ok(der_tree_check) => der_tree_check,
        Err(derivation_failed) => {
            return Err(DerivationFailed {
                head: FailHead::InferFail(cxt, term),
                label: DerivationLabel::Conv,
                child,
                extra,
                err: derivation_failed.into(),
            });
        }
    };

    let infered_type = der_tree_infered.of_type().clone();
    child.push(der_tree_infered.into());

    match Condition::reduce_to_pow(gcxt, infered_type) {
        Ok((cond, pow)) => {
            child.push(cond.into());
            Ok((
                PartialDerivationTreeTypeCheck {
                    head: TypeCheckJudgement {
                        context: cxt,
                        term,
                        type_of_term: Exp::Pow(Box::new(pow.clone())),
                    },
                    label: DerivationLabel::Conv,
                    child,
                    extra,
                },
                pow,
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
                err: derivation_failed.into(),
            });
        }
    };

    let infered_term = der_tree_infered.head.type_of_term.clone();
    child.push(der_tree_infered.into());

    match Condition::reduce_to_indtype(gcxt, infered_term) {
        Ok((cond, (type_name, args))) => {
            child.push(cond.into());
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
                err: derivation_failed.into(),
            });
        }
    };

    let infered_term = der_tree_infered.head.type_of_term.clone();

    child.push(der_tree_infered.into());

    match Condition::reduce_to_returntype(gcxt, infered_term, type_name) {
        Ok((cond, (_params, sort))) => {
            child.push(cond.into());
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
                    child.push(cond.into());
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
                    child.push(der_tree.into());
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
                    child.push(der_tree.into());
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
                    child.push(cond.into());
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
                    child.push(der_tree.into());
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
                    child.push(der_tree.into());
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
                    child.push(der_tree.into());
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
                    child.push(der_tree.into());
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
                    child.push(der_tree.into());
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
                    child.push(cond.into());
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
                    child.push(der_tree.into());
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
                        child.push(der_tree.into());
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
            let child = vec![provablejudgement.into()];
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
                Ok(der_tree) => child.push(der_tree.into()),
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
                    child.push(der_tree.into());
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
                    child.push(der_tree.into());
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
                    child.push(der_tree.into());
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
                    child.push(der_tree.into());
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
    use termtree::Tree;

    #[derive(Debug, Clone, PartialEq, Eq)]
    enum Node {
        TypeCheckJudgement(TypeCheckJudgement, DerivationLabel),
        ProvableJudgement(ProvableJudgement),
        Condition(Condition),
        Fail(FailHead, DerivationLabel),
        ErrCond(ErrOnCondition),
        ExtraInfo(ExtraInfo),
    }

    fn error_string(s: String) -> String {
        format!("{}", s.red())
    }

    impl Display for Node {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let s: String = match self {
                Node::TypeCheckJudgement(type_check_judgement, label) => {
                    format!("{type_check_judgement} ({})", format!("{label}").green())
                }
                Node::ProvableJudgement(provable_judgement) => format!("{provable_judgement}"),
                Node::Condition(condition) => format!("{condition}"),
                Node::Fail(fail_head, label) => match fail_head {
                    FailHead::InferFail(local_context, exp) => {
                        error_string(format!("!{local_context} {exp} ({label})"))
                    }
                    FailHead::CheckFail(type_check_judgement) => {
                        error_string(format!("{type_check_judgement} {label}"))
                    }
                },
                Node::ErrCond(err) => error_string(err.err.clone()),
                Node::ExtraInfo(extra_info) => format!("{extra_info:?}"),
            };
            write!(f, "{s}")
        }
    }

    fn tree_partial_derivation_tree(tree: &PartialDerivationTreeTypeCheck) -> Tree<Node> {
        let PartialDerivationTreeTypeCheck {
            head,
            label,
            child,
            extra,
        } = tree;
        let mut tree = Tree::new(Node::TypeCheckJudgement(head.clone(), label.clone()));
        tree.extend(child.iter().map(|child| match child {
            DerChild::PartialDerivationTree(partial_derivation_tree_type_check) => {
                tree_partial_derivation_tree(partial_derivation_tree_type_check)
            }
            DerChild::Condition(condition) => Tree::new(Node::Condition(condition.clone())),
            DerChild::NeedProve(provable_judgement) => {
                Tree::new(Node::ProvableJudgement(provable_judgement.clone()))
            }
        }));
        tree.extend(
            extra
                .iter()
                .map(|extra| Tree::new(Node::ExtraInfo(extra.clone()))),
        );
        tree
    }

    pub fn print_tree(tree: &PartialDerivationTreeTypeCheck) {
        println!("{}", tree_partial_derivation_tree(tree))
    }

    fn tree_fail_tree(tree: &DerivationFailed) -> Tree<Node> {
        let DerivationFailed {
            head,
            label,
            child,
            err,
            extra,
        } = tree;
        let mut tree = Tree::new(Node::Fail(head.clone(), label.clone()));
        tree.extend(child.iter().map(|child| match child {
            DerChild::PartialDerivationTree(partial_derivation_tree_type_check) => {
                tree_partial_derivation_tree(partial_derivation_tree_type_check)
            }
            DerChild::Condition(condition) => Tree::new(Node::Condition(condition.clone())),
            DerChild::NeedProve(provable_judgement) => {
                Tree::new(Node::ProvableJudgement(provable_judgement.clone()))
            }
        }));
        tree.extend(
            extra
                .iter()
                .map(|extra| Tree::new(Node::ExtraInfo(extra.clone()))),
        );
        tree.extend(vec![match err {
            ErrInfo::ErrOnCondition(err_on_condition) => {
                Tree::new(Node::ErrCond(err_on_condition.clone()))
            }
            ErrInfo::ErrOnTree(derivation_failed) => tree_fail_tree(derivation_failed),
        }]);
        tree
    }

    pub fn print_fail_tree(tree: &DerivationFailed) {
        println!("{}", tree_fail_tree(tree))
    }
}
