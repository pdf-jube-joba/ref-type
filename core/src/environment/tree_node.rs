use super::*;
use crate::utils;

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
    // if cxt already has var d.0 => false
    pub fn push_decl(&mut self, d: (Var, Exp)) -> bool {
        if self.search_var_exp(&d.0).is_none() {
            self.0.push(d);
            true
        } else {
            false
        }
    }
    pub fn search_var_exp(&self, var: &Var) -> Option<&(Var, Exp)> {
        self.0.iter().find(|(v, _)| v == var)
    }
    pub fn new_variable(&self) -> Var {
        let i = self.0.iter().map(|(v, _)| fresh_var(v)).max().unwrap_or(0);
        Var::Internal("cxt created".to_string(), i)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvableJudgement {
    pub context: LocalContext,
    pub proposition: Exp,
}

impl ProvableJudgement {
    pub fn predicate_element(context: LocalContext, large: Exp, sub: Exp, element: Exp) -> Self {
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
    pub fn context_has_var(cxt: LocalContext, var: Var) -> Result<(Self, Exp), ErrOnCondition> {
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
    pub fn convertible(
        gcxt: &GlobalContext,
        term1: Exp,
        term2: Exp,
    ) -> Result<Self, ErrOnCondition> {
        if beta_equiv(gcxt, term1.clone(), term2.clone()) {
            Ok(Condition::Convertible(term1, term2))
        } else {
            Err(format!("{term1} !=~ {term2}").into())
        }
    }
    pub fn reduce_to_sort(gcxt: &GlobalContext, term: Exp) -> Result<(Self, Sort), ErrOnCondition> {
        let term2 = normalize(gcxt, term.clone());
        match term2 {
            Exp::Sort(s) => Ok((Condition::Convertible(term, Exp::Sort(s)), s)),
            _ => Err(format!("{term} !->* sort").into()),
        }
    }
    pub fn reduce_to_prod(
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
    pub fn reduce_to_pow(gcxt: &GlobalContext, term: Exp) -> Result<(Self, Exp), ErrOnCondition> {
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
    pub fn reduce_to_indtype(
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
    pub fn reduce_to_returntype(
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
    pub fn axiom_sort(s: Sort) -> Result<(Self, Sort), ErrOnCondition> {
        let s2 = s.type_of_sort();
        Ok((Condition::SortAxiom(s, s2), s2))
    }
    pub fn relation_sort(s1: Sort, s2: Sort) -> Result<(Self, Sort), ErrOnCondition> {
        match s1.relation_of_sort(s2) {
            Some(s3) => Ok((Condition::SortRelation(s1, s2, s3), s3)),
            None => Err(format!("({s1}, {s2}) is not in rel").into()),
        }
    }
    pub fn indrel_sort(s1: Sort, s2: Sort) -> Result<Self, ErrOnCondition> {
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
    PredForm,       // B: Pow(A) => Pred(A, B): A -> PROP
    IdentityForm,   // Id(A, a, b)
    IdentityIntro,  // Refl(A, a): Id(A, a, a)
    // IdentityELim
    ExistsIntro, // exists T
    TakeIntro,   // => Take x:A. m: M
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
            DerivationLabel::IdentityForm => "IdentityForm",
            DerivationLabel::IdentityIntro => "IdentityIntro",
            DerivationLabel::ExistsIntro => "ExistsIntro",
            DerivationLabel::TakeIntro => "TakeIntro",
        };
        write!(f, "{}", s)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DerivationLabelProof {
    Test,
}

impl Display for DerivationLabelProof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: &str = match self {
            DerivationLabelProof::Test => "test",
        };
        write!(f, "{}", s)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ErrInfo {
    Condition(ErrOnCondition),
    FailTree(DerivationFailed),
    Other(String),
}

impl From<ErrOnCondition> for ErrInfo {
    fn from(value: ErrOnCondition) -> Self {
        ErrInfo::Condition(value)
    }
}

impl From<DerivationFailed> for ErrInfo {
    fn from(value: DerivationFailed) -> Self {
        ErrInfo::FailTree(value)
    }
}

impl From<String> for ErrInfo {
    fn from(value: String) -> Self {
        ErrInfo::Other(value)
    }
}
