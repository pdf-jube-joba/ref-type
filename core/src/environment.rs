use crate::{
    ast::*,
    lambda_calculus::*,
    typing::{type_check, type_infer, type_infered_to_sort},
};
use std::fmt::Display;

use self::utils::{assoc_apply, assoc_lam, assoc_prod, decompose_to_app_exps};

pub mod inductives {
    use super::*;

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct IndTypeDefs {
        name: TypeName,
        variable: Var,
        arity: (Vec<(Var, Exp)>, Sort),
        constructors: Vec<(ConstructorName, ConstructorType)>,
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    // P1 -> ... -> Pn -> X m1 ... mk
    pub struct ConstructorType {
        end: (Var, Vec<Exp>),  // = X m1 ... mk
        params: Vec<ParamCst>, // P[.]
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum ParamCst {
        Positive(Positive), // (_: P) -> C where P is positive of variable = X
        Simple((Var, Exp)), // (x: A) -> C where A.free_var does not contains X
    }

    // variable = X, parameter = [(y_1, M_1), ..., (y_k, M_k)], exps = [N_1, ... N_l]
    // => (y_1: M_1) -> ... -> (y_k: M_k) -> (X N_1 ... N_l)
    // free variable of Pos is only X
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Positive {
        parameter: Vec<(Var, Exp)>,
        variable: Var,
        exps: Vec<Exp>,
    }

    impl ConstructorType {
        pub fn variable(&self) -> &Var {
            &self.end.0
        }
        pub fn arg_num(&self) -> usize {
            self.params.len()
        }
        pub fn arg_end(&self) -> &Vec<Exp> {
            &self.end.1
        }
        pub fn new_constructor(
            end: (Var, Vec<Exp>),
            params: Vec<ParamCst>,
        ) -> Result<(Self, Var), String> {
            let var_type = end.0.clone();
            for p in &params {
                match p {
                    ParamCst::Positive(positive) => {}
                    ParamCst::Simple((x, a)) => {}
                }
            }
            Ok((Self { end, params }, var_type))
        }
    }

    impl From<ConstructorType> for Exp {
        fn from(value: ConstructorType) -> Exp {
            let ConstructorType {
                end: (v, exps),
                params,
            } = value;
            let mut end = assoc_apply(Exp::Var(v), exps);
            for p in params.into_iter().rev() {
                match p {
                    ParamCst::Positive(positive) => {
                        end = Exp::prod(Var::Unused, positive.into(), end);
                    }
                    ParamCst::Simple((var, a)) => end = Exp::prod(var, a, end),
                }
            }
            end
        }
    }
    impl Positive {
        pub fn parameter(&self) -> &Vec<(Var, Exp)> {
            &self.parameter
        }
        pub fn exps(&self) -> &Vec<Exp> {
            &self.exps
        }
        pub fn subst(&self, e: Exp) -> Exp {
            let Positive {
                parameter,
                variable: _,
                exps,
            } = self.clone();
            assoc_prod(parameter, assoc_apply(e, exps))
        }
        pub fn new(
            variable: Var,
            parameter: Vec<(Var, Exp)>,
            exps: Vec<Exp>,
        ) -> Result<Self, String> {
            for (_, a) in &parameter {
                // a.free_variables() <=(subset) allow
                if a.free_variable().contains(&variable) {
                    return Err(format!("pos param {a:?} contains {variable:?}"));
                }
            }

            for e in &exps {
                if e.free_variable().contains(&variable) {
                    return Err(format!("arg {e:?} contains {variable:?}"));
                }
            }

            let positive = Positive {
                variable,
                parameter,
                exps,
            };

            Ok(positive)
        }
    }

    impl From<Positive> for Exp {
        fn from(
            Positive {
                variable,
                parameter,
                exps,
            }: Positive,
        ) -> Self {
            assoc_prod(parameter, assoc_apply(Exp::Var(variable), exps))
        }
    }

    impl ConstructorType {
        pub fn eliminator_type(&self, q: Exp, mut c: Exp) -> Exp {
            let Self { end, params } = self;

            let mut usable_fresh_var: usize = {
                let end_fresh = end.1.iter().map(|e| fresh(e)).max().unwrap_or(0);
                let params_fresh = params
                    .iter()
                    .map(|p| match p {
                        ParamCst::Positive(positive) => {
                            let positive: Exp = positive.clone().into();
                            fresh(&positive)
                        }
                        ParamCst::Simple((v, a)) => std::cmp::max(fresh_var(v), fresh(a)),
                    })
                    .max()
                    .unwrap_or(0);
                std::cmp::max(end_fresh, params_fresh)
            };

            let mut pre_params: Vec<(Var, Exp)> = vec![];

            for p in params {
                match p {
                    ParamCst::Positive(positive) => {
                        let Positive {
                            variable: _,
                            parameter,
                            exps,
                        } = positive.clone();
                        let new_var_p: Var = {
                            usable_fresh_var += 1;
                            Var::Internal("elimtype".to_string(), usable_fresh_var)
                        };
                        let qmpx_type = {
                            let p_x = assoc_apply(
                                Exp::Var(new_var_p.clone()),
                                parameter.iter().map(|(x, _)| Exp::Var(x.clone())).collect(),
                            );
                            let q_m = assoc_apply(q.clone(), exps.clone());
                            let qmpx = Exp::App(Box::new(q_m), Box::new(p_x));
                            assoc_prod(parameter.clone(), qmpx)
                        };
                        pre_params.push((new_var_p.clone(), positive.clone().into()));
                        pre_params.push((Var::Unused, qmpx_type));
                        c = Exp::App(Box::new(c), Box::new(Exp::Var(new_var_p)));
                    }
                    ParamCst::Simple((x, a)) => {
                        pre_params.push((x.clone(), a.clone()));
                        c = Exp::App(Box::new(c), Box::new(Exp::Var(x.clone())));
                    }
                }
            }

            let res = Exp::App(Box::new(assoc_apply(q, end.1.to_owned())), Box::new(c));
            utils::assoc_prod(pre_params, res)
        }

        pub fn recursor(&self, ff: Exp, mut f: Exp) -> Exp {
            let Self { end, params } = self;

            let mut usable_fresh_var = {
                let end_fresh = end.1.iter().map(|e| fresh(e)).max().unwrap_or(0);
                let params_fresh = params
                    .iter()
                    .map(|p| match p {
                        ParamCst::Positive(positive) => {
                            let positive: Exp = positive.clone().into();
                            fresh(&positive)
                        }
                        ParamCst::Simple((v, a)) => std::cmp::max(fresh_var(v), fresh(a)),
                    })
                    .max()
                    .unwrap_or(0);
                std::cmp::max(end_fresh, params_fresh)
            };

            let mut pre_params: Vec<(Var, Exp)> = vec![];
            for p in params {
                match p {
                    ParamCst::Positive(positive) => {
                        let Positive {
                            variable: _,
                            parameter,
                            exps,
                        } = positive.clone();
                        let new_var_p = {
                            usable_fresh_var += 1;
                            Var::Internal("recursor".to_string(), usable_fresh_var)
                        };
                        let lam_ffmpx = {
                            let p_x = assoc_apply(
                                Exp::Var(new_var_p.clone()),
                                parameter.iter().map(|(x, _)| Exp::Var(x.clone())).collect(),
                            );
                            let f_m = assoc_apply(ff.clone(), exps.clone());
                            let fmpx = Exp::App(Box::new(f_m), Box::new(p_x));
                            assoc_lam(parameter.clone(), fmpx)
                        };
                        f = Exp::App(
                            Box::new(Exp::App(Box::new(f), Box::new(Exp::Var(new_var_p.clone())))),
                            Box::new(lam_ffmpx),
                        );
                        pre_params.push((new_var_p, positive.clone().into()));
                    }
                    ParamCst::Simple((x, a)) => {
                        f = Exp::App(Box::new(f), Box::new(Exp::Var(x.clone())));
                        pre_params.push((x.clone(), a.clone()));
                    }
                }
            }

            utils::assoc_lam(pre_params, f)
        }
    }

    impl IndTypeDefs {
        pub fn new(
            inddefs_syntax: crate::ast::inductives::InductiveDefinitionsSyntax,
        ) -> Result<Self, String> {
            let crate::ast::inductives::InductiveDefinitionsSyntax {
                name,
                variable,
                arity,
                constructors,
            } = inddefs_syntax;
            let arity = arity.into();
            let constructors = constructors
                .into_iter()
                .map(|(cname, c)| {
                    let (c, v) = ConstructorType::new_constructor(c, arity.clone())?;
                    Ok((cname, c))
                })
                .collect::<Result<Vec<(ConstructorName, ConstructorType)>, String>>()?;
            Ok(Self {
                name,
                variable,
                arity,
                constructors,
            })
        }
        pub fn name(&self) -> &TypeName {
            &self.name
        }
        pub fn variable(&self) -> &Var {
            &self.variable
        }
        pub fn arity(&self) -> &(Vec<(Var, Exp)>, Sort) {
            &self.arity
        }
        pub fn arity_as_exp(&self) -> Exp {
            let (vars, sort) = self.arity();
            assoc_prod(vars.clone(), sort.clone().into())
        }
        pub fn arg_of_type(&self) -> &Vec<(Var, Exp)> {
            &self.arity.0
        }
        pub fn sort(&self) -> Sort {
            self.arity.1
        }
        pub fn constructors(&self) -> &Vec<(ConstructorName, ConstructorType)> {
            &self.constructors
        }
        pub fn constructor(&self, constructor_name: &ConstructorName) -> Option<&ConstructorType> {
            self.constructors.iter().find_map(|(name, c)| {
                if name == constructor_name {
                    Some(c)
                } else {
                    None
                }
            })
        }
        pub fn constructor_as_exp(&self, constructor_name: &ConstructorName) -> Option<Exp> {
            self.constructors.iter().find_map(|(name, exp)| {
                if name == constructor_name {
                    Some(exp.clone().into())
                } else {
                    None
                }
            })
        }
        pub fn return_type(&self, sort: Sort) -> Exp {
            let arity = self.arity().clone();
            let vars = arity.0.iter().map(|(x, _)| Exp::Var(x.clone())).collect();
            let end = Exp::prod(
                Var::Unused,
                utils::assoc_apply(
                    Exp::IndTypeType {
                        ind_type_name: self.name().clone(),
                    },
                    vars,
                ),
                Exp::Sort(sort),
            );
            utils::assoc_prod(arity.0.clone(), end)
        }
        pub fn induction_scheme(&self, sort: Sort) -> Exp {
            let arity = self.arity().clone();
            // (x1: A1) -> ... -> (xn: An) -> (_: I x1 ... xn) -> s
            let return_type: Exp = {
                let vars = arity.0.iter().map(|(x, _)| Exp::Var(x.clone())).collect();
                let end = Exp::lambda(
                    Var::Unused,
                    utils::assoc_apply(
                        Exp::IndTypeType {
                            ind_type_name: self.name().clone(),
                        },
                        vars,
                    ),
                    Exp::Sort(sort),
                );
                utils::assoc_prod(arity.0.clone(), end)
            };
            let q_exp = Exp::Var("Q".into());
            // (fi: xi(I, Q, I::i, C_i)) -> ... ->
            let type_cases: Vec<(Var, Exp)> = {
                let mut v = vec![];
                for (cname, c) in self.constructors() {
                    // xi_X(Q, c, C[i])
                    let pre = c.eliminator_type(
                        q_exp.clone(),
                        Exp::IndTypeCst {
                            ind_type_name: self.name().clone(),
                            constructor_name: cname.clone(),
                        },
                    );
                    let exact = crate::lambda_calculus::subst(
                        pre,
                        self.variable(),
                        &Exp::IndTypeType {
                            ind_type_name: self.name().clone(),
                        },
                    );
                    v.push((cname.to_string().into(), exact));
                }
                v
            };
            // (x1: A1) -> ... -> (xn: An) -> (x: I x1... xn) -> Q x1 ... xn x
            let end: Exp = {
                let vars: Vec<Exp> = arity.0.iter().map(|(x, _)| Exp::Var(x.clone())).collect();
                let new_x: Var = "x".into();
                let end = Exp::lambda(
                    new_x.clone(),
                    utils::assoc_apply(
                        Exp::IndTypeType {
                            ind_type_name: self.name().clone(),
                        },
                        vars.clone(),
                    ),
                    utils::assoc_apply(
                        utils::assoc_apply(q_exp.clone(), vars),
                        vec![Exp::Var(new_x)],
                    ),
                );
                utils::assoc_prod(arity.0.clone(), end)
            };
            Exp::prod("Q".into(), return_type, utils::assoc_prod(type_cases, end))
        }
    }
}

use inductives::*;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GlobalContext {
    definitions: Vec<(Var, Exp, Exp)>,       // x := v
    parameters: Vec<(Var, Exp)>,             // x: t
    inductive_definitions: Vec<IndTypeDefs>, // inductive definitions
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResIndDefsError {
    AlreadyDefinedType,
    SyntaxError,
    ArityNotWellformed(DerivationFailed),
    ConstructorNotWellFormed(Vec<Result<PartialDerivationTreeTypeCheck, DerivationFailed>>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResIndDefsOk {
    pub arity_well_formed: PartialDerivationTreeTypeCheck,
    pub constructor_wellformed: Vec<PartialDerivationTreeTypeCheck>,
}

fn check_well_formedness_new_definition(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    x: Var,
    a: Exp,
    v: Exp,
) -> Result<PartialDerivationTreeTypeCheck, DerivationFailed> {
    match type_check(gcxt, cxt, v.clone(), a.clone()) {
        Ok(der_tree) => Ok(der_tree),
        Err(err) => Err(err),
    }
}

fn check_well_formedness_new_assmption(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    x: Var,
    a: Exp,
) -> Result<PartialDerivationTreeTypeCheck, DerivationFailed> {
    match type_infered_to_sort(gcxt, cxt, a.clone()) {
        Ok((der_tree, _)) => Ok(der_tree),
        Err(err) => Err(err),
    }
}

fn check_well_formednewss_new_inddefs(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    defs: IndTypeDefs,
) -> Result<ResIndDefsOk, ResIndDefsError> {
    if gcxt
        .inductive_definitions
        .iter()
        .any(|inddefs| inddefs.name() == defs.name())
    {
        return Err(ResIndDefsError::AlreadyDefinedType);
    }

    // arity の well defined
    let arity_well_formed =
        match type_infered_to_sort(gcxt, LocalContext::default(), defs.arity_as_exp()) {
            Ok((der_tree, _)) => der_tree,
            Err(err) => return Err(ResIndDefsError::ArityNotWellformed(err)),
        };

    let mut constructor_well_formed = vec![];
    let mut flag = true;

    // 各 constructor の well defined
    for (_, c) in defs.constructors() {
        let sort = defs.sort();
        let mut cxt = LocalContext::default();
        let (x, a) = (defs.variable().clone(), defs.arity_as_exp());
        cxt.push_decl((x, a));
        let constructor: Exp = c.clone().into();
        match type_check(gcxt, cxt, constructor, Exp::Sort(sort)) {
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
        Ok(ResIndDefsOk {
            arity_well_formed,
            constructor_wellformed: constructor_well_formed
                .into_iter()
                .map(|res| res.unwrap())
                .collect(),
        })
    }
}

impl GlobalContext {
    pub fn push_new_defs(&mut self, (x, a, v): (Var, Exp, Exp)) {}
    pub fn push_new_assum(&mut self, (x, a): (Var, Exp)) {}
    pub fn push_new_ind(&mut self, defs: inductives::IndTypeDefs) {}
    pub fn type_of_indtype(&self, ind_type_name: &TypeName) -> Option<Exp> {
        let indtype_def = self.indtype_defs(ind_type_name)?;
        Some(indtype_def.arity_as_exp())
    }
    pub fn type_of_cst(
        &self,
        ind_type_name: &TypeName,
        constructor_name: &ConstructorName,
    ) -> Option<Exp> {
        let defs = self.indtype_defs(ind_type_name)?;
        let constructor_def = defs.constructor(constructor_name)?;
        let constructor_exp: Exp = constructor_def.clone().into();
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ErrCases {
    pub case: String,
    pub successes: Vec<DerChild>,
    pub error: ErrInfo,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DerChild {
    PartialDerivationTree(PartialDerivationTreeTypeCheck),
    Condition(Condition),
    NeedProve(ProvableJudgement),
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

impl DerChild {
    pub fn get_goals(&self) -> Vec<ProvableJudgement> {
        match self {
            DerChild::PartialDerivationTree(partial_derivation_tree_type_check) => {
                partial_derivation_tree_type_check.get_goals()
            }
            DerChild::Condition(_) => vec![],
            DerChild::NeedProve(provable_judgement) => vec![provable_judgement.clone()],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartialDerivationTreeTypeCheck {
    pub head: TypeCheckJudgement,
    pub label: DerivationLabel,
    pub child: Vec<DerChild>,
    pub gen_and_case: (String, String),
    pub other_case: Vec<ErrCases>,
}

impl PartialDerivationTreeTypeCheck {
    pub fn get_goals(&self) -> Vec<ProvableJudgement> {
        let mut v = vec![];
        for der_child in &self.child {
            match der_child {
                DerChild::PartialDerivationTree(partial_derivation_tree_type_check) => {
                    v.extend(partial_derivation_tree_type_check.get_goals());
                }
                DerChild::Condition(_) => {}
                DerChild::NeedProve(provable_judgement) => {
                    v.push(provable_judgement.clone());
                }
            }
        }
        v
    }
}

impl PartialDerivationTreeTypeCheck {
    pub fn of_type(&self) -> &Exp {
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
    pub generated_info: String,
    pub err_cases: Vec<ErrCases>,
}

pub mod printing {
    use std::default;

    use super::*;
    use colored::Colorize;
    use termtree::Tree;

    #[derive(Debug, Clone, PartialEq, Eq)]
    enum Node {
        TypeCheckJudgement(TypeCheckJudgement),
        Label(DerivationLabel),
        ProvableJudgement(ProvableJudgement),
        Condition(Condition),
        Fail(FailHead),
        ErrCond(ErrOnCondition),
        ErrOther(String),
        ContextInfo(String),
    }

    #[derive(Debug, Clone, PartialEq, Eq, Default)]
    pub enum TreeConfig {
        #[default]
        OnlyGoals,
        SuccTree,
        AllCase,
    }

    fn error_string(s: String) -> String {
        format!("{}", s.red())
    }

    impl Display for Node {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let s: String = match self {
                Node::TypeCheckJudgement(type_check_judgement) => {
                    format!("{type_check_judgement}")
                }
                Node::Label(label) => format!("{label}"),
                Node::ProvableJudgement(provable_judgement) => {
                    format!("{}", format!("{provable_judgement}").green())
                }
                Node::Condition(condition) => format!("{condition}"),
                Node::Fail(fail_head) => match fail_head {
                    FailHead::InferFail(local_context, exp) => {
                        error_string(format!("!{local_context} |- {exp}: !"))
                    }
                    FailHead::CheckFail(type_check_judgement) => {
                        error_string(format!("{type_check_judgement}"))
                    }
                },
                Node::ErrCond(err) => error_string(err.err.clone()),
                Node::ErrOther(other) => error_string(other.clone()),
                Node::ContextInfo(extra_info) => format!("{extra_info:?}"),
            };
            write!(f, "{s}")
        }
    }

    fn node_to_tree(node: &DerChild, tree_config: &TreeConfig) -> Option<Tree<Node>> {
        match node {
            DerChild::PartialDerivationTree(partial_derivation_tree_type_check) => Some(
                tree_partial_derivation_tree(partial_derivation_tree_type_check, tree_config),
            ),
            DerChild::Condition(condition) => {
                if matches!(tree_config, TreeConfig::AllCase | TreeConfig::SuccTree) {
                    Some(Tree::new(Node::Condition(condition.clone())))
                } else {
                    None
                }
            }
            DerChild::NeedProve(provable_judgement) => Some(Tree::new(Node::ProvableJudgement(
                provable_judgement.clone(),
            ))),
        }
    }

    fn err_info(err_info: &ErrInfo, tree_config: &TreeConfig) -> Tree<Node> {
        match err_info {
            ErrInfo::Condition(err_on_condition) => {
                Tree::new(Node::ErrCond(err_on_condition.clone()))
            }
            ErrInfo::FailTree(derivation_failed) => tree_fail_tree(derivation_failed, tree_config),
            ErrInfo::Other(other) => Tree::new(Node::ErrOther(other.clone())),
        }
    }

    fn tree_err_case(err_case: &ErrCases, tree_config: &TreeConfig) -> Tree<Node> {
        let ErrCases {
            case,
            successes,
            error,
        } = err_case;
        let mut tree = Tree::new(Node::ContextInfo(format!("err info {case}")));

        tree.extend(
            successes
                .iter()
                .filter_map(|child| node_to_tree(child, tree_config)),
        );
        tree.push(err_info(error, tree_config));
        tree
    }

    fn tree_partial_derivation_tree(
        tree: &PartialDerivationTreeTypeCheck,
        tree_config: &TreeConfig,
    ) -> Tree<Node> {
        if *tree_config == TreeConfig::OnlyGoals {
            let mut show_tree = Tree::new(Node::TypeCheckJudgement(tree.head.clone()));
            show_tree.extend(
                tree.get_goals()
                    .into_iter()
                    .map(|goal| Node::ProvableJudgement(goal)),
            );
            return show_tree;
        }

        let PartialDerivationTreeTypeCheck {
            head,
            label,
            child,
            gen_and_case: (generated, case),
            other_case,
        } = tree;
        let mut tree = Tree::new(Node::TypeCheckJudgement(head.clone()));

        if matches!(tree_config, TreeConfig::SuccTree) {
            tree.push(Tree::new(Node::ContextInfo(format!(
                "generated {generated}, case {case}"
            ))));
            tree.push(Tree::new(Node::Label(label.clone())));
        }

        tree.extend(
            child
                .iter()
                .filter_map(|child| node_to_tree(child, tree_config)),
        );

        if matches!(tree_config, TreeConfig::AllCase) {
            tree.extend(
                other_case
                    .iter()
                    .map(|err_case| tree_err_case(err_case, tree_config)),
            );
        }
        tree
    }

    pub fn print_tree(tree: &PartialDerivationTreeTypeCheck, tree_config: &TreeConfig) -> String {
        tree_partial_derivation_tree(tree, tree_config).to_string()
    }

    fn tree_fail_tree(tree: &DerivationFailed, tree_config: &TreeConfig) -> Tree<Node> {
        let DerivationFailed {
            head,
            generated_info,
            err_cases,
        } = tree;
        let mut tree = Tree::new(Node::Fail(head.clone()));
        tree.push(Tree::new(Node::ContextInfo(generated_info.clone())));
        tree.extend(
            err_cases
                .iter()
                .map(|child| tree_err_case(child, tree_config)),
        );
        tree
    }

    pub fn print_fail_tree(tree: &DerivationFailed, tree_config: &TreeConfig) -> String {
        tree_fail_tree(tree, tree_config).to_string()
    }
}
