use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

use crate::relation::subst;

pub mod parse;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Exp {
    Sort(Sort),
    Var(Var),
    Prod(Var, Box<Exp>, Box<Exp>),
    Lam(Var, Box<Exp>, Box<Exp>),
    App(Box<Exp>, Box<Exp>),
    // inductive hoge は global context を見ながらやること
    // 型 T
    IndTypeType {
        ind_type_name: String,
    },
    // 型 T のコンストラクタ C の指定
    IndTypeCst {
        ind_type_name: String,
        constructor_name: String,
    },
    // Elim(T, c, Q){f[0], ..., f[m]}
    IndTypeElim {
        ind_type_name: String,
        eliminated_exp: Box<Exp>,
        return_type: Box<Exp>,
        cases: Vec<Exp>,
    },
    // これがほしいメインの部分
    // Proof(Box<Exp>), // Proof t
    // Id(Box<Exp>, Box<Exp>, Box<Exp>) // a =_A b
    // Refl(Box<Exp>, Box<Exp>) // refl_A a
    // Sub(Var, Box<Exp>, Box<Exp>), // { x : A | P }
    // Pow(Box<Exp>), // Power X
    // Pred(Box<Exp>, Box<Exp>), // Pred X
    // Take(Var, Box<Exp>, Box<Exp>), // take x:A. t
    // Rec(Var, Var, Box<Exp>), // rec f x = m
}

impl Display for Exp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: String = match self {
            Exp::Sort(sort) => format!("{sort}"),
            Exp::Var(var) => format!("{var}"),
            Exp::Prod(var, exp, exp1) => format!("({var}:{exp}) -> {exp1}"),
            Exp::Lam(var, exp, exp1) => format!("\\{var}:{exp}. {exp1}"),
            Exp::App(exp, exp1) => format!("({exp} {exp1})"),
            Exp::IndTypeType { ind_type_name } => ind_type_name.to_string(),
            Exp::IndTypeCst {
                ind_type_name,
                constructor_name,
            } => format!("{ind_type_name}::{constructor_name}"),
            Exp::IndTypeElim {
                ind_type_name,
                eliminated_exp,
                return_type,
                cases,
            } => {
                format!(
                    "elim({ind_type_name}) {eliminated_exp} return {return_type} with ({})",
                    cases
                        .iter()
                        .fold(String::new(), |s, e| { format!("{s} {e}") }),
                )
            }
        };
        write!(f, "{}", s)
    }
}

impl Exp {
    pub fn prod(var: Var, a: Exp, b: Exp) -> Self {
        Exp::Prod(var, Box::new(a), Box::new(b))
    }
    pub fn lambda(var: Var, a: Exp, b: Exp) -> Self {
        Exp::Lam(var, Box::new(a), Box::new(b))
    }
    pub fn indtype(gcxt: &GlobalContext, type_name: String) -> Result<Self, String> {
        if gcxt.indtype_defs(&type_name).is_none() {
            return Err(format!("type {type_name} is not found"));
        };
        Ok(Self::IndTypeType {
            ind_type_name: type_name,
        })
    }
    pub fn indcst(
        gcxt: &GlobalContext,
        type_name: String,
        cst_name: String,
    ) -> Result<Self, String> {
        if gcxt.indtype_defs(&type_name).is_none() {
            return Err(format!("type {type_name} is not found"));
        };
        if gcxt.indtype_constructor(&type_name, &cst_name).is_none() {
            return Err(format!("constructor {type_name} {cst_name} is not found"));
        };
        Ok(Self::IndTypeCst {
            ind_type_name: type_name,
            constructor_name: cst_name,
        })
    }
    pub fn indelim(
        gcxt: &GlobalContext,
        ind_type_name: String,
        eliminated_exp: Exp,
        return_type: Exp,
        cases: Vec<Exp>,
    ) -> Result<Self, String> {
        let Some(type_def) = gcxt.indtype_defs(&ind_type_name) else {
            return Err(format!("type {ind_type_name} is not found"));
        };
        if type_def.constructors().len() != cases.len() {
            return Err(format!("elim case num is diff {}", cases.len()));
        }
        Ok(Self::IndTypeElim {
            ind_type_name,
            eliminated_exp: Box::new(eliminated_exp),
            return_type: Box::new(return_type),
            cases,
        })
    }
}

pub mod utils {
    use super::*;
    // (a v[0] ... v[k])
    pub fn assoc_apply(mut a: Exp, v: Vec<Exp>) -> Exp {
        for v in v {
            a = Exp::App(Box::new(a), Box::new(v))
        }
        a
    }

    // (x[0]: t[0]) -> ... (x[k]: t[k]) -> e
    pub fn assoc_prod(mut v: Vec<(Var, Exp)>, mut e: Exp) -> Exp {
        while let Some((x, a)) = v.pop() {
            e = Exp::Prod(x, Box::new(a), Box::new(e));
        }
        e
    }

    // \ x[0]: t[0]). ... (x[k]: t[k]). e
    pub fn assoc_lam(mut v: Vec<(Var, Exp)>, mut e: Exp) -> Exp {
        while let Some((x, a)) = v.pop() {
            e = Exp::Lam(x, Box::new(a), Box::new(e));
        }
        e
    }

    pub fn decompose_to_app_exps(mut e: Exp) -> Vec<Exp> {
        let mut v = vec![];
        while let Exp::App(t1, t2) = e {
            v.push(*t2);
            e = *t1;
        }
        v.push(e);
        v.reverse();
        v
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Var {
    Str(String),
    Internal(String, usize),
    Unused,
}

pub fn fresh_var(v: &Var) -> usize {
    match v {
        Var::Str(_) => 0,
        Var::Internal(_, i) => *i + 1,
        Var::Unused => 0,
    }
}

// term に含まれるどの変数よりも大きい数を返す
pub fn fresh(term: &Exp) -> usize {
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

impl<S> From<S> for Var
where
    S: AsRef<str>,
{
    fn from(value: S) -> Self {
        Var::Str(value.as_ref().to_string())
    }
}

impl From<Var> for Exp {
    fn from(value: Var) -> Self {
        Exp::Var(value)
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Var::Str(s) => s.to_string(),
                Var::Internal(s, n) => format!("{s}_{n}"),
                Var::Unused => "_".to_string(),
            }
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Sort {
    Set,
    Type,
    Prop,
    // Program, // for computation
}

impl Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Sort::Set => "SORT",
            Sort::Type => "TYPE",
            Sort::Prop => "PROP",
        };
        write!(f, "{}", s)
    }
}

impl From<Sort> for Exp {
    fn from(value: Sort) -> Self {
        Exp::Sort(value)
    }
}

// functional なものしか考えないのでよい。
impl Sort {
    // functional なので、
    // (s1, s2) in A な s2 は s1 に対して一意 ... それを返す。
    pub fn type_of_sort(self) -> Option<Self> {
        if matches!(self, Sort::Prop | Sort::Set) {
            Some(Sort::Type)
        } else {
            None
        }
    }

    // functional なので、
    // (s1, s2, s3) in R な s3 は (s1, s2) に対して一意 ... それを返す。
    pub fn relation_of_sort(self, other: Self) -> Option<Self> {
        match (self, other) {
            // CoC 部分
            (Sort::Prop, Sort::Prop) => Some(Sort::Prop),
            (Sort::Type, Sort::Type) => Some(Sort::Type),
            (Sort::Type, Sort::Prop) => Some(Sort::Prop),
            (Sort::Prop, Sort::Type) => Some(Sort::Type),
            // Set を入れる分
            (Sort::Set, Sort::Set) => Some(Sort::Set),
            (Sort::Set, Sort::Type) => Some(Sort::Type),
            (Sort::Set, Sort::Prop) => Some(Sort::Prop),
            (Sort::Prop, Sort::Set) => None,
            (Sort::Type, Sort::Set) => None, // Set は predicative
        }
    }

    // elimination の制限用
    pub fn ind_type_rel(self, other: Self) -> Option<()> {
        match (self, other) {
            (Sort::Prop, Sort::Prop) => Some(()),

            _ => None,
        }
    }
}

// inductive definition には自由変数がないことを仮定する
pub mod inductives {
    use super::{utils::*, *};

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Arity {
        signature: Vec<(Var, Exp)>,
        sort: Sort,
    }

    impl Arity {
        pub fn new(signature: Vec<(Var, Exp)>, sort: Sort) -> Result<Self, String> {
            let arity = Arity { signature, sort };
            let as_exp: Exp = arity.clone().into();
            if as_exp.free_variable().is_empty() {
                Ok(arity)
            } else {
                Err(format!("arity {arity:?} contains free variables"))
            }
        }
        pub fn signature(&self) -> &Vec<(Var, Exp)> {
            &self.signature
        }
        pub fn sort(&self) -> &Sort {
            &self.sort
        }
        pub fn arg_num(&self) -> usize {
            self.signature.len()
        }
    }

    impl From<Arity> for Exp {
        fn from(Arity { signature, sort }: Arity) -> Self {
            assoc_prod(signature, Exp::Sort(sort))
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct IndTypeDefs {
        variable: Var,
        arity: Arity,
        constructor: Vec<ConstructorType>,
    }

    impl IndTypeDefs {
        pub fn new(
            variable: Var,
            (signature, sort): (Vec<(Var, Exp)>, Sort),
            constructor: Vec<ConstructorType>,
        ) -> Result<Self, String> {
            let arity = Arity::new(signature, sort)?;
            Ok(Self {
                variable,
                arity,
                constructor,
            })
        }
        pub fn variable(&self) -> &Var {
            &self.variable
        }
        pub fn arity(&self) -> &Arity {
            &self.arity
        }
        pub fn constructors(&self) -> &Vec<ConstructorType> {
            &self.constructor
        }
        pub fn constructor(&self, i: usize) -> Option<&ConstructorType> {
            self.constructor.get(i)
        }
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
            let mut allow = vec![var_type.clone()];
            for p in &params {
                match p {
                    ParamCst::Positive(positive) => {
                        if positive.variable != var_type {
                            return Err(format!("pos {positive:?} is not of type {var_type:?}"));
                        }
                        let e: Exp = positive.clone().into();
                        for vfree in e.free_variable() {
                            if !allow.contains(&vfree) {
                                return Err(format!("pos {positive:?} contains free variable"));
                            }
                        }
                    }
                    ParamCst::Simple((x, a)) => {
                        for vfree in a.free_variable() {
                            if !allow.contains(&vfree) {
                                return Err(format!(
                                    "simple ({x:?}: {a:?}) contains free variable"
                                ));
                            }
                            allow.push(x.clone());
                        }
                    }
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

    // variable = X, parameter = [(y_1, M_1), ..., (y_k, M_k)], exps = [N_1, ... N_l]
    // => (y_1: M_1) -> ... -> (y_k: M_k) -> (X N_1 ... N_l)
    // free variable of Pos is only X
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Positive {
        parameter: Vec<(Var, Exp)>,
        variable: Var,
        exps: Vec<Exp>,
    }

    impl Positive {
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

            let mut pre_params: Vec<(Var, Exp)> = vec![];

            for p in params {
                match p {
                    ParamCst::Positive(positive) => {
                        let Positive {
                            variable: _,
                            parameter,
                            exps,
                        } = positive.clone();
                        let new_var_p = Var::Str("new_cons".to_string()); // ちゃんとした変数をあとで作る
                        let qmpx_type = {
                            let p_x = assoc_apply(
                                Exp::Var(new_var_p.clone()),
                                parameter.iter().map(|(x, _)| Exp::Var(x.clone())).collect(),
                            );
                            let q_m = assoc_apply(q.clone(), exps.clone());
                            let qmpx = Exp::App(Box::new(q_m), Box::new(p_x));
                            assoc_prod(parameter.clone(), qmpx)
                        };
                        pre_params.push((Var::Unused, qmpx_type));
                        pre_params.push((new_var_p, positive.clone().into()));
                    }
                    ParamCst::Simple((x, a)) => {
                        pre_params.push((x.clone(), a.clone()));
                        c = Exp::App(Box::new(c), Box::new(Exp::Var(x.clone())));
                    }
                }
            }

            let mut res = Exp::App(Box::new(assoc_apply(q, end.1.to_owned())), Box::new(c));
            for (x, a) in pre_params {
                res = Exp::prod(x, a, res)
            }

            res
        }

        pub fn recursor(&self, ff: Exp, mut f: Exp) -> Exp {
            let Self { end: _, params } = self;
            let mut pre_params: Vec<(Var, Exp)> = vec![];
            for p in params {
                match p {
                    ParamCst::Positive(positive) => {
                        let Positive {
                            variable: _,
                            parameter,
                            exps,
                        } = positive.clone();
                        let new_var_p = Var::Str("new_cons".to_string()); // ちゃんとした変数をあとで作る
                        let ffmpx_lam = {
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
                            Box::new(ffmpx_lam),
                        );
                        pre_params.push((new_var_p, positive.clone().into()));
                    }
                    ParamCst::Simple((x, a)) => {
                        f = Exp::App(Box::new(f), Box::new(Exp::Var(x.clone())));
                        pre_params.push((x.clone(), a.clone()));
                    }
                }
            }

            for (x, a) in pre_params {
                f = Exp::Lam(x, Box::new(a), Box::new(f))
            }

            f
        }
    }
}

impl Exp {
    pub fn free_variable(&self) -> HashSet<Var> {
        match self {
            Exp::Sort(_) => HashSet::new(),
            Exp::Var(v) => vec![v.clone()].into_iter().collect(),
            Exp::Prod(x, a, b) => {
                let mut v = b.free_variable();
                v.remove(x);
                v.extend(a.free_variable());
                v
            }
            Exp::Lam(x, a, b) => {
                let mut v = b.free_variable();
                v.remove(x);
                v.extend(a.free_variable());
                v
            }
            Exp::App(e1, e2) => {
                let mut v = e1.free_variable();
                v.extend(e2.free_variable());
                v
            }
            Exp::IndTypeType { ind_type_name: _ } => HashSet::new(),
            Exp::IndTypeCst {
                ind_type_name: _,
                constructor_name: _,
            } => HashSet::new(),
            Exp::IndTypeElim {
                ind_type_name: _,
                eliminated_exp,
                return_type,
                cases,
            } => cases
                .iter()
                .flat_map(|e| e.free_variable())
                .chain(eliminated_exp.free_variable())
                .chain(return_type.free_variable())
                .collect(),
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GlobalContext {
    definitions: Vec<(Var, Exp, Exp)>, // x := v
    parameters: Vec<(Var, Exp)>,       // x: t
    inductive_definitions: HashMap<String, (Vec<String>, inductives::IndTypeDefs)>, //
}

impl GlobalContext {
    pub fn push_newind(
        &mut self,
        type_name: String,
        constructors: Vec<String>,
        defs: inductives::IndTypeDefs,
    ) -> Result<(), String> {
        use crate::relation::{type_check, type_infered_to_sort, Context, StatePartialTree};
        if self.inductive_definitions.contains_key(&type_name) {
            return Err(format!("already defined {type_name}"));
        }

        // arity の well defined
        let arity_exp: Exp = defs.arity().clone().into();
        let check = type_infered_to_sort(self, Context::default(), arity_exp);
        if check.1.is_none() {
            return Err(format!(
                "arity {:?} is not well formed \n{}",
                defs.arity(),
                check.0.pretty_print(0),
            ));
        }

        // 各 constructor の well defined
        for c in defs.constructors() {
            let sort = *defs.arity().sort();
            let mut cxt = Context::default();
            let (x, a) = (defs.variable().clone(), defs.arity().clone().into());
            cxt.push_decl((x, a));
            let constructor: Exp = c.clone().into();
            let check = type_check(self, cxt, constructor, Exp::Sort(sort));
            if check.result_of_tree() == StatePartialTree::Fail {
                return Err(format!(
                    "constructor {:?} is nor well formed \n{}",
                    c,
                    check.pretty_print(0),
                ));
            }
        }

        self.inductive_definitions
            .insert(type_name, (constructors, defs));
        Ok(())
    }
    pub fn type_of_indtype(&self, type_name: &str) -> Option<Exp> {
        let indtype_def = self.indtype_defs(type_name)?;
        let arity = indtype_def.arity().clone();
        Some(arity.into())
    }
    pub fn type_of_cst(&self, type_name: &str, constructor_name: &str) -> Option<Exp> {
        let constructor_def = self.indtype_constructor(type_name, constructor_name)?.1;
        let constructor_exp: Exp = constructor_def.clone().into();
        let constructor_exp = subst(
            constructor_exp,
            constructor_def.variable(),
            &Exp::IndTypeType {
                ind_type_name: type_name.to_string(),
            },
        );
        Some(constructor_exp)
    }
    pub fn name_of_cst(&self, type_name: &str, i: usize) -> Option<&String> {
        let a = self.inductive_definitions.get(type_name)?;
        a.0.get(i)
    }
    pub fn push_new_defs(&mut self, (x, a, t): (Var, Exp, Exp)) -> Result<(), String> {
        todo!()
    }
    pub fn push_new_assum(&mut self, (v, a): (Var, Exp)) -> Result<(), String> {
        todo!()
    }
    pub fn indtype_defs(&self, type_name: &str) -> Option<&inductives::IndTypeDefs> {
        self.inductive_definitions.get(type_name).map(|s| &s.1)
    }
    pub fn indtype_constructor(
        &self,
        type_name: &str,
        constructor_name: &str,
    ) -> Option<(usize, &inductives::ConstructorType)> {
        let (cs_name, cs) = self.inductive_definitions.get(type_name)?;
        let i = cs_name
            .iter()
            .position(|c_name| c_name == constructor_name)?;
        Some((i, cs.constructor(i)?))
    }
}
