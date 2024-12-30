use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

pub mod parse;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Exp {
    Sort(Sort),
    Var(Var),
    Prod(Var, Box<Exp>, Box<Exp>),
    Lam(Var, Box<Exp>, Box<Exp>),
    App(Box<Exp>, Box<Exp>),
    // inductive hoge は global context を見ながらやること
    // T m[0] ... m[k]
    IndTypeType {
        ind_type_name: String,
        argument: Vec<Exp>,
    },
    // T[i] a[0] ... a[l]
    IndTypeCst {
        ind_type_name: String,
        constructor_name: String,
        argument: Vec<Exp>,
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

impl Exp {
    pub fn pretty_print(&self) -> String {
        match self {
            Exp::Sort(sort) => format!("{sort}"),
            Exp::Var(var) => format!("{var}"),
            Exp::Prod(var, exp, exp1) => {
                format!("({var}: {}) -> {}", exp.pretty_print(), exp1.pretty_print())
            }
            Exp::Lam(var, exp, exp1) => {
                format!("\\({var}: {}). {}", exp.pretty_print(), exp1.pretty_print())
            }
            Exp::App(exp, exp1) => {
                format!("{} {}", exp.pretty_print(), exp1.pretty_print())
            }
            Exp::IndTypeType {
                ind_type_name,
                argument,
            } => format!(
                "{ind_type_name}({})",
                argument
                    .iter()
                    .fold(String::new(), |s, e| format!("{s} {}", e.pretty_print()))
            ),
            Exp::IndTypeCst {
                ind_type_name,
                constructor_name,
                argument,
            } => format!(
                "{ind_type_name}::{constructor_name}({})",
                argument
                    .iter()
                    .fold(String::new(), |s, e| format!("{s} {}", e.pretty_print()))
            ),
            Exp::IndTypeElim {
                ind_type_name,
                eliminated_exp,
                return_type,
                cases,
            } => format!(
                "Elim[{ind_type_name}] {} return {} ({})",
                eliminated_exp.pretty_print(),
                return_type.pretty_print(),
                cases.iter().fold(String::new(), |s, e| {
                    format!("{s} {}", e.pretty_print())
                }),
            ),
        }
    }
    pub fn prod(var: Var, a: Exp, b: Exp) -> Self {
        Exp::Prod(var, Box::new(a), Box::new(b))
    }
    pub fn lambda(var: Var, a: Exp, b: Exp) -> Self {
        Exp::Lam(var, Box::new(a), Box::new(b))
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
                Var::Str(s) => s.as_str(),
                Var::Internal(s, _) => s.as_str(),
                Var::Unused => "_",
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
        pub fn arity(&self) -> &Arity {
            &self.arity
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

    impl From<ConstructorType> for Exp {
        fn from(value: ConstructorType) -> Self {
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

    impl ConstructorType {
        pub fn new_constructor(
            end: (Var, Vec<Exp>),
            params: Vec<ParamCst>,
        ) -> Result<(Self, Var), String> {
            let var_type = end.0.clone();
            let mut allow = vec![];
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
                                parameter.iter().map(|(x, e)| Exp::Var(x.clone())).collect(),
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
                                parameter.iter().map(|(x, e)| Exp::Var(x.clone())).collect(),
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
            Exp::IndTypeType {
                argument,
                ind_type_name: _,
            } => argument.iter().flat_map(|e| e.free_variable()).collect(),
            Exp::IndTypeCst {
                ind_type_name: _,
                constructor_name: _,
                argument,
            } => argument.iter().flat_map(|e| e.free_variable()).collect(),
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
        if self.inductive_definitions.contains_key(&type_name) {
            return Err(format!("already defined {type_name}"));
        }
        self.inductive_definitions
            .insert(type_name, (constructors, defs));
        Ok(())
    }
    pub fn push_new_decl(&mut self, (v, a): (Var, Exp)) -> Result<(), String> {
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
