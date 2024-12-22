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
    IndTypeType {
        type_name: String,
        argument: Vec<Exp>,
    },
    IndTypeCst {
        type_name: String,
        projection: usize,
        argument: Vec<Exp>,
    },
    IndTypeElim {
        type_name: String,
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

pub mod utils {
    use super::*;
    pub fn assoc_apply(mut a: Exp, v: Vec<Exp>) -> Exp {
        for v in v {
            a = Exp::App(Box::new(a), Box::new(v))
        }
        a
    }

    pub fn assoc_prod(mut v: Vec<(Var, Exp)>, mut e: Exp) -> Exp {
        while let Some((x, a)) = v.pop() {
            e = Exp::Prod(x, Box::new(a), Box::new(e));
        }
        e
    }

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
        pub signature: Vec<(Var, Exp)>,
        pub sort: Sort,
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
    }

    impl From<Arity> for Exp {
        fn from(Arity { signature, sort }: Arity) -> Self {
            assoc_prod(signature, Exp::Sort(sort))
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct IndTypeDefs {
        pub variable: Var,
        pub signature: Arity,
        pub constructor: Vec<ConstructorType>,
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum ConstructorType {
        End(Var, Vec<Exp>), // X m1 ... mk
        Map((Var, Exp), Box<ConstructorType>),
        PosToCst(Positive, Box<ConstructorType>),
    }

    impl ConstructorType {
        pub fn eliminator_type(&self, q: Exp, c: Exp) -> Exp {
            match self {
                ConstructorType::End(x, a) => {
                    let v = assoc_apply(q, a.clone());
                    Exp::App(Box::new(v), Box::new(c))
                }
                ConstructorType::Map((x, a), m) => {
                    let b = Box::new(m.eliminator_type(q, c));
                    Exp::Prod(x.clone(), Box::new(a.clone()), b)
                }
                ConstructorType::PosToCst(p, n) => {
                    let new_var = Var::Str("new_cons".to_string()); // ちゃんとした変数をあとで作る
                    let Positive {
                        variable,
                        parameter,
                        exps,
                    } = p.clone();
                    let neg = n.eliminator_type(q.clone(), c.clone());
                    let pp = assoc_apply(
                        Exp::Var(new_var.clone()),
                        parameter.iter().map(|(x, e)| Exp::Var(x.clone())).collect(),
                    );
                    let q = assoc_apply(q.clone(), exps.clone());
                    let pos = assoc_prod(parameter.clone(), Exp::App(Box::new(q), Box::new(pp)));

                    Exp::Prod(
                        new_var,
                        Box::new(p.clone().into()),
                        Box::new(Exp::Prod(Var::Unused, Box::new(pos), Box::new(neg))),
                    )
                }
            }
        }

        pub fn recursor(&self, ff: Exp, f: Exp) -> Exp {
            match self {
                ConstructorType::End(_, _) => f,
                ConstructorType::Map((x, a), n) => {
                    Exp::Lam(x.clone(), Box::new(a.clone()), Box::new(n.recursor(ff, f)))
                }
                ConstructorType::PosToCst(p, n) => {
                    let new_var_p = Var::Str("new_cons".to_string()); // ちゃんとした変数をあとで作る
                    let Positive {
                        variable,
                        parameter,
                        exps,
                    } = p.clone();
                    let ff = {
                        let p = assoc_apply(
                            Exp::Var(new_var_p.clone()),
                            parameter.iter().map(|(x, _)| Exp::Var(x.clone())).collect(),
                        );
                        let ff = assoc_apply(ff, exps.clone());
                        Exp::App(Box::new(ff), Box::new(p))
                    };
                    let new_f = {
                        let u = assoc_lam(parameter.clone(), ff.clone());
                        let v = Exp::App(Box::new(f), Box::new(Exp::Var(new_var_p.clone())));
                        Exp::App(Box::new(v), Box::new(u))
                    };
                    let rec = n.recursor(ff, new_f);
                    Exp::Lam(new_var_p.clone(), Box::new(p.clone().into()), Box::new(rec))
                }
            }
        }
    }

    // variable = X, parameter = [(y_1, M_1), ..., (y_k, M_k)], exps = [N_1, ... N_l]
    // => (y_1: M_1) -> ... -> (y_k: M_k) -> (X N_1 ... N_l)
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Positive {
        pub parameter: Vec<(Var, Exp)>,
        pub variable: Var,
        pub exps: Vec<Exp>,
    }

    impl Positive {
        fn new(variable: Var, parameter: Vec<(Var, Exp)>, exps: Vec<Exp>) -> Result<Self, String> {
            if parameter
                .iter()
                .any(|(_, e)| e.free_variable().contains(&variable))
            {
                return Err(format!("{parameter:?} contains {variable:?}"));
            }
            Ok(Self {
                variable,
                parameter,
                exps,
            })
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
                type_name,
                argument,
            } => argument
                .iter()
                .map(|e| e.free_variable())
                .flatten()
                .collect(),
            Exp::IndTypeCst {
                type_name,
                projection: _,
                argument,
            } => argument
                .into_iter()
                .map(|e| e.free_variable())
                .flatten()
                .collect(),
            Exp::IndTypeElim {
                type_name,
                eliminated_exp,
                return_type,
                cases,
            } => cases
                .into_iter()
                .map(|e| e.free_variable())
                .flatten()
                .chain(eliminated_exp.free_variable())
                .chain(return_type.free_variable())
                .collect(),
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GlobalContext {
    inductive_definitions: HashMap<String, (Vec<String>, inductives::IndTypeDefs)>,
}

impl GlobalContext {
    pub fn indtype_defs(&self, type_name: &str) -> Option<&inductives::IndTypeDefs> {
        self.inductive_definitions.get(type_name).map(|s| &s.1)
    }
    pub fn indtype_constructor(&self, type_name: &str, constructor_name: &str) -> Option<usize> {
        let (cs, _) = self.inductive_definitions.get(type_name)?;
        cs.iter().position(|c_name| c_name == constructor_name)
    }
}
