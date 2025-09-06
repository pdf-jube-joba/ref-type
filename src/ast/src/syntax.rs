use std::fmt::Display;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Exp {
    Sort(Sort),
    Var(Var),
    Prod(Bind, Box<Exp>),
    Lam(Bind, Box<Exp>),
    App(Box<Exp>, Box<Exp>),
    // inductive hoge は global context を見ながらやること
    // 型 T
    IndType {
        ind_type_name: inductives::TypeName,
    },
    // 型 T のコンストラクタ C の指定
    IndCst {
        ind_type_name: inductives::TypeName,
        constructor_name: inductives::ConstructorName,
    },
    // Elim(T, c, Q){f[0], ..., f[m]}
    IndTypeElim {
        ind_type_name: inductives::TypeName,
        eliminated_exp: Box<Exp>,
        return_type: Box<Exp>,
        cases: Vec<(inductives::ConstructorName, Exp)>,
    },
    // これがほしいメインの部分
    Proof(Box<Exp>),                    // Proof t
    Pow(Box<Exp>),                      // Power X
    Sub(Bind, Box<Exp>),                // { x : A | P }
    Pred(Box<Exp>, Box<Exp>, Box<Exp>), // Pred (A, B, t)
    Id(Box<Exp>, Box<Exp>),             // a = b
    Exists(Box<Exp>),                   // exists T.
    Take(Bind, Box<Exp>),               // take x:A. t
}

impl Display for Exp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: String = match self {
            Exp::Sort(sort) => format!("{sort}"),
            Exp::Var(var) => format!("{var}"),
            Exp::Prod(bind, exp1) => format!("({bind}) -> {exp1}"),
            Exp::Lam(bind, exp1) => format!("({bind}) |-> {exp1}"),
            Exp::App(exp, exp1) => format!("{{{exp}}} {{{exp1}}}"),
            Exp::IndType { ind_type_name } => ind_type_name.to_string(),
            Exp::IndCst {
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
                    "elim({ind_type_name}) {eliminated_exp} return {return_type} with {} end",
                    cases
                        .iter()
                        .fold(String::new(), |s, (c, e)| { format!("{s} | {c} => {e} ") }),
                )
            }
            Exp::Proof(t) => format!("Proof({t})"),
            Exp::Sub(bind, p) => format!("{{ {bind} | {p} }}"),
            Exp::Pow(a) => format!("Power({a})"),
            Exp::Pred(a, b, t) => format!("Pred({a}, {b}, {t})"),
            Exp::Id(a, b) => format!("({a} = {b})"),
            Exp::Exists(t) => format!("Exists {t}"),
            Exp::Take(bind, m) => format!("Take ({bind}) |-> {m}"),
        };
        write!(f, "{}", s)
    }
}

impl Exp {
    pub fn is_sort(&self) -> Option<Sort> {
        if let Exp::Sort(s) = self {
            Some(*s)
        } else {
            None
        }
    }
    pub fn indelim(
        ind_type_name: String,
        eliminated_exp: Exp,
        return_type: Exp,
        cases: Vec<(String, Exp)>,
    ) -> Self {
        Self::IndTypeElim {
            ind_type_name: ind_type_name.into(),
            eliminated_exp: Box::new(eliminated_exp),
            return_type: Box::new(return_type),
            cases: cases.into_iter().map(|(c, e)| (c.into(), e)).collect(),
        }
    }
}

// occurence of bind (x: A)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bind {
    pub var: Var,
    pub ty: Box<Exp>,
}

impl Bind {
    pub fn new(x: Var, a: Exp) -> Self {
        Bind {
            var: x,
            ty: Box::new(a),
        }
    }
}

impl Display for Bind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.var, self.ty)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Var {
    Str(String),
    Internal(String, usize),
    Unused,
}

// pub fn fresh_var(v: &Var) -> usize {
//     match v {
//         Var::Str(_) => 0,
//         Var::Internal(_, i) => *i + 1,
//         Var::Unused => 0,
//     }
// }

// // term に含まれるどの変数よりも大きい数を返す
// pub fn fresh(term: &Exp) -> usize {
//     match term {
//         Exp::Sort(_) => 0,
//         Exp::Var(v) => fresh_var(v),
//         Exp::Prod(x, t1, t2) => {
//             let v1 = fresh(t1);
//             let v2 = fresh(t2);
//             let v = std::cmp::max(v1, v2);
//             std::cmp::max(fresh_var(x), v)
//         }
//         Exp::Lam(x, t1, t2) => {
//             let v1 = fresh(t1);
//             let v2 = fresh(t2);
//             let v = std::cmp::max(v1, v2);
//             std::cmp::max(fresh_var(x), v)
//         }
//         Exp::App(t1, t2) => {
//             let v1 = fresh(t1);
//             let v2 = fresh(t2);
//             std::cmp::max(v1, v2)
//         }
//         Exp::IndType { ind_type_name: _ } => 0,
//         Exp::IndCst {
//             ind_type_name: _,
//             constructor_name: _,
//         } => 0,
//         Exp::IndTypeElim {
//             ind_type_name: _,
//             eliminated_exp,
//             return_type,
//             cases,
//         } => cases
//             .iter()
//             .map(|(_, e)| e)
//             .chain(vec![eliminated_exp.as_ref(), return_type.as_ref()])
//             .map(fresh)
//             .max()
//             .unwrap(),
//         Exp::Proof(t) => fresh(t),
//         Exp::Sub(x, t1, t2) => {
//             let v1 = fresh(t1);
//             let v2 = fresh(t2);
//             let v = std::cmp::max(v1, v2);
//             std::cmp::max(fresh_var(x), v)
//         }
//         Exp::Pow(t) => fresh(t),
//         Exp::Pred(a, b, t) => std::cmp::max(std::cmp::max(fresh(a), fresh(b)), fresh(t)),
//         Exp::Id(exp1, exp2) => std::cmp::max(fresh(exp1), fresh(exp2)),
//         Exp::Exists(exp) => fresh(exp),
//         Exp::Take(var, exp, exp1) => {
//             std::cmp::max(fresh_var(var), std::cmp::max(fresh(exp), fresh(exp1)))
//         }
//     }
// }

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
                Var::Str(s) => format!("[{s}]"),
                Var::Internal(s, n) => format!("[{s}_{n}]"),
                Var::Unused => "_".to_string(),
            }
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Sort {
    Set(usize),  // predicateive SET(0): SET(1): SET(2) ...
    Prop,        // proposition
    Univ(usize), // Prop: Univ(0): Univ(1): Univ(2) ...,
    Type,        // for programming language
}

impl Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Sort::Univ(i) => format!("UNIV({i})"),
            Sort::Set(i) => format!("SET({i})"),
            Sort::Prop => "PROP".to_string(),
            Sort::Type => "TYPE".to_string(),
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
    pub fn type_of_sort(self) -> Self {
        match self {
            Sort::Univ(i) => Sort::Univ(i + 1),
            Sort::Set(i) => Sort::Set(i + 1),
            Sort::Prop => Sort::Univ(0),
            Sort::Type => Sort::Univ(0),
        }
    }

    // functional なので、
    // (s1, s2, s3) in R な s3 は (s1, s2) に対して一意 ... それを返す。
    pub fn relation_of_sort(self, other: Self) -> Option<Self> {
        match (self, other) {
            // CoC 部分
            (Sort::Prop, Sort::Prop) => Some(Sort::Prop),
            (Sort::Univ(i1), Sort::Univ(i2)) => Some(Sort::Univ(std::cmp::max(i1, i2))),
            (Sort::Univ(_), Sort::Prop) => Some(Sort::Prop),
            (Sort::Prop, Sort::Univ(i)) => Some(Sort::Univ(i)),
            // Set を入れる部分
            (Sort::Set(i), Sort::Set(j)) => Some(Sort::Set(std::cmp::max(i, j))),
            (Sort::Set(_), Sort::Univ(i)) => Some(Sort::Univ(i)),
            (Sort::Set(_), Sort::Prop) => Some(Sort::Prop),
            (Sort::Prop, Sort::Set(_)) => None,
            (Sort::Univ(_), Sort::Set(_)) => None, // Set は predicative
            // Type を入れる部分
            (Sort::Type, Sort::Type) => Some(Sort::Type),
            (Sort::Type, Sort::Univ(i)) => Some(Sort::Univ(i)),
            (Sort::Univ(_), Sort::Type) => Some(Sort::Type),
            (Sort::Type, _) => None,
            (_, Sort::Type) => None,
            // Univ 用
        }
    }

    // elimination の制限用
    pub fn ind_type_rel(self, other: Self) -> Option<()> {
        match (self, other) {
            (Sort::Univ(_) | Sort::Set(_) | Sort::Type | Sort::Prop, Sort::Prop) => Some(()),
            (Sort::Set(_) | Sort::Type, Sort::Univ(_)) => Some(()),
            (Sort::Univ(i1), Sort::Univ(i2)) if i1 == i2 => Some(()),
            (Sort::Univ(_) | Sort::Type, Sort::Type) => Some(()),
            (Sort::Set(_), Sort::Set(_)) => Some(()),
            _ => None,
        }
    }
}

// inductive definition には自由変数がないことを仮定する
pub mod inductives {
    use super::*;

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct TypeName(String);

    impl<S> From<S> for TypeName
    where
        S: AsRef<str>,
    {
        fn from(value: S) -> Self {
            TypeName(value.as_ref().to_string())
        }
    }

    impl Display for TypeName {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.0)
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct ConstructorName(String);

    impl<S> From<S> for ConstructorName
    where
        S: AsRef<str>,
    {
        fn from(value: S) -> Self {
            ConstructorName(value.as_ref().to_string())
        }
    }

    impl Display for ConstructorName {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.0)
        }
    }

    use crate::utils;

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct InductiveDefinitionsSyntax {
        pub parameter: Vec<(Var, Exp)>,
        pub type_name: String,
        pub arity: (Vec<(Var, Exp)>, Sort),
        pub constructors: Vec<(String, Vec<ParamCstSyntax>, Vec<Exp>)>,
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum ParamCstSyntax {
        Positive((Vec<(Var, Exp)>, Vec<Exp>)),
        Simple((Var, Exp)),
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Arity {
        pub signature: Vec<(Var, Exp)>,
        pub sort: Sort,
    }

    impl Arity {
        pub fn new(signature: Vec<(Var, Exp)>, sort: Sort) -> Result<Self, String> {
            let arity = Arity { signature, sort };
            Ok(arity)
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
            utils::assoc_prod(signature, Exp::Sort(sort))
        }
    }

    impl Display for InductiveDefinitionsSyntax {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let InductiveDefinitionsSyntax {
                parameter,
                type_name,
                arity,
                constructors,
            } = self;
            writeln!(f, "name: {type_name}")?;
            writeln!(
                f,
                "parameter: {}",
                parameter
                    .iter()
                    .map(|(x, a)| format!("({x}: {a}) "))
                    .collect::<String>()
            )?;
            writeln!(
                f,
                "arity: {}",
                utils::assoc_prod(arity.0.clone(), arity.1.into())
            )?;
            for (csname, params, end) in constructors {
                write!(f, "constructor({csname}):")?;
                for param in params {
                    write!(f, " {} ->", param)?;
                }
                writeln!(
                    f,
                    " {}",
                    utils::assoc_apply(end[0].clone(), end[1..].to_owned())
                )?;
            }
            Ok(())
        }
    }

    impl Display for ParamCstSyntax {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let s = match self {
                ParamCstSyntax::Positive((params, end)) => {
                    format!(
                        "Pos({})",
                        utils::assoc_prod(
                            params.clone(),
                            utils::assoc_apply(end[0].clone(), end[1..].to_owned())
                        )
                    )
                }
                ParamCstSyntax::Simple(param) => {
                    format!("Sim({}: {})", param.0, param.1)
                }
            };
            write!(f, "{}", s)
        }
    }
}
