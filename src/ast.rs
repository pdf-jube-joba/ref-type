use std::fmt::Display;

pub mod parse;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Var {
    Str(String),
    Internal(String, usize),
}

impl<S> From<S> for Var
where
    S: AsRef<str>,
{
    fn from(value: S) -> Self {
        Var::Str(value.as_ref().to_string())
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
            (Sort::Type, Sort::Set) => None, // Set は impredicative （これでいいのか?????）
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct IndTypeName(String);

pub struct IndTypeDefs {
    signature: Vec<(Var, Exp)>,
    constructor: Vec<IndTypeCst>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct IndTypeCstName(String);

pub struct IndTypeCst {
    name_constructor: IndTypeCstName,
    parameter: Vec<(Var, Exp)>,
    return_signature: Vec<Exp>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Exp {
    Sort(Sort),
    Var(Var),
    Prod(Var, Box<Exp>, Box<Exp>),
    Lam(Var, Box<Exp>, Box<Exp>),
    App(Box<Exp>, Box<Exp>),
    // inductive hoge は global context を見ながらやること
    IndTypeType {
        type_name: IndTypeName,
        argument: Vec<Exp>,
    },
    IndTypeCst {
        type_name: IndTypeName,
        constructor_name: IndTypeCstName,
        argument: Vec<Exp>,
    },
    IndTypeElim {
        type_name: IndTypeName,
        eliminated_exp: Box<Exp>,
        cases: (Vec<(IndTypeCstName, Exp)>),
    },
    // これがほしいメインの部分
    // Sub(Var, Box<Exp>, Box<Exp>),
    // Take(Var, Box<Exp>, Box<Exp>),
    // Rec(Var, Var, Box<Exp>),
}

pub struct GlobalContext {
    definitions: Vec<(Var, Exp)>,
    assumptions: Vec<(Var, Exp)>,
    inductive_definitions: Vec<IndTypeDefs>,
}
