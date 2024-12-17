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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Sort {
    Set,
    Type,
    Prop,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Exp {
    Sort(Sort),
    Var(Var),
    Prod(Var, Box<Exp>, Box<Exp>),
    Lam(Var, Box<Exp>, Box<Exp>),
    App(Box<Exp>, Box<Exp>),
    // Sub(Var, Box<Exp>, Box<Exp>),
    // Take(Var, Box<Exp>, Box<Exp>),
    // Rec(Var, Var, Box<Exp>),
}

