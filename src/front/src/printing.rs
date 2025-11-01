use std::fmt::Display;

use super::syntax::*;


impl From<Identifier> for kernel::exp::Var {
    fn from(value: Identifier) -> Self {
        kernel::exp::Var::new(&value.0)
    }
}

impl From<&Identifier> for kernel::exp::Var {
    fn from(value: &Identifier) -> Self {
        kernel::exp::Var::new(&value.0)
    }
}

impl From<String> for Identifier {
    fn from(value: String) -> Self {
        Identifier(value)
    }
}

impl From<&str> for Identifier {
    fn from(value: &str) -> Self {
        Identifier(value.to_string())
    }
}

impl Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for MacroToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
