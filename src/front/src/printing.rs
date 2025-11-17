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

impl Display for SExp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SExp::AccessPath { access, parameters } => {
                match access {
                    LocalAccess::Current { access } => {
                        write!(f, "{}", access)?;
                    }
                    LocalAccess::Named { access, child } => {
                        write!(f, "{}.{}", access, child)?;
                    }
                }
                if !parameters.is_empty() {
                    write!(f, "[")?;
                    for (i, param) in parameters.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", param)?;
                    }
                    write!(f, "]")?;
                }
                Ok(())
            }
            SExp::AssociatedAccess { base, field } => {
                write!(f, "{}#{}", base, field)
            }
            SExp::MathMacro { tokens } => todo!(),
            SExp::NamedMacro { name, tokens } => todo!(),
            SExp::Where { exp, clauses } => {
                write!(f, "where {} {{ ", exp)?;
                for (var, ty, body) in clauses {
                    write!(f, "{}: {} := {}; ", var, ty, body)?;
                }
                write!(f, "}}")
            }
            SExp::WithProofs { exp, proofs } => {
                write!(f, "with_proofs {} {{ ", exp)?;
                for proof in proofs {
                    write!(f, "{:?} ", proof)?; // Placeholder
                }
                write!(f, "}}")
            }
            SExp::Sort(sort) => {
                write!(f, "{:?}", sort)
            }
            SExp::Prod { bind, body } => todo!(),
            SExp::Lam { bind, body } => todo!(),
            SExp::App { func, arg, piped } => todo!(),
            SExp::Cast { exp, to } => todo!(),
            SExp::IndElim {
                path,
                elim,
                return_type,
                cases,
            } => todo!(),
            SExp::IndElimPrim {
                path,
                parameters,
                sort,
            } => todo!(),
            SExp::RecordTypeCtor {
                access,
                parameters,
                fields,
            } => todo!(),
            SExp::ProveLater { prop } => todo!(),
            SExp::PowerSet { set } => todo!(),
            SExp::SubSet {
                var,
                set,
                predicate,
            } => todo!(),
            SExp::Pred {
                superset,
                subset,
                element,
            } => todo!(),
            SExp::TypeLift { superset, subset } => todo!(),
            SExp::Equal { left, right } => todo!(),
            SExp::Exists { bind } => todo!(),
            SExp::Take { bind, body } => todo!(),
            SExp::ProofTermRaw(sprove_command_by) => todo!(),
            SExp::Block(block) => todo!(),
        }
    }
}
