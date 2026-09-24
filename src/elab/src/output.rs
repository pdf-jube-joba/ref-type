use crate::{
    exp::Exp,
    program::{ComputationTerm, ComputationType, ValueType},
};

#[derive(Debug, Clone)]
pub enum Output {
    Message(String),
    Exp(Exp),
    ValueType(ValueType),
    ComputationType(ComputationType),
    ComputationTerm(ComputationTerm),
    OutOfFuel(ComputationTerm),
}

impl Output {
    pub fn render(&self, env: &crate::environment::CrateEnv) -> String {
        use crate::printing;
        match self {
            Self::Message(message) => message.clone(),
            Self::Exp(exp) => printing::format_exp(env, *exp),
            Self::ValueType(ty) => printing::format_value_type(env, *ty),
            Self::ComputationType(ty) => printing::format_computation_type(env, *ty),
            Self::ComputationTerm(term) => printing::format_computation(env, *term),
            Self::OutOfFuel(term) => format!(
                "evaluation stopped after reaching the reduction limit: {}",
                printing::format_computation(env, *term)
            ),
        }
    }
}
