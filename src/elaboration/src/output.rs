use crate::raw::{
    exp::Exp,
    program::{ComputationTerm, ComputationType, ValueType},
};

#[derive(Debug, Clone)]
pub enum Output {
    Failure(crate::error::Error),
    Exp(Exp),
    ValueType(ValueType),
    ComputationType(ComputationType),
    ComputationTerm(ComputationTerm),
    OutOfFuel(ComputationTerm),
}

pub fn format_output(env: &crate::raw::environment::CrateEnv, output: &Output) -> String {
    match output {
        Output::Failure(error) => error.render(env),
        Output::Exp(exp) => crate::raw::printing::format_exp(env, *exp),
        Output::ValueType(ty) => crate::raw::printing::format_value_type(env, *ty),
        Output::ComputationType(ty) => crate::raw::printing::format_computation_type(env, *ty),
        Output::ComputationTerm(computation) => {
            crate::raw::printing::format_computation(env, *computation)
        }
        Output::OutOfFuel(computation) => format!(
            "evaluation stopped after reaching the reduction limit: {}",
            crate::raw::printing::format_computation(env, *computation)
        ),
    }
}
