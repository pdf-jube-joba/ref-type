use front::output::Output;
use kernel::{environment::CrateEnv, printing};

pub fn format_output(env: &CrateEnv, output: &Output) -> String {
    match output {
        Output::Message(message) => message.clone(),
        Output::Exp(exp) => printing::format_exp(env, *exp),
        Output::ValueType(ty) => printing::format_value_type(env, *ty),
        Output::ComputationType(ty) => printing::format_computation_type(env, *ty),
        Output::Computation(computation) => printing::format_computation(env, *computation),
        Output::OutOfFuel(computation) => format!(
            "evaluation stopped after reaching the reduction limit: {}",
            printing::format_computation(env, *computation)
        ),
    }
}
