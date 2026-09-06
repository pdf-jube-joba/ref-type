use kernel::{
    environment::CrateEnv,
    exp::Exp,
    program::{Computation, ComputationType, Value, ValueType},
};

pub(super) fn format_exp(env: &CrateEnv, exp: Exp) -> String {
    kernel::printing::format_exp(env, exp)
}

pub(super) fn format_value_type(env: &CrateEnv, ty: ValueType) -> String {
    kernel::printing::format_value_type(env, ty)
}
pub(super) fn format_computation_type(env: &CrateEnv, ty: ComputationType) -> String {
    kernel::printing::format_computation_type(env, ty)
}
pub(super) fn format_value(env: &CrateEnv, value: Value) -> String {
    kernel::printing::format_value(env, value)
}
pub(super) fn format_computation(env: &CrateEnv, computation: Computation) -> String {
    kernel::printing::format_computation(env, computation)
}
