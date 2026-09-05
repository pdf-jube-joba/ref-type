use kernel::{
    environment::CrateEnv,
    exp::{Exp, ExpContext},
    program::{Computation, ComputationType, ProgramContext, Value, ValueType},
};

pub(super) fn format_exp(env: &CrateEnv, exp: Exp) -> String {
    kernel::printing::format_exp(env, exp)
}

pub(super) fn format_ctx(env: &CrateEnv, ctx: &ExpContext) -> String {
    kernel::printing::format_ctx(env, ctx)
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
pub(super) fn format_program_ctx(env: &CrateEnv, ctx: &ProgramContext) -> String {
    kernel::printing::format_program_ctx(env, ctx)
}
