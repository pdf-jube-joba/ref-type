use kernel::{
    environment::CrateEnv,
    exp::{Context, RawExp},
};

pub(super) fn format_exp(env: &CrateEnv, exp: RawExp) -> String {
    kernel::printing::format_exp(env, exp)
}

pub(super) fn format_ctx(env: &CrateEnv, ctx: &Context) -> String {
    kernel::printing::format_ctx(env, ctx)
}
