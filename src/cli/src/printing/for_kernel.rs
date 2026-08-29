use kernel::{
    environment::CrateEnv,
    exp::{Context, Exp},
};

pub(super) fn format_exp(env: &CrateEnv, exp: Exp) -> String {
    kernel::printing::format_exp(env, exp)
}

pub(super) fn format_ctx(env: &CrateEnv, ctx: &Context) -> String {
    kernel::printing::format_ctx(env, ctx)
}
