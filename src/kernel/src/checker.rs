// "interactive" type checker

use crate::{
    calculus::is_alpha_eq,
    derivation::prove_command,
    exp::{Context, Derivation, Exp, Judgement, Provable, ProveCommandBy, Var},
};

#[derive(Debug)]
pub struct Checker {
    context: Context,
}

impl Default for Checker {
    fn default() -> Self {
        Checker {
            context: Context(vec![]),
        }
    }
}

impl Checker {
    pub fn context(&self) -> &Context {
        &self.context
    }
    pub fn check(
        &mut self,
        term: &Exp,
        ty: &Exp,
    ) -> (Derivation, bool) {
        let (der, b) = crate::derivation::check(&self.context, term, ty);
        if !b {
            return (der, false);
        }

        (der, b)
    }
    pub fn infer(
        &mut self,
        term: &Exp,
    ) -> (Derivation, Option<Exp>) {
        let (der, ty_opt) = crate::derivation::infer(&self.context, term);
        if ty_opt.is_none() {
            return (der, None);
        }

        (der, ty_opt)
    }
    pub fn push(&mut self, var: Var, ty: Exp) -> (Derivation, bool) {
        let (der, res) = crate::derivation::infer_sort(&self.context, &ty);
        if res.is_none() {
            return (der, false);
        }

        self.context.0.push((var, ty));
        (der, true)
    }
    pub fn pop(&mut self) {
        self.context.0.pop();
    }
}
