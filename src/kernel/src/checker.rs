// "interactive" type checker

use crate::exp::{Context, Derivation, Exp, ProveCommandBy, Var};

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
    pub fn check(&self, term: &Exp, ty: &Exp) -> Derivation {
        crate::derivation::check(&self.context, term, ty)
    }
    pub fn infer(&self, term: &Exp) -> Derivation {
        crate::derivation::infer(&self.context, term)
    }
    pub fn prove_command(&self, command: &ProveCommandBy) -> Derivation {
        crate::derivation::prove_command(&self.context, command)
    }
    pub fn push(&mut self, var: Var, ty: Exp) -> Derivation {
        let der = crate::derivation::infer_sort(&self.context, &ty);
        if !der.node().unwrap().is_success() {
            return der;
        }

        self.context.0.push((var, ty));
        der
    }
    pub fn pop(&mut self) {
        self.context.0.pop();
    }
}
