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
    pub fn check(&self, term: &Exp, ty: &Exp) -> Result<Derivation, Derivation> {
        let derivation = crate::derivation::check(&self.context, term, ty);
        if derivation.node().unwrap().is_success() {
            Ok(derivation)
        } else {
            Err(derivation)
        }
    }
    pub fn infer(&self, term: &Exp) -> Result<Derivation, Derivation> {
        let derivation = crate::derivation::infer(&self.context, term);
        if derivation.node().unwrap().is_success() {
            Ok(derivation)
        } else {
            Err(derivation)
        }
    }
    pub fn prove_command(&self, command: &ProveCommandBy) -> Derivation {
        crate::derivation::prove_command(&self.context, command)
    }
    pub fn push(&mut self, var: Var, ty: Exp) -> Result<Derivation, Derivation> {
        let der = crate::derivation::infer_sort(&self.context, &ty);
        if !der.node().unwrap().is_success() {
            return Err(der);
        }

        self.context.0.push((var, ty));
        Ok(der)
    }
    pub fn pop(&mut self) {
        self.context.0.pop();
    }
}
