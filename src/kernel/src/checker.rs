// "interactive" type checker

use crate::exp::{Context, Derivation, Exp, ProveCommandBy, TypeInfer, Var};

#[derive(Debug)]
pub struct Checker {
    context: Context,
    derivations: Vec<Derivation>,
}

impl Default for Checker {
    fn default() -> Self {
        Checker {
            context: vec![].into(),
            derivations: vec![],
        }
    }
}

impl Checker {
    pub fn history(&self) -> &Vec<Derivation> {
        &self.derivations
    }
    pub fn context(&self) -> &Context {
        &self.context
    }
    pub fn check(&mut self, term: &Exp, ty: &Exp) -> bool {
        let derivation = crate::derivation::check(&self.context, term, ty);
        let res = derivation.node().unwrap().is_success();
        self.derivations.push(derivation);
        res
    }
    pub fn infer(&mut self, term: &Exp) -> Option<Exp> {
        let derivation = crate::derivation::infer(&self.context, term);
        let ty = {
            let TypeInfer { ty, .. } = derivation.node().unwrap().as_type_infer().unwrap();
            ty.clone()
        };
        self.derivations.push(derivation);
        ty
    }
    pub fn prove_command(&self, command: &ProveCommandBy) -> Derivation {
        crate::derivation::prove_command(&self.context, command)
    }
    pub fn chk_indspec(
        &mut self,
        params: Vec<(Var, Exp)>,
        indices: Vec<(Var, Exp)>,
        sort: crate::exp::Sort,
        constructors: Vec<crate::inductive::CtorType>,
    ) -> Result<crate::inductive::InductiveTypeSpecs, String> {
        let (derivation, res) = crate::inductive::acceptable_typespecs(
            &self.context,
            params,
            indices,
            sort,
            constructors,
        );
        self.derivations.extend(derivation);
        res
    }
    pub fn push(&mut self, var: Var, ty: Exp) -> bool {
        let der = crate::derivation::infer_sort(&self.context, &ty);
        let res = der.node().unwrap().is_success();
        self.derivations.push(der);
        if res {
            self.context.push((var, ty));
        }
        res
    }
    pub fn pop(&mut self) {
        self.context.pop();
    }
}
