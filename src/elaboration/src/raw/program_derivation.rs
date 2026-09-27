//! Source-facing Program judgements delegated to the shared kernel.
use crate::raw::{
    derivation::JudgementError, environment::CrateEnv, exp::Arena, program::*, traversal::Term,
};
pub struct ProgramCheckSession<'env, 'context> {
    env: &'env CrateEnv,
    context: &'context mut ProgramContext,
}
impl<'env, 'context> ProgramCheckSession<'env, 'context> {
    pub fn new(env: &'env CrateEnv, context: &'context mut ProgramContext) -> Self {
        Self { env, context }
    }
    pub fn env(&self) -> &'env CrateEnv {
        self.env
    }
    pub fn arena(&self) -> &'env Arena {
        self.env.arena()
    }
    pub fn context(&self) -> &ProgramContext {
        self.context
    }
    fn infer(&self, term: Term) -> Result<kernel::syntax::Expression, Box<JudgementError>> {
        crate::kernel_bridge::program(self.env, self.context, &[term], |env, context, terms| {
            kernel::check::Checker::new(
                env,
                &mut kernel::metavariables::MetaContext::new(),
                context,
            )
            .infer(terms[0])
        })
        .map_err(|e| Box::new(JudgementError::caused(e)))
    }
    fn check(&self, term: Term, ty: Term) -> Result<(), Box<JudgementError>> {
        crate::kernel_bridge::program(
            self.env,
            self.context,
            &[term, ty],
            |env, context, terms| {
                kernel::check::Checker::new(
                    env,
                    &mut kernel::metavariables::MetaContext::new(),
                    context,
                )
                .check(terms[0], terms[1])
            },
        )
        .map_err(|e| Box::new(JudgementError::caused(e)))
    }
    pub fn check_value_type(&mut self, ty: ValueType) -> Result<(), Box<JudgementError>> {
        let inferred = self.infer(Term::ValueType(ty))?;
        if matches!(
            self.arena().core.get(inferred),
            kernel::syntax::Node::Sort(kernel::sort::Sort::Base(kernel::sort::BaseSort::Value(_)))
        ) {
            Ok(())
        } else {
            Err(Box::new(JudgementError::caused(
                "incorrect Program type sort",
            )))
        }
    }
    pub fn infer_value_term(&mut self, term: ValueTerm) -> Result<ValueType, Box<JudgementError>> {
        self.infer(Term::Value(term)).map(ValueType)
    }
    pub fn check_value_term(
        &mut self,
        term: ValueTerm,
        ty: ValueType,
    ) -> Result<(), Box<JudgementError>> {
        self.check(Term::Value(term), Term::ValueType(ty))
    }
    #[cfg(test)]
    pub fn infer_computation_term(
        &mut self,
        term: ComputationTerm,
    ) -> Result<ComputationType, Box<JudgementError>> {
        self.infer(Term::Computation(term)).map(ComputationType)
    }
    pub fn check_computation_term(
        &mut self,
        term: ComputationTerm,
        ty: ComputationType,
    ) -> Result<(), Box<JudgementError>> {
        self.check(Term::Computation(term), Term::ComputationType(ty))
    }
}
