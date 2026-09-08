//! Elaborate, certify, and evaluate interactive queries.
use super::*;

impl GlobalEnvironment {
    fn elaborate_query_term(
        &mut self,
        exp: &SExp,
        ctx: &mut ExpContext,
    ) -> Result<Exp, ElaborationError> {
        let mut local_scope = LocalScope::default();
        let exp_elab = local_scope.elab_exp(exp, self)?;
        if !self.metavariables.is_empty() {
            self.infer_term_with_metavariables(ctx, exp_elab)
                .map_err(|message| self.metavariables.constraint_error(message))?;
            self.finish_metavariables()?;
        }
        Ok(self.metavariables.zonk(&self.crate_env, exp_elab))
    }

    fn elaborate_query_computation(
        &mut self,
        exp: &ComputationTermExp,
    ) -> Result<crate::raw::program::ComputationTerm, ElaborationError> {
        let mut scope = program_term_elaborator::ProgramScope::new();
        let computation = scope.elaborate_computation(exp, self)?;
        let computation = if scope.has_metas() {
            scope
                .infer_computation_term_with_metas(self, computation)?
                .0
        } else {
            computation
        };
        Ok(computation)
    }

    fn certify_query(&mut self, context: &ExpContext, term: Exp, ty: Exp) -> Result<(), String> {
        let mut lower = crate::lowering::Lowerer::new(&self.crate_env, &mut self.kernel_env);
        let module = self.module_manager.current();
        let mut raw_context = context.clone();
        let term = lower.set(term, &mut raw_context, module)?;
        let expected = lower.classifier(ty, &mut raw_context, module)?;
        let context = lower.context(context, module)?;
        kernel::check::Checker::new(lower.kernel, context).check(term, expected)
    }

    fn certify_program_query(
        &mut self,
        context: &crate::raw::program::ProgramContext,
        term: crate::raw::program::ProgramTerm,
        ty: crate::raw::program::ProgramType,
    ) -> Result<(), String> {
        let mut lower = crate::lowering::Lowerer::new(&self.crate_env, &mut self.kernel_env);
        let term = lower.program_in_context(term, &mut context.clone())?;
        let ty = lower.program_type(ty)?;
        let context = lower.program_context(context)?;
        kernel::check::Checker::new(lower.kernel, context).check(term, ty)
    }

    pub(super) fn eval_query(
        &mut self,
        exp: &SExp,
        ctx: &mut ExpContext,
    ) -> Result<(), ElaborationError> {
        let exp_elab = self.elaborate_query_term(exp, ctx)?;
        self.outputs.push(Output::Exp(
            crate::raw::calculus::reduce_one(&self.crate_env, exp_elab).unwrap_or(exp_elab),
        ));
        Ok(())
    }

    pub(super) fn normalize_query(
        &mut self,
        exp: &SExp,
        ctx: &mut ExpContext,
    ) -> Result<(), ElaborationError> {
        let exp_elab = self.elaborate_query_term(exp, ctx)?;
        self.outputs
            .push(Output::Exp(crate::raw::calculus::normalize(
                &self.crate_env,
                exp_elab,
            )));
        Ok(())
    }

    pub(super) fn computation_eval_query(
        &mut self,
        exp: &ComputationTermExp,
    ) -> Result<(), ElaborationError> {
        let computation = self.elaborate_query_computation(exp)?;
        let reduced =
            crate::raw::program_calculus::reduce_computation_once(&self.crate_env, computation);
        self.outputs
            .push(Output::ComputationTerm(reduced.unwrap_or(computation)));
        Ok(())
    }

    pub(super) fn computation_normalize_query(
        &mut self,
        exp: &ComputationTermExp,
    ) -> Result<(), ElaborationError> {
        let computation = self.elaborate_query_computation(exp)?;
        self.outputs.push(
            match crate::raw::program_calculus::evaluate_computation(&self.crate_env, computation) {
                crate::raw::program_calculus::Evaluation::Normal(result) => {
                    Output::ComputationTerm(result)
                }
                crate::raw::program_calculus::Evaluation::OutOfFuel(result) => {
                    Output::OutOfFuel(result)
                }
            },
        );
        Ok(())
    }

    pub(super) fn value_check_query(
        &mut self,
        exp: &ValueTermExp,
        ty: &ValueTypeExp,
    ) -> Result<(), ElaborationError> {
        let mut scope = program_term_elaborator::ProgramScope::new();
        let ty = scope.elaborate_value_type(ty, self)?;
        let value = scope.elaborate_value(exp, self)?;
        let (value, ty) = scope.check_value_term_with_metas(self, value, ty)?;
        let mut context = scope.context().clone();
        ProgramCheckSession::new(&self.crate_env, &mut context)
            .check_value_term(value, ty)
            .map_err(|error| format!("Program value check failed: {error:?}"))?;
        self.certify_program_query(
            scope.context(),
            crate::raw::program::ProgramTerm::ValueTerm(value),
            crate::raw::program::ProgramType::ValueType(ty),
        )?;
        self.outputs.push(Output::ValueType(ty));
        Ok(())
    }

    pub(super) fn computation_check_query(
        &mut self,
        exp: &ComputationTermExp,
        ty: &ComputationTypeExp,
    ) -> Result<(), ElaborationError> {
        let mut scope = program_term_elaborator::ProgramScope::new();
        let ty = scope.elaborate_computation_type(ty, self)?;
        let computation = scope.elaborate_computation(exp, self)?;
        let (computation, ty) = scope.check_computation_term_with_metas(self, computation, ty)?;
        let mut context = scope.context().clone();
        ProgramCheckSession::new(&self.crate_env, &mut context)
            .check_computation_term(computation, ty)
            .map_err(|error| format!("Program computation check failed: {error:?}"))?;
        self.certify_program_query(
            scope.context(),
            crate::raw::program::ProgramTerm::ComputationTerm(computation),
            crate::raw::program::ProgramType::ComputationType(ty),
        )?;
        self.outputs.push(Output::ComputationType(ty));
        Ok(())
    }

    pub(super) fn value_infer_query(&mut self, exp: &ValueTermExp) -> Result<(), ElaborationError> {
        let mut scope = program_term_elaborator::ProgramScope::new();
        let value = scope.elaborate_value(exp, self)?;
        let (value, ty) = scope.infer_value_term_with_metas(self, value)?;
        self.certify_program_query(
            scope.context(),
            crate::raw::program::ProgramTerm::ValueTerm(value),
            crate::raw::program::ProgramType::ValueType(ty),
        )?;
        self.outputs.push(Output::ValueType(ty));
        Ok(())
    }

    pub(super) fn computation_infer_query(
        &mut self,
        exp: &ComputationTermExp,
    ) -> Result<(), ElaborationError> {
        let mut scope = program_term_elaborator::ProgramScope::new();
        let computation = scope.elaborate_computation(exp, self)?;
        let (computation, ty) = scope.infer_computation_term_with_metas(self, computation)?;
        self.certify_program_query(
            scope.context(),
            crate::raw::program::ProgramTerm::ComputationTerm(computation),
            crate::raw::program::ProgramType::ComputationType(ty),
        )?;
        self.outputs.push(Output::ComputationType(ty));
        Ok(())
    }

    pub(super) fn check_query(
        &mut self,
        exp: &SExp,
        ty: &SExp,
        ctx: &mut ExpContext,
    ) -> Result<(), ElaborationError> {
        let mut local_scope = LocalScope::default();
        let exp_elab = local_scope.elab_exp(exp, self)?;
        let ty_elab = local_scope.elab_exp(ty, self)?;
        if !self.metavariables.is_empty() {
            self.check_term_with_metavariables(ctx, exp_elab, ty_elab)
                .map_err(|message| self.metavariables.constraint_error(message))?;
            self.finish_metavariables()?;
        }
        let exp_elab = self.metavariables.zonk(&self.crate_env, exp_elab);
        let ty_elab = self.metavariables.zonk(&self.crate_env, ty_elab);
        let result = CheckSession::new(&self.crate_env, self.module_manager.current(), ctx)
            .check_pts(exp_elab, ty_elab)
            .map_err(|error| format!("{error:?}"))
            .and_then(|()| self.certify_query(ctx, exp_elab, ty_elab));
        self.outputs.push(match result {
            Ok(()) => Output::Exp(ty_elab),
            Err(error) => Output::Message(format!("check failed: {error}")),
        });
        Ok(())
    }

    pub(super) fn infer_query(
        &mut self,
        exp: &SExp,
        ctx: &mut ExpContext,
    ) -> Result<(), ElaborationError> {
        let exp_elab = self.elaborate_query_term(exp, ctx)?;
        let result = CheckSession::new(&self.crate_env, self.module_manager.current(), ctx)
            .infer_exp_judgement(exp_elab)
            .map_err(|error| format!("{error:?}"))
            .and_then(|judgement| {
                self.certify_query(ctx, exp_elab, judgement.ty)?;
                Ok(judgement.ty)
            });
        self.outputs.push(match result {
            Ok(ty) => Output::Exp(ty),
            Err(error) => Output::Message(format!("infer failed: {error}")),
        });
        Ok(())
    }
}
