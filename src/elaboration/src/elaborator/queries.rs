//! Elaborate, certify, and evaluate interactive queries.
use super::*;
use crate::raw::program::{ProgramTerm, ProgramType};
use program_term_elaborator::ProgramScope;

struct ProgramQuery {
    scope: ProgramScope,
    term: ProgramTerm,
    expected: Option<ProgramType>,
}

impl GlobalEnvironment {
    fn elaborate_program_query(
        &mut self,
        exp: &SExp,
        expected: Option<&SExp>,
        computations_only: bool,
    ) -> Result<ProgramQuery, Vec<ElaborationError>> {
        let mut errors = Vec::new();
        // As in definitions, a bare CBV lambda/arrow denotes a computation.
        // Explicit thunks and value types select the value judgement.
        for computation in [true, false] {
            if !computation && computations_only {
                break;
            }
            self.metavariables.clear();
            let attempt = (|| -> Result<ProgramQuery, ElaborationError> {
                let mut scope = ProgramScope::new();
                let (term, expected) = if computation {
                    let expected = expected
                        .map(|ty| {
                            let ty = ComputationTypeExp::try_from(ty.clone())?;
                            scope
                                .elaborate_computation_type(&ty, self)
                                .map(ProgramType::ComputationType)
                        })
                        .transpose()?;
                    let exp = ComputationTermExp::try_from(exp.clone())?;
                    let term = scope.elaborate_computation(&exp, self)?;
                    (ProgramTerm::ComputationTerm(term), expected)
                } else {
                    let expected = expected
                        .map(|ty| {
                            let ty = ValueTypeExp::try_from(ty.clone())?;
                            scope
                                .elaborate_value_type(&ty, self)
                                .map(ProgramType::ValueType)
                        })
                        .transpose()?;
                    let exp = ValueTermExp::try_from(exp.clone())?;
                    let term = scope.elaborate_value(&exp, self)?;
                    (ProgramTerm::ValueTerm(term), expected)
                };
                Ok(ProgramQuery {
                    scope,
                    term,
                    expected,
                })
            })();
            match attempt {
                Ok(query) => return Ok(query),
                Err(error) => errors.push(error),
            }
        }
        self.metavariables.clear();
        Err(errors)
    }

    fn program_type_query(&mut self, query: ProgramQuery) -> Result<(), ElaborationError> {
        let ProgramQuery {
            mut scope,
            term,
            expected,
        } = query;
        let (term, ty, output) = match (term, expected) {
            (ProgramTerm::ValueTerm(value), expected) => {
                let (value, ty) = match expected {
                    Some(ProgramType::ValueType(ty)) => {
                        scope.check_value_term_with_metas(self, value, ty)?
                    }
                    None => scope.infer_value_term_with_metas(self, value)?,
                    _ => unreachable!("query type and term categories agree"),
                };
                (
                    ProgramTerm::ValueTerm(value),
                    ProgramType::ValueType(ty),
                    Output::ValueType(ty),
                )
            }
            (ProgramTerm::ComputationTerm(computation), expected) => {
                let (computation, ty) = match expected {
                    Some(ProgramType::ComputationType(ty)) => {
                        scope.check_computation_term_with_metas(self, computation, ty)?
                    }
                    None => scope.infer_computation_term_with_metas(self, computation)?,
                    _ => unreachable!("query type and term categories agree"),
                };
                (
                    ProgramTerm::ComputationTerm(computation),
                    ProgramType::ComputationType(ty),
                    Output::ComputationType(ty),
                )
            }
        };
        self.certify_program_query(scope.context(), term, ty)?;
        self.outputs.push(output);
        Ok(())
    }

    pub(super) fn check_query(
        &mut self,
        exp: &SExp,
        ty: &SExp,
        ctx: &mut ExpContext,
    ) -> Result<(), ElaborationError> {
        match self.elaborate_program_query(exp, Some(ty), false) {
            Ok(query) => self.program_type_query(query),
            Err(mut errors) => self.pts_check_query(exp, ty, ctx).map_err(|error| {
                errors.insert(0, error);
                ElaborationError::alternatives(errors)
            }),
        }
    }

    pub(super) fn infer_query(
        &mut self,
        exp: &SExp,
        ctx: &mut ExpContext,
    ) -> Result<(), ElaborationError> {
        match self.elaborate_program_query(exp, None, false) {
            Ok(query) => self.program_type_query(query),
            Err(mut errors) => self.pts_infer_query(exp, ctx).map_err(|error| {
                errors.insert(0, error);
                ElaborationError::alternatives(errors)
            }),
        }
    }

    fn evaluation_query(
        &mut self,
        exp: &SExp,
        ctx: &mut ExpContext,
        normalize: bool,
    ) -> Result<(), ElaborationError> {
        match self.elaborate_program_query(exp, None, true) {
            Ok(ProgramQuery {
                mut scope,
                term: ProgramTerm::ComputationTerm(mut computation),
                ..
            }) => {
                // Raw evaluation permits stuck non-recursive syntax. Runs and
                // inference holes require checking before evaluation.
                if scope.query_requires_checking() {
                    let (checked, ty) =
                        scope.infer_computation_term_with_metas(self, computation)?;
                    self.certify_program_query(
                        scope.context(),
                        ProgramTerm::ComputationTerm(checked),
                        ProgramType::ComputationType(ty),
                    )?;
                    computation = checked;
                }
                let output = if normalize {
                    match crate::raw::program_calculus::evaluate_computation(
                        &self.crate_env,
                        computation,
                    ) {
                        crate::raw::program_calculus::Evaluation::Normal(result) => {
                            Output::ComputationTerm(result)
                        }
                        crate::raw::program_calculus::Evaluation::OutOfFuel(result) => {
                            Output::OutOfFuel(result)
                        }
                    }
                } else {
                    let reduced = crate::raw::program_calculus::reduce_computation_once(
                        &self.crate_env,
                        computation,
                    );
                    Output::ComputationTerm(reduced.unwrap_or(computation))
                };
                self.outputs.push(output);
                Ok(())
            }
            Ok(_) => unreachable!("evaluation elaborates computations only"),
            Err(mut errors) => {
                let result = if normalize {
                    self.pts_normalize_query(exp, ctx)
                } else {
                    self.pts_eval_query(exp, ctx)
                };
                result.map_err(|error| {
                    errors.insert(0, error);
                    ElaborationError::alternatives(errors)
                })
            }
        }
    }

    pub(super) fn eval_query(
        &mut self,
        exp: &SExp,
        ctx: &mut ExpContext,
    ) -> Result<(), ElaborationError> {
        self.evaluation_query(exp, ctx, false)
    }

    pub(super) fn normalize_query(
        &mut self,
        exp: &SExp,
        ctx: &mut ExpContext,
    ) -> Result<(), ElaborationError> {
        self.evaluation_query(exp, ctx, true)
    }

    fn elaborate_query_term(
        &mut self,
        exp: &SExp,
        ctx: &mut ExpContext,
    ) -> Result<Exp, ElaborationError> {
        let mut local_scope = LocalScope::default();
        let exp_elab = local_scope.elab_exp(exp, self)?;
        if !self.metavariables.is_empty() {
            self.infer_term_with_metavariables(ctx, exp_elab)
                .map_err(|message| {
                    self.metavariables
                        .constraint_error(&self.crate_env, message)
                })?;
            self.finish_metavariables()?;
        }
        Ok(self.metavariables.zonk(&self.crate_env, exp_elab))
    }

    fn certify_query(&mut self, context: &ExpContext, term: Exp, ty: Exp) -> Result<(), String> {
        crate::lowering::Lowerer::new(&self.crate_env, &mut self.crate_env.kernel.borrow_mut())
            .check_query(context, self.module_manager.current(), term, ty)
    }

    fn certify_program_query(
        &mut self,
        context: &crate::raw::program::ProgramContext,
        term: crate::raw::program::ProgramTerm,
        ty: crate::raw::program::ProgramType,
    ) -> Result<(), String> {
        crate::lowering::Lowerer::new(&self.crate_env, &mut self.crate_env.kernel.borrow_mut())
            .check_program_query(context, term, ty)
    }

    fn pts_eval_query(&mut self, exp: &SExp, ctx: &mut ExpContext) -> Result<(), ElaborationError> {
        let exp_elab = self.elaborate_query_term(exp, ctx)?;
        self.outputs.push(Output::Exp(
            crate::raw::calculus::reduce_one(&self.crate_env, exp_elab).unwrap_or(exp_elab),
        ));
        Ok(())
    }

    fn pts_normalize_query(
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

    fn pts_check_query(
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
                .map_err(|message| {
                    self.metavariables
                        .constraint_error(&self.crate_env, message)
                })?;
            self.finish_metavariables()?;
        }
        let exp_elab = self.metavariables.zonk(&self.crate_env, exp_elab);
        let ty_elab = self.metavariables.zonk(&self.crate_env, ty_elab);
        let result = CheckSession::new(&self.crate_env, ctx)
            .check_pts(exp_elab, ty_elab)
            .map_err(|error| format!("{error}"))
            .and_then(|()| self.certify_query(ctx, exp_elab, ty_elab));
        self.outputs.push(match result {
            Ok(()) => Output::Exp(ty_elab),
            Err(error) => Output::Message(format!("check failed: {error}")),
        });
        Ok(())
    }

    fn pts_infer_query(
        &mut self,
        exp: &SExp,
        ctx: &mut ExpContext,
    ) -> Result<(), ElaborationError> {
        let exp_elab = self.elaborate_query_term(exp, ctx)?;
        let result = CheckSession::new(&self.crate_env, ctx)
            .infer_exp_judgement(exp_elab)
            .map_err(|error| format!("{error}"))
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

#[cfg(test)]
mod tests {
    use super::*;
    use ::syntax::parse;

    #[test]
    fn unified_queries_dispatch_by_type_and_term() {
        let source = r#"
            \module Queries(A: \VType, x: A) {
                \inductive Unit: \Set := | unit: Unit;
                \definition logical: Unit := Unit::unit;
                \check logical: Unit;
                \infer logical;
                \eval logical;
                \normalize logical;

                \definition value: A := x;
                \definition computation: \F(A) := \return x;
                \check value: A;
                \infer value;
                \check computation: \F(A);
                \infer computation;
                \eval computation;
                \normalize computation;
            }
        "#;
        let modules = parse::str_parse_modules(source).unwrap();
        let mut environment = GlobalEnvironment::default();
        environment.add_new_module_to_root(&modules[0]).unwrap();
        use crate::output::Output;
        assert!(matches!(
            environment.outputs.as_slice(),
            [
                Output::Exp(_),
                Output::Exp(_),
                Output::Exp(_),
                Output::Exp(_),
                Output::ValueType(_),
                Output::ValueType(_),
                Output::ComputationType(_),
                Output::ComputationType(_),
                Output::ComputationTerm(_),
                Output::ComputationTerm(_),
            ]
        ));
        for output in &environment.outputs[8..] {
            let Output::ComputationTerm(term) = output else {
                unreachable!()
            };
            assert!(matches!(
                environment.crate_env.arena().get(*term),
                crate::raw::program::ComputationTermNode::Return { .. }
            ));
        }
    }
}
