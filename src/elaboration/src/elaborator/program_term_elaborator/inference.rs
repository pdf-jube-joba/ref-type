//! Contextual Program metavariables, constraint solving, and diagnostics.
use super::*;

impl ProgramScope {
    fn unify_value_types(
        &mut self,
        environment: &GlobalEnvironment,
        left: ValueType,
        right: ValueType,
    ) -> Result<(), String> {
        let index = self.record_constraint(
            environment,
            ProgramConstraint::Equal(Term::ValueType(left), Term::ValueType(right)),
        );
        let result = self.unify_value_types_inner(environment, left, right);
        self.constraints[index].status = if result.is_ok() {
            ConstraintStatus::Discharged
        } else {
            ConstraintStatus::Failed
        };
        result
    }

    fn unify_value_types_inner(
        &mut self,
        environment: &GlobalEnvironment,
        left: ValueType,
        right: ValueType,
    ) -> Result<(), String> {
        let arena = environment.crate_env.arena();
        let left = self.zonk_value_type(environment, left);
        let right = self.zonk_value_type(environment, right);
        if crate::raw::program_calculus::value_type_is_alpha_eq(arena, left, right) {
            return Ok(());
        }
        match (arena.get(left), arena.get(right)) {
            (
                ValueTypeNode::Meta {
                    metavariable,
                    spine,
                },
                _,
            ) => self.assign(environment, metavariable, &spine, Term::ValueType(right)),
            (
                _,
                ValueTypeNode::Meta {
                    metavariable,
                    spine,
                },
            ) => self.assign(environment, metavariable, &spine, Term::ValueType(left)),
            (
                ValueTypeNode::Thunk {
                    computation_ty: left,
                },
                ValueTypeNode::Thunk {
                    computation_ty: right,
                },
            ) => self.unify_computation_types(environment, left, right),
            (
                ValueTypeNode::RunStep {
                    state_ty: left_state,
                    result_ty: left_result,
                },
                ValueTypeNode::RunStep {
                    state_ty: right_state,
                    result_ty: right_result,
                },
            ) => {
                self.unify_value_types(environment, left_state, right_state)?;
                self.unify_value_types(environment, left_result, right_result)
            }
            (
                ValueTypeNode::Inductive {
                    indspec: left_spec,
                    parameters: left_parameters,
                },
                ValueTypeNode::Inductive {
                    indspec: right_spec,
                    parameters: right_parameters,
                },
            ) if left_spec == right_spec && left_parameters.len() == right_parameters.len() => {
                for (left, right) in left_parameters.into_iter().zip(right_parameters) {
                    self.unify_value_types(environment, left, right)?;
                }
                Ok(())
            }
            _ => Err(format!(
                "Program value types do not unify: {:?} and {:?}",
                arena.get(left),
                arena.get(right)
            )),
        }
    }

    fn unify_computation_types(
        &mut self,
        environment: &GlobalEnvironment,
        left: ComputationType,
        right: ComputationType,
    ) -> Result<(), String> {
        let index = self.record_constraint(
            environment,
            ProgramConstraint::Equal(Term::ComputationType(left), Term::ComputationType(right)),
        );
        let result = self.unify_computation_types_inner(environment, left, right);
        self.constraints[index].status = if result.is_ok() {
            ConstraintStatus::Discharged
        } else {
            ConstraintStatus::Failed
        };
        result
    }

    fn unify_computation_types_inner(
        &mut self,
        environment: &GlobalEnvironment,
        left: ComputationType,
        right: ComputationType,
    ) -> Result<(), String> {
        let arena = environment.crate_env.arena();
        let left = self.zonk_computation_type(environment, left);
        let right = self.zonk_computation_type(environment, right);
        if crate::raw::program_calculus::computation_type_is_alpha_eq(arena, left, right) {
            return Ok(());
        }
        match (arena.get(left), arena.get(right)) {
            (
                ComputationTypeNode::Meta {
                    metavariable,
                    spine,
                },
                _,
            ) => self.assign(
                environment,
                metavariable,
                &spine,
                Term::ComputationType(right),
            ),
            (
                _,
                ComputationTypeNode::Meta {
                    metavariable,
                    spine,
                },
            ) => self.assign(
                environment,
                metavariable,
                &spine,
                Term::ComputationType(left),
            ),
            (
                ComputationTypeNode::Return { value_ty: left },
                ComputationTypeNode::Return { value_ty: right },
            ) => self.unify_value_types(environment, left, right),
            (
                ComputationTypeNode::Function {
                    domain: left_domain,
                    codomain: left_codomain,
                },
                ComputationTypeNode::Function {
                    domain: right_domain,
                    codomain: right_codomain,
                },
            ) => {
                self.unify_value_types(environment, left_domain, right_domain)?;
                self.unify_computation_types(environment, left_codomain, right_codomain)
            }
            _ => Err(format!(
                "Program computation types do not unify: {:?} and {:?}",
                arena.get(left),
                arena.get(right)
            )),
        }
    }

    pub(super) fn infer_kernel_value(
        &self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        value: ValueTerm,
    ) -> Result<ValueType, String> {
        ProgramCheckSession::new(&environment.crate_env, context)
            .infer_value_term(value)
            .map_err(|error| format!("cannot infer Program value: {error:?}"))
    }

    fn infer_kernel_computation(
        &self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        computation: ComputationTerm,
    ) -> Result<ComputationType, String> {
        ProgramCheckSession::new(&environment.crate_env, context)
            .infer_computation_term(computation)
            .map_err(|error| format!("cannot infer Program computation: {error:?}"))
    }

    fn solve_value(
        &mut self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        value: ValueTerm,
        expected: ValueType,
    ) -> Result<(), String> {
        let previous = self.origins.clone();
        let term = Term::Value(value);
        self.origins
            .extend(self.sources.get(&term).into_iter().flatten().copied());
        if let Some((id, _)) = occurrence(environment.crate_env.arena(), term) {
            self.origins
                .extend(self.metas[id.index()].occurrences.iter().copied());
        }
        let result = self.solve_value_inner(environment, context, value, expected);
        self.origins = previous;
        result
    }

    fn solve_value_inner(
        &mut self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        value: ValueTerm,
        expected: ValueType,
    ) -> Result<(), String> {
        let arena = environment.crate_env.arena();
        let expected = self.zonk_value_type(environment, expected);
        match arena.get(value) {
            ValueTermNode::DefinitionInstance { .. } => {
                let inferred = self.infer_value_term(environment, context, value)?;
                self.unify_value_types(environment, inferred, expected)
            }
            ValueTermNode::Meta {
                metavariable,
                spine,
            } => self.expect_meta(
                environment,
                metavariable,
                &spine,
                Term::Value(value),
                Term::ValueType(expected),
            ),
            ValueTermNode::Bound(_)
            | ValueTermNode::ModuleParam(_)
            | ValueTermNode::DefinedConstant(_) => {
                let inferred = self.infer_kernel_value(environment, context, value)?;
                self.unify_value_types(environment, inferred, expected)
            }
            ValueTermNode::Thunk { computation } => {
                if let ValueTypeNode::Thunk { computation_ty } = arena.get(expected) {
                    self.solve_computation(environment, context, computation, computation_ty)
                } else {
                    let inferred =
                        self.infer_computation_term(environment, context, computation)?;
                    let inferred = arena.alloc(ValueTypeNode::Thunk {
                        computation_ty: inferred,
                    });
                    self.unify_value_types(environment, inferred, expected)
                }
            }
            ValueTermNode::Continue {
                state_ty,
                result_ty,
                next,
            } => {
                if let ValueTypeNode::RunStep {
                    state_ty: expected_state,
                    result_ty: expected_result,
                } = arena.get(expected)
                {
                    self.unify_value_types(environment, state_ty, expected_state)?;
                    self.unify_value_types(environment, result_ty, expected_result)?;
                }
                self.solve_value(environment, context, next, state_ty)?;
                let inferred = arena.alloc(ValueTypeNode::RunStep {
                    state_ty,
                    result_ty,
                });
                self.unify_value_types(environment, inferred, expected)
            }
            ValueTermNode::Finish {
                state_ty,
                result_ty,
                output,
            } => {
                if let ValueTypeNode::RunStep {
                    state_ty: expected_state,
                    result_ty: expected_result,
                } = arena.get(expected)
                {
                    self.unify_value_types(environment, state_ty, expected_state)?;
                    self.unify_value_types(environment, result_ty, expected_result)?;
                }
                self.solve_value(environment, context, output, result_ty)?;
                let inferred = arena.alloc(ValueTypeNode::RunStep {
                    state_ty,
                    result_ty,
                });
                self.unify_value_types(environment, inferred, expected)
            }
            ValueTermNode::InductiveConstructor {
                indspec,
                parameters,
                idx,
                fields,
            } => {
                let result = arena.alloc(ValueTypeNode::Inductive {
                    indspec,
                    parameters: parameters.clone(),
                });
                self.unify_value_types(environment, result, expected)?;
                let parameters = parameters
                    .into_iter()
                    .map(|parameter| self.zonk_value_type(environment, parameter))
                    .collect::<Vec<_>>();
                let expected_fields = environment
                    .crate_env
                    .program_inductive(indspec)
                    .constructors()
                    .get(idx)
                    .ok_or_else(|| "Program constructor index out of bounds".to_string())?
                    .instantiated_fields(arena, &parameters);
                if fields.len() != expected_fields.len() {
                    return Err("Program constructor field count mismatch".into());
                }
                for (field, (_, field_ty)) in fields.into_iter().zip(expected_fields) {
                    self.solve_value(environment, context, field, field_ty)?;
                }
                Ok(())
            }
        }
    }

    pub(super) fn infer_value_term(
        &mut self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        value: ValueTerm,
    ) -> Result<ValueType, String> {
        let previous = self.origins.clone();
        let term = Term::Value(value);
        self.origins
            .extend(self.sources.get(&term).into_iter().flatten().copied());
        if let Some((id, _)) = occurrence(environment.crate_env.arena(), term) {
            self.origins
                .extend(self.metas[id.index()].occurrences.iter().copied());
        }
        let result = self.infer_value_term_inner(environment, context, value);
        self.origins = previous;
        result
    }

    fn infer_value_term_inner(
        &mut self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        value: ValueTerm,
    ) -> Result<ValueType, String> {
        let arena = environment.crate_env.arena();
        match arena.get(value) {
            ValueTermNode::DefinitionInstance {
                definition,
                parameters,
            } => {
                let DefinedConstant::ProgramValue { ty, .. } =
                    environment.crate_env.definition(definition)
                else {
                    return Err("wrong Program associated item category".into());
                };
                Ok(crate::raw::program_definitions::instantiate_value_type(
                    arena,
                    *ty,
                    &parameters,
                    0,
                ))
            }
            ValueTermNode::Meta {
                metavariable,
                spine,
            } => {
                let ty = self.infer_meta_type(
                    environment,
                    metavariable,
                    &spine,
                    context,
                    Term::Value(value),
                );
                let Term::ValueType(ty) = ty else {
                    unreachable!()
                };
                Ok(ty)
            }
            ValueTermNode::Bound(_)
            | ValueTermNode::ModuleParam(_)
            | ValueTermNode::DefinedConstant(_) => {
                self.infer_kernel_value(environment, context, value)
            }
            ValueTermNode::Thunk { computation } => {
                let computation_ty =
                    self.infer_computation_term(environment, context, computation)?;
                Ok(arena.alloc(ValueTypeNode::Thunk { computation_ty }))
            }
            ValueTermNode::Continue {
                state_ty,
                result_ty,
                next,
            } => {
                self.solve_value(environment, context, next, state_ty)?;
                Ok(arena.alloc(ValueTypeNode::RunStep {
                    state_ty: self.zonk_value_type(environment, state_ty),
                    result_ty: self.zonk_value_type(environment, result_ty),
                }))
            }
            ValueTermNode::Finish {
                state_ty,
                result_ty,
                output,
            } => {
                self.solve_value(environment, context, output, result_ty)?;
                Ok(arena.alloc(ValueTypeNode::RunStep {
                    state_ty: self.zonk_value_type(environment, state_ty),
                    result_ty: self.zonk_value_type(environment, result_ty),
                }))
            }
            ValueTermNode::InductiveConstructor {
                indspec,
                parameters,
                idx,
                fields,
            } => {
                let expected_fields = environment
                    .crate_env
                    .program_inductive(indspec)
                    .constructors()
                    .get(idx)
                    .ok_or_else(|| "Program constructor index out of bounds".to_string())?
                    .instantiated_fields(arena, &parameters);
                if fields.len() != expected_fields.len() {
                    return Err("Program constructor field count mismatch".into());
                }
                for (field, (_, field_ty)) in fields.into_iter().zip(expected_fields) {
                    self.solve_value(environment, context, field, field_ty)?;
                }
                Ok(arena.alloc(ValueTypeNode::Inductive {
                    indspec,
                    parameters: parameters
                        .into_iter()
                        .map(|parameter| self.zonk_value_type(environment, parameter))
                        .collect(),
                }))
            }
        }
    }

    fn solve_computation(
        &mut self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        computation: ComputationTerm,
        expected: ComputationType,
    ) -> Result<(), String> {
        let previous = self.origins.clone();
        let term = Term::Computation(computation);
        self.origins
            .extend(self.sources.get(&term).into_iter().flatten().copied());
        if let Some((id, _)) = occurrence(environment.crate_env.arena(), term) {
            self.origins
                .extend(self.metas[id.index()].occurrences.iter().copied());
        }
        let result = self.solve_computation_inner(environment, context, computation, expected);
        self.origins = previous;
        result
    }

    fn solve_computation_inner(
        &mut self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        computation: ComputationTerm,
        expected: ComputationType,
    ) -> Result<(), String> {
        let arena = environment.crate_env.arena();
        let expected = self.zonk_computation_type(environment, expected);
        match arena.get(computation) {
            ComputationTermNode::Meta {
                metavariable,
                spine,
            } => self.expect_meta(
                environment,
                metavariable,
                &spine,
                Term::Computation(computation),
                Term::ComputationType(expected),
            ),
            ComputationTermNode::DefinedConstant(_) => {
                let inferred = self.infer_kernel_computation(environment, context, computation)?;
                self.unify_computation_types(environment, inferred, expected)
            }
            ComputationTermNode::Return { value } => {
                if let ComputationTypeNode::Return { value_ty } = arena.get(expected) {
                    self.solve_value(environment, context, value, value_ty)
                } else {
                    let value_ty = self.infer_value_term(environment, context, value)?;
                    let inferred = arena.alloc(ComputationTypeNode::Return { value_ty });
                    self.unify_computation_types(environment, inferred, expected)
                }
            }
            ComputationTermNode::Force { value } => {
                let value_ty = self.infer_value_term(environment, context, value)?;
                let value_ty = self.zonk_value_type(environment, value_ty);
                let ValueTypeNode::Thunk { computation_ty } = arena.get(value_ty) else {
                    return Err("forced Program value is not a thunk".into());
                };
                self.unify_computation_types(environment, computation_ty, expected)
            }
            ComputationTermNode::Lambda {
                var,
                value_ty,
                body,
            } => {
                let ComputationTypeNode::Function { domain, codomain } = arena.get(expected) else {
                    let inferred =
                        self.infer_computation_term(environment, context, computation)?;
                    return self.unify_computation_types(environment, inferred, expected);
                };
                self.unify_value_types(environment, value_ty, domain)?;
                let domain = self.zonk_value_type(environment, domain);
                context.push(ProgramContextEntry::ValueTerm { var, ty: domain });
                let codomain = crate::raw::program_calculus::shift_computation_type_indices(
                    arena, codomain, 1, 0,
                );
                let result = self.solve_computation(environment, context, body, codomain);
                context.pop();
                result
            }
            ComputationTermNode::Application { computation, value } => {
                let function_ty = self.infer_computation_term(environment, context, computation)?;
                let function_ty = self.zonk_computation_type(environment, function_ty);
                let ComputationTypeNode::Function { domain, codomain } = arena.get(function_ty)
                else {
                    return Err("Program computation application head is not a function".into());
                };
                self.solve_value(environment, context, value, domain)?;
                self.unify_computation_types(environment, codomain, expected)
            }
            ComputationTermNode::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => {
                self.solve_value(environment, context, value, value_ty)?;
                let value_ty = self.zonk_value_type(environment, value_ty);
                context.push(ProgramContextEntry::ValueTerm { var, ty: value_ty });
                let expected = crate::raw::program_calculus::shift_computation_type_indices(
                    arena, expected, 1, 0,
                );
                let result = self.solve_computation(environment, context, body, expected);
                context.pop();
                result
            }
            ComputationTermNode::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => {
                let first_ty = self.infer_computation_term(environment, context, computation)?;
                let first_ty = self.zonk_computation_type(environment, first_ty);
                let ComputationTypeNode::Return { value_ty: returned } = arena.get(first_ty) else {
                    return Err("Program sequence head does not return a value".into());
                };
                self.unify_value_types(environment, value_ty, returned)?;
                let value_ty = self.zonk_value_type(environment, value_ty);
                context.push(ProgramContextEntry::ValueTerm { var, ty: value_ty });
                let expected = crate::raw::program_calculus::shift_computation_type_indices(
                    arena, expected, 1, 0,
                );
                let result = self.solve_computation(environment, context, body, expected);
                context.pop();
                result
            }
            _ => {
                let inferred = self.infer_computation_term(environment, context, computation)?;
                self.unify_computation_types(environment, inferred, expected)
            }
        }
    }

    pub(super) fn infer_computation_term(
        &mut self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        computation: ComputationTerm,
    ) -> Result<ComputationType, String> {
        let previous = self.origins.clone();
        let term = Term::Computation(computation);
        self.origins
            .extend(self.sources.get(&term).into_iter().flatten().copied());
        if let Some((id, _)) = occurrence(environment.crate_env.arena(), term) {
            self.origins
                .extend(self.metas[id.index()].occurrences.iter().copied());
        }
        let result = self.infer_computation_term_inner(environment, context, computation);
        self.origins = previous;
        result
    }

    fn infer_computation_term_inner(
        &mut self,
        environment: &GlobalEnvironment,
        context: &mut ProgramContext,
        computation: ComputationTerm,
    ) -> Result<ComputationType, String> {
        let arena = environment.crate_env.arena();
        match arena.get(computation) {
            ComputationTermNode::DefinitionInstance {
                definition,
                parameters,
            } => {
                let DefinedConstant::ProgramComputation { ty, .. } =
                    environment.crate_env.definition(definition)
                else {
                    return Err("wrong Program associated item category".into());
                };
                Ok(
                    crate::raw::program_definitions::instantiate_computation_type(
                        arena,
                        *ty,
                        &parameters,
                        0,
                    ),
                )
            }
            ComputationTermNode::Meta {
                metavariable,
                spine,
            } => {
                let ty = self.infer_meta_type(
                    environment,
                    metavariable,
                    &spine,
                    context,
                    Term::Computation(computation),
                );
                let Term::ComputationType(ty) = ty else {
                    unreachable!()
                };
                Ok(ty)
            }
            ComputationTermNode::DefinedConstant(_) => {
                self.infer_kernel_computation(environment, context, computation)
            }
            ComputationTermNode::Return { value } => {
                let value_ty = self.infer_value_term(environment, context, value)?;
                Ok(arena.alloc(ComputationTypeNode::Return { value_ty }))
            }
            ComputationTermNode::Force { value } => {
                let value_ty = self.infer_value_term(environment, context, value)?;
                let value_ty = self.zonk_value_type(environment, value_ty);
                let ValueTypeNode::Thunk { computation_ty } = arena.get(value_ty) else {
                    return Err("forced Program value is not a thunk".into());
                };
                Ok(computation_ty)
            }
            ComputationTermNode::Lambda {
                var,
                value_ty,
                body,
            } => {
                let value_ty = self.zonk_value_type(environment, value_ty);
                context.push(ProgramContextEntry::ValueTerm { var, ty: value_ty });
                let body_ty = self.infer_computation_term(environment, context, body);
                context.pop();
                Ok(arena.alloc(ComputationTypeNode::Function {
                    domain: value_ty,
                    codomain: strengthen_computation_type(arena, body_ty?, 0)
                        .ok_or("Program result type depends on a local value")?,
                }))
            }
            ComputationTermNode::Application { computation, value } => {
                let function_ty = self.infer_computation_term(environment, context, computation)?;
                let function_ty = self.zonk_computation_type(environment, function_ty);
                let ComputationTypeNode::Function { domain, codomain } = arena.get(function_ty)
                else {
                    return Err("Program computation application head is not a function".into());
                };
                self.solve_value(environment, context, value, domain)?;
                Ok(codomain)
            }
            ComputationTermNode::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => {
                self.solve_value(environment, context, value, value_ty)?;
                let value_ty = self.zonk_value_type(environment, value_ty);
                context.push(ProgramContextEntry::ValueTerm { var, ty: value_ty });
                let result = self.infer_computation_term(environment, context, body);
                context.pop();
                strengthen_computation_type(arena, result?, 0)
                    .ok_or_else(|| "Program result type depends on a local value".into())
            }
            ComputationTermNode::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => {
                let first_ty = self.infer_computation_term(environment, context, computation)?;
                let first_ty = self.zonk_computation_type(environment, first_ty);
                let ComputationTypeNode::Return { value_ty: returned } = arena.get(first_ty) else {
                    return Err("Program sequence head does not return a value".into());
                };
                self.unify_value_types(environment, value_ty, returned)?;
                let value_ty = self.zonk_value_type(environment, value_ty);
                context.push(ProgramContextEntry::ValueTerm { var, ty: value_ty });
                let result = self.infer_computation_term(environment, context, body);
                context.pop();
                let mut result = result?;
                result = strengthen_computation_type(arena, result, 0)
                    .ok_or("Program result type depends on a local value")?;
                Ok(result)
            }
            _ => self.infer_kernel_computation(
                environment,
                context,
                self.zonk_computation(environment, computation),
            ),
        }
    }

    pub(crate) fn check_value_term_with_metas(
        &mut self,
        environment: &GlobalEnvironment,
        value: ValueTerm,
        expected: ValueType,
    ) -> Result<(ValueTerm, ValueType), ElaborationError> {
        let mut context = self.context.clone();
        self.solve_value(environment, &mut context, value, expected)
            .map_err(|message| self.solver_error(environment, message))?;
        self.finish_program_metas(environment)?;
        Ok((
            self.zonk_value(environment, value),
            self.zonk_value_type(environment, expected),
        ))
    }

    pub(crate) fn check_computation_term_with_metas(
        &mut self,
        environment: &GlobalEnvironment,
        computation: ComputationTerm,
        expected: ComputationType,
    ) -> Result<(ComputationTerm, ComputationType), ElaborationError> {
        let mut context = self.context.clone();
        self.solve_computation(environment, &mut context, computation, expected)
            .map_err(|message| self.solver_error(environment, message))?;
        self.finish_program_metas(environment)?;
        Ok((
            self.zonk_computation(environment, computation),
            self.zonk_computation_type(environment, expected),
        ))
    }

    pub(crate) fn infer_value_term_with_metas(
        &mut self,
        environment: &GlobalEnvironment,
        value: ValueTerm,
    ) -> Result<(ValueTerm, ValueType), ElaborationError> {
        let mut context = self.context.clone();
        let ty = self
            .infer_value_term(environment, &mut context, value)
            .map_err(|message| self.solver_error(environment, message))?;
        self.finish_program_metas(environment)?;
        Ok((
            self.zonk_value(environment, value),
            self.zonk_value_type(environment, ty),
        ))
    }

    pub(crate) fn infer_computation_term_with_metas(
        &mut self,
        environment: &GlobalEnvironment,
        computation: ComputationTerm,
    ) -> Result<(ComputationTerm, ComputationType), ElaborationError> {
        let mut context = self.context.clone();
        let ty = self
            .infer_computation_term(environment, &mut context, computation)
            .map_err(|message| self.solver_error(environment, message))?;
        self.finish_program_metas(environment)?;
        Ok((
            self.zonk_computation(environment, computation),
            self.zonk_computation_type(environment, ty),
        ))
    }
}

fn context_symbol(entry: &ProgramContextEntry) -> SymbolId {
    match entry {
        ProgramContextEntry::ValueType { var } | ProgramContextEntry::ValueTerm { var, .. } => *var,
    }
}
fn spine(arena: &Arena, context: &ProgramContext) -> Vec<ProgramArgument> {
    context
        .iter()
        .enumerate()
        .map(|(position, entry)| {
            let index = context.len() - position - 1;
            match entry {
                ProgramContextEntry::ValueType { .. } => {
                    ProgramArgument::ValueType(arena.value_type_bound(index))
                }
                ProgramContextEntry::ValueTerm { .. } => {
                    ProgramArgument::ValueTerm(arena.value_bound(index))
                }
            }
        })
        .collect()
}
fn argument_term(argument: ProgramArgument) -> Term {
    match argument {
        ProgramArgument::ValueType(ty) => Term::ValueType(ty),
        ProgramArgument::ValueTerm(value) => Term::Value(value),
    }
}
fn occurrence(arena: &Arena, term: Term) -> Option<(MetaVarId, Vec<ProgramArgument>)> {
    match term {
        Term::ValueType(ty) => match arena.get(ty) {
            ValueTypeNode::Meta {
                metavariable,
                spine,
            } => Some((metavariable, spine)),
            _ => None,
        },
        Term::ComputationType(ty) => match arena.get(ty) {
            ComputationTypeNode::Meta {
                metavariable,
                spine,
            } => Some((metavariable, spine)),
            _ => None,
        },
        Term::Value(value) => match arena.get(value) {
            ValueTermNode::Meta {
                metavariable,
                spine,
            } => Some((metavariable, spine)),
            _ => None,
        },
        Term::Computation(value) => match arena.get(value) {
            ComputationTermNode::Meta {
                metavariable,
                spine,
            } => Some((metavariable, spine)),
            _ => None,
        },
        Term::Logical(_) => None,
    }
}
fn bound(arena: &Arena, term: Term) -> Option<usize> {
    match term {
        Term::ValueType(ty) => match arena.get(ty) {
            ValueTypeNode::Bound(index) => Some(index),
            _ => None,
        },
        Term::Value(value) => match arena.get(value) {
            ValueTermNode::Bound(index) => Some(index),
            _ => None,
        },
        _ => None,
    }
}
fn reindex(arena: &Arena, term: Term, index: usize) -> Term {
    match term {
        Term::ValueType(_) => Term::ValueType(arena.value_type_bound(index)),
        Term::Value(_) => Term::Value(arena.value_bound(index)),
        _ => unreachable!(),
    }
}
pub(super) fn metas(arena: &Arena, term: Term) -> HashSet<MetaVarId> {
    let mut result = HashSet::new();
    term.walk(arena, 0, &mut |term, _| {
        if let Some((id, _)) = occurrence(arena, term) {
            result.insert(id);
        }
        None
    });
    result
}
fn print_term(printer: &Printer<'_>, term: Term) -> String {
    match term {
        Term::Logical(term) => printer.format_exp(term),
        Term::ValueType(ty) => printer.format_value_type(ty),
        Term::ComputationType(ty) => printer.format_computation_type(ty),
        Term::Value(value) => printer.format_value(value),
        Term::Computation(value) => printer.format_computation(value),
    }
}

impl ProgramScope {
    pub(super) fn fresh_meta(
        &mut self,
        environment: &GlobalEnvironment,
        flavor: SurfaceMeta,
        span: SourceSpan,
        category: MetaCategory,
    ) -> Result<(MetaVarId, Vec<ProgramArgument>), String> {
        let arguments = spine(environment.crate_env.arena(), &self.context);
        if let SurfaceMeta::Named(number) = flavor
            && let Some(id) = self.named_metas.get(&number).copied()
        {
            let existing = &self.metas[id.index()];
            if existing.category != category {
                return Err(format!(
                    "metavariable _{number} is used in two syntactic categories"
                ));
            }
            let common = existing
                .context
                .iter()
                .zip(&self.context)
                .take_while(|(a, b)| context_symbol(a) == context_symbol(b))
                .count();
            // Rebase both a previously inferred type and a solution before
            // shrinking the scope. A escaping local is an actual contradiction.
            let old_spine = spine(environment.crate_env.arena(), &existing.context);
            let solution = existing
                .solution
                .map(|term| self.abstract_term(environment, term, &old_spine, common))
                .transpose()?;
            let expected = existing
                .expected
                .map(|term| self.abstract_term(environment, term, &old_spine, common))
                .transpose()?;
            let existing = &mut self.metas[id.index()];
            existing.context.truncate(common);
            existing.solution = solution;
            existing.expected = expected;
            existing.occurrences.push(span);
            return Ok((id, arguments));
        }
        let id = MetaVarId(
            self.metas
                .len()
                .try_into()
                .expect("Program metavariable table exceeded u32::MAX"),
        );
        self.metas.push(ProgramMeta {
            flavor: flavor.into(),
            span,
            occurrences: vec![span],
            category,
            context: self.context.clone(),
            solution: None,
            expected: None,
        });
        if let SurfaceMeta::Named(number) = flavor {
            self.named_metas.insert(number, id);
        }
        Ok((id, arguments))
    }

    fn instantiate(
        &self,
        environment: &GlobalEnvironment,
        term: Term,
        arguments: &[ProgramArgument],
        scope: usize,
    ) -> Term {
        let arena = environment.crate_env.arena();
        term.walk(arena, 0, &mut |term, depth| {
            let index = bound(arena, term)?;
            if index < depth {
                return Some(term);
            }
            let slot = scope
                .checked_sub(index - depth + 1)
                .expect("metavariable solution escaped its scope");
            Some(argument_term(arguments[slot]).shift(arena, depth, 0))
        })
    }

    fn abstract_term(
        &self,
        environment: &GlobalEnvironment,
        term: Term,
        arguments: &[ProgramArgument],
        scope: usize,
    ) -> Result<Term, String> {
        let arena = environment.crate_env.arena();
        let term = self.zonk_term(environment, term);
        let mut escaped = false;
        let result = term.walk(arena, 0, &mut |term, depth| {
            let index = bound(arena, term)?;
            if index < depth {
                return Some(term);
            }
            let slot = arguments[..scope]
                .iter()
                .position(|argument| bound(arena, argument_term(*argument)) == Some(index - depth));
            match slot {
                Some(slot) => Some(reindex(arena, term, depth + scope - slot - 1)),
                None => {
                    escaped = true;
                    Some(term)
                }
            }
        });
        if escaped {
            Err("metavariable solution captures a variable outside its shared context".into())
        } else {
            Ok(result)
        }
    }

    fn zonk_term(&self, environment: &GlobalEnvironment, term: Term) -> Term {
        let arena = environment.crate_env.arena();
        term.walk(arena, 0, &mut |term, _| {
            let (id, arguments) = occurrence(arena, term)?;
            let meta = &self.metas[id.index()];
            let solution = meta.solution?;
            Some(self.zonk_term(
                environment,
                self.instantiate(environment, solution, &arguments, meta.context.len()),
            ))
        })
    }

    fn assign(
        &mut self,
        environment: &GlobalEnvironment,
        id: MetaVarId,
        arguments: &[ProgramArgument],
        value: Term,
    ) -> Result<(), String> {
        let value = self.zonk_term(environment, value);
        if metas(environment.crate_env.arena(), value).contains(&id) {
            return Err(format!(
                "occurs check failed for {}",
                self.metas[id.index()].flavor.display_name(id)
            ));
        }
        let value = self.abstract_term(
            environment,
            value,
            arguments,
            self.metas[id.index()].context.len(),
        )?;
        self.metas[id.index()].solution = Some(value);
        Ok(())
    }

    fn expect_meta(
        &mut self,
        environment: &GlobalEnvironment,
        id: MetaVarId,
        arguments: &[ProgramArgument],
        term: Term,
        expected: Term,
    ) -> Result<(), String> {
        self.record_constraint(environment, ProgramConstraint::HasType(term, expected));
        let expected = self.abstract_term(
            environment,
            expected,
            arguments,
            self.metas[id.index()].context.len(),
        )?;
        if let Some(previous) = self.metas[id.index()].expected {
            match (previous, expected) {
                (Term::ValueType(left), Term::ValueType(right)) => {
                    self.unify_value_types(environment, left, right)?
                }
                (Term::ComputationType(left), Term::ComputationType(right)) => {
                    self.unify_computation_types(environment, left, right)?
                }
                _ => unreachable!(),
            }
        } else {
            self.metas[id.index()].expected = Some(expected);
        }
        Ok(())
    }

    fn infer_meta_type(
        &mut self,
        environment: &GlobalEnvironment,
        id: MetaVarId,
        arguments: &[ProgramArgument],
        _context: &ProgramContext,
        term: Term,
    ) -> Term {
        if let Some(expected) = self.metas[id.index()].expected {
            return self.instantiate(
                environment,
                expected,
                arguments,
                self.metas[id.index()].context.len(),
            );
        }
        let arena = environment.crate_env.arena();
        let category = match self.metas[id.index()].category {
            MetaCategory::ValueTerm => MetaCategory::ValueType,
            MetaCategory::ComputationTerm => MetaCategory::ComputationType,
            _ => unreachable!(),
        };
        let synthetic = MetaVarId(
            self.metas
                .len()
                .try_into()
                .expect("Program metavariable table exceeded u32::MAX"),
        );
        let context = self.metas[id.index()].context.clone();
        let span = self.metas[id.index()].span;
        let expected = match category {
            MetaCategory::ValueType => Term::ValueType(arena.alloc(ValueTypeNode::Meta {
                metavariable: synthetic,
                spine: spine(arena, &context),
            })),
            MetaCategory::ComputationType => {
                Term::ComputationType(arena.alloc(ComputationTypeNode::Meta {
                    metavariable: synthetic,
                    spine: spine(arena, &context),
                }))
            }
            _ => unreachable!(),
        };
        self.metas.push(ProgramMeta {
            flavor: MetaFlavor::Synthetic,
            span,
            occurrences: vec![span],
            category,
            context,
            solution: None,
            expected: None,
        });
        self.metas[id.index()].expected = Some(expected);
        let expected = self.instantiate(
            environment,
            expected,
            arguments,
            self.metas[id.index()].context.len(),
        );
        self.record_constraint(environment, ProgramConstraint::HasType(term, expected));
        expected
    }

    fn record_constraint(
        &mut self,
        environment: &GlobalEnvironment,
        constraint: ProgramConstraint,
    ) -> usize {
        let mut origins = self.origins.clone();
        let (left, right) = match constraint {
            ProgramConstraint::Equal(a, b) | ProgramConstraint::HasType(a, b) => (a, b),
        };
        for id in metas(environment.crate_env.arena(), left)
            .into_iter()
            .chain(metas(environment.crate_env.arena(), right))
        {
            origins.extend(self.metas[id.index()].occurrences.iter().copied());
        }
        origins.sort_by_key(|span| (span.start, span.end));
        origins.dedup();
        let index = self.constraints.len();
        self.constraints.push(ProgramConstraintRecord {
            constraint,
            status: ConstraintStatus::Residual,
            origins,
        });
        index
    }

    fn constraint_diagnostic(
        &self,
        environment: &GlobalEnvironment,
        record: &ProgramConstraintRecord,
    ) -> ConstraintDiagnostic {
        let names = |id: MetaVarId| self.metas[id.index()].flavor.display_name(id);
        let printer = Printer::new(&environment.crate_env, &names);
        let (left, relation, right) = match record.constraint {
            ProgramConstraint::Equal(left, right) => (left, "≡", right),
            ProgramConstraint::HasType(left, right) => (left, ":", right),
        };
        let render = |a, b| {
            format!(
                "{} {relation} {}",
                print_term(&printer, a),
                print_term(&printer, b)
            )
        };
        ConstraintDiagnostic {
            original: render(left, right),
            normalized: render(
                self.zonk_term(environment, left),
                self.zonk_term(environment, right),
            ),
            status: record.status,
            origins: record.origins.clone(),
        }
    }

    fn goals(&self, environment: &GlobalEnvironment) -> Vec<MetaGoal> {
        let arena = environment.crate_env.arena();
        let names = |id: MetaVarId| self.metas[id.index()].flavor.display_name(id);
        let printer = Printer::new(&environment.crate_env, &names);
        self.metas
            .iter()
            .enumerate()
            .filter_map(|(index, meta)| {
                let id = MetaVarId(index as u32);
                let solution = meta.solution.map(|term| self.zonk_term(environment, term));
                let solved = solution.is_some_and(|term| metas(arena, term).is_empty());
                if meta.flavor == MetaFlavor::Synthetic
                    || (solved && meta.flavor != MetaFlavor::Goal)
                {
                    return None;
                }
                let expected = meta.expected.map(|term| self.zonk_term(environment, term));
                let mut dependencies: Vec<_> = expected
                    .into_iter()
                    .chain(solution)
                    .flat_map(|term| metas(arena, term))
                    .filter(|other| *other != id)
                    .collect();
                dependencies.sort_by_key(|id| id.0);
                dependencies.dedup();
                let state = if solved {
                    MetaState::Solved
                } else if dependencies.is_empty() {
                    MetaState::InsufficientInformation
                } else {
                    MetaState::Waiting
                };
                let local_context = meta
                    .context
                    .iter()
                    .map(|entry| match entry {
                        ProgramContextEntry::ValueType { var } => {
                            format!("{}: \\VType", environment.crate_env.symbol(*var))
                        }
                        ProgramContextEntry::ValueTerm { var, ty } => format!(
                            "{}: {}",
                            environment.crate_env.symbol(*var),
                            printer.format_value_type(self.zonk_value_type(environment, *ty))
                        ),
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                let mut module_context = Vec::new();
                let mut module = Some(environment.module_manager.current());
                while let Some(id) = module {
                    let current = environment.crate_env.module(id);
                    for parameter in current.parameters() {
                        let name = environment.crate_env.symbol(parameter.name);
                        let ty = match parameter.kind {
                            crate::raw::environment::ModuleParameterKind::ProgramType => {
                                "\\VType".to_string()
                            }
                            crate::raw::environment::ModuleParameterKind::ProgramValue { ty } => {
                                printer.format_value_type(ty)
                            }
                            crate::raw::environment::ModuleParameterKind::Pts { ty } => {
                                printer.format_exp(ty)
                            }
                        };
                        module_context.push(format!("{name}: {ty}"));
                    }
                    module = current.parent();
                }
                if !local_context.is_empty() {
                    module_context.push(local_context);
                }
                let context = module_context.join(", ");
                let expected =
                    expected.map(|term| print_term(&printer, term)).or_else(|| {
                        match meta.category {
                            MetaCategory::ValueType => Some("\\VType".into()),
                            MetaCategory::ComputationType => Some("\\CType".into()),
                            _ => None,
                        }
                    });
                Some(MetaGoal {
                    metavariable: id,
                    flavor: meta.flavor,
                    span: meta.span,
                    occurrences: meta.occurrences.clone(),
                    context,
                    principal: expected.map(|expected| format!("{} : {expected}", names(id))),
                    solution: solution.map(|term| print_term(&printer, term)),
                    state,
                    dependencies,
                    constraints: self
                        .constraints
                        .iter()
                        .filter(|record| {
                            record
                                .origins
                                .iter()
                                .any(|span| meta.occurrences.contains(span))
                        })
                        .map(|record| self.constraint_diagnostic(environment, record))
                        .collect(),
                })
            })
            .collect()
    }

    fn solver_error(&self, environment: &GlobalEnvironment, message: String) -> ElaborationError {
        let mut goals = self.goals(environment);
        let state = if self
            .constraints
            .iter()
            .any(|record| record.status == ConstraintStatus::Failed)
        {
            MetaState::Contradiction
        } else {
            MetaState::Unsupported
        };
        for goal in &mut goals {
            if goal.state != MetaState::Solved {
                goal.state = state;
            }
        }
        ElaborationError::ConstraintFailure {
            message,
            constraints: self
                .constraints
                .iter()
                .map(|record| self.constraint_diagnostic(environment, record))
                .collect(),
            goals,
        }
    }

    pub(super) fn finish_program_metas(
        &self,
        environment: &GlobalEnvironment,
    ) -> Result<(), ElaborationError> {
        let goals = self.goals(environment);
        if goals.is_empty() {
            Ok(())
        } else {
            Err(ElaborationError::Metavariables(goals))
        }
    }
}

impl ProgramScope {
    pub(super) fn zonk_value_type(
        &self,
        environment: &GlobalEnvironment,
        value: ValueType,
    ) -> ValueType {
        let Term::ValueType(value) = self.zonk_term(environment, Term::ValueType(value)) else {
            unreachable!()
        };
        value
    }
    pub(super) fn zonk_computation_type(
        &self,
        environment: &GlobalEnvironment,
        value: ComputationType,
    ) -> ComputationType {
        let Term::ComputationType(value) =
            self.zonk_term(environment, Term::ComputationType(value))
        else {
            unreachable!()
        };
        value
    }
    pub(super) fn zonk_value(
        &self,
        environment: &GlobalEnvironment,
        value: ValueTerm,
    ) -> ValueTerm {
        let Term::Value(value) = self.zonk_term(environment, Term::Value(value)) else {
            unreachable!()
        };
        value
    }
    pub(super) fn zonk_computation(
        &self,
        environment: &GlobalEnvironment,
        value: ComputationTerm,
    ) -> ComputationTerm {
        let Term::Computation(value) = self.zonk_term(environment, Term::Computation(value)) else {
            unreachable!()
        };
        value
    }
    pub(super) fn resolve_value_type_head(
        &self,
        environment: &GlobalEnvironment,
        value: ValueType,
    ) -> ValueType {
        self.zonk_value_type(environment, value)
    }
    pub(super) fn resolve_computation_type_head(
        &self,
        environment: &GlobalEnvironment,
        value: ComputationType,
    ) -> ComputationType {
        self.zonk_computation_type(environment, value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shared_solution_is_rebased_between_sibling_contexts() {
        let mut environment = GlobalEnvironment::default();
        let a = environment.crate_env.intern("A");
        let x = environment.crate_env.intern("x");
        let y = environment.crate_env.intern("y");
        let mut scope = ProgramScope::new();
        scope.push_type(a);
        scope.push_value(x, environment.crate_env.arena().value_type_bound(0));
        let (id, first_spine) = scope
            .fresh_meta(
                &environment,
                SurfaceMeta::Named(4),
                SourceSpan { start: 1, end: 3 },
                MetaCategory::ValueType,
            )
            .unwrap();
        scope
            .assign(
                &environment,
                id,
                &first_spine,
                Term::ValueType(environment.crate_env.arena().value_type_bound(1)),
            )
            .unwrap();
        scope.truncate(1);
        scope.push_value(y, environment.crate_env.arena().value_type_bound(0));
        let (same, second_spine) = scope
            .fresh_meta(
                &environment,
                SurfaceMeta::Named(4),
                SourceSpan { start: 8, end: 10 },
                MetaCategory::ValueType,
            )
            .unwrap();
        assert_eq!(id, same);
        assert_eq!(scope.metas[id.index()].context.len(), 1);
        let occurrence = environment.crate_env.arena().alloc(ValueTypeNode::Meta {
            metavariable: id,
            spine: second_spine,
        });
        assert!(matches!(
            environment
                .crate_env
                .arena()
                .get(scope.zonk_value_type(&environment, occurrence)),
            ValueTypeNode::Bound(1)
        ));
    }

    #[test]
    fn a_solution_cannot_capture_a_sibling_type_binder() {
        let mut environment = GlobalEnvironment::default();
        let a = environment.crate_env.intern("A");
        let b = environment.crate_env.intern("B");
        let mut scope = ProgramScope::new();
        scope.push_type(a);
        let (id, arguments) = scope
            .fresh_meta(
                &environment,
                SurfaceMeta::Named(4),
                SourceSpan::default(),
                MetaCategory::ValueType,
            )
            .unwrap();
        scope
            .assign(
                &environment,
                id,
                &arguments,
                Term::ValueType(environment.crate_env.arena().value_type_bound(0)),
            )
            .unwrap();
        scope.truncate(0);
        scope.push_type(b);
        let error = scope
            .fresh_meta(
                &environment,
                SurfaceMeta::Named(4),
                SourceSpan::default(),
                MetaCategory::ValueType,
            )
            .unwrap_err();
        assert!(error.contains("outside its shared context"), "{error}");
    }
}
