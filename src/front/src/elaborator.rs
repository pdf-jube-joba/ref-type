use crate::macros::MacroKind;
use crate::{
    elaborator::{module_manager::ItemAccessResult, term_elaborator::LocalScope},
    log_msg, log_record,
    logger::{LogLevel, LogPayload, Logger},
    metavariables::{ElaborationError, MetaStore},
    syntax::*,
};
use kernel::{
    calculus::{exp_contains_inductive, exp_subst_map},
    derivation::CheckSession,
    environment::{
        CrateEnv, DefinedConstant, DefinitionKind, ModuleParameter, ModuleParameterKind,
    },
    exp::*,
    ids::*,
    inductive::{CtorBinder, InductiveTypeSpecs},
    program_derivation::ProgramCheckSession,
    program_inductive::{ProgramConstructorSpec, ProgramInductiveTypeSpecs},
    sort::Sort,
};
use std::cell::RefCell;

pub mod module_manager;
pub mod program_term_elaborator;
pub mod term_elaborator;

// do type checking
#[derive(Default)]
pub struct GlobalEnvironment {
    crate_env: CrateEnv,
    logger: Logger, // to pass to elaborator
    module_manager: module_manager::ModuleManager,
    metavariables: MetaStore,
}

impl term_elaborator::Handler for GlobalEnvironment {
    fn env(&self) -> &CrateEnv {
        &self.crate_env
    }

    fn arena(&self) -> &Arena {
        self.crate_env.arena()
    }

    fn current_module(&self) -> ModuleId {
        self.module_manager.current()
    }

    fn module_context(&self) -> ExpContext {
        self.module_manager.current_context(&self.crate_env)
    }

    fn intern(&mut self, name: &str) -> SymbolId {
        self.crate_env.intern(name)
    }

    fn symbol(&self, symbol: SymbolId) -> &str {
        self.crate_env.symbol(symbol)
    }

    fn fresh_meta(
        &mut self,
        kind: SurfaceMeta,
        span: SourceSpan,
        local_context: &ExpContext,
    ) -> Exp {
        let mut context = self.module_manager.current_context(&self.crate_env);
        context.extend(local_context.iter().cloned());
        self.metavariables
            .fresh(&self.crate_env, kind, span, &context, local_context.len())
    }

    fn expand_math_macro(
        &mut self,
        tokens: &[MacroExp],
        scope: Option<ModuleId>,
        depth: u16,
        max_order: Option<u64>,
    ) -> Result<SExp, String> {
        self.module_manager.expand_math_macro(
            &self.crate_env,
            scope.unwrap_or_else(|| self.module_manager.current()),
            tokens,
            depth,
            max_order,
        )
    }

    fn expand_named_macro(
        &mut self,
        name: &Identifier,
        tokens: &[MacroExp],
        scope: Option<ModuleId>,
        depth: u16,
        max_order: Option<u64>,
    ) -> Result<SExp, String> {
        self.module_manager.expand_named_macro(
            &self.crate_env,
            scope.unwrap_or_else(|| self.module_manager.current()),
            name,
            tokens,
            depth,
            max_order,
        )
    }

    fn get_item_from_access_path(
        &mut self,
        access_path: &LocalAccess,
    ) -> Result<ItemAccessResult, String> {
        self.module_manager
            .get_item(&self.crate_env, access_path)
            .ok_or("Failed to access item at path".to_string())
    }

    fn field_projection(&mut self, e: Exp, field_name: &Identifier) -> Result<Exp, String> {
        log_record!(
            self.logger,
            LogLevel::Debug,
            ["field projection"],
            LogPayload::Exp(e),
            "field projection {} called",
            field_name.as_str(),
        );

        let mut ctx = self.module_manager.current_context(&self.crate_env);

        let infer_type_e = self
            .logger
            .infer(&self.crate_env, self.module_manager.current(), &mut ctx, e)
            .ok_or("Failed to infer type of expression for field projection".to_string())?;

        log_record!(
            self.logger,
            LogLevel::Debug,
            ["field projection"],
            LogPayload::Exp(infer_type_e),
            "inferred type",
        );

        let ExpNode::IndType {
            indspec,
            parameters,
        } = self.crate_env.arena().get(infer_type_e)
        else {
            return Err("Expected inductive type for field projection".to_string());
        };

        let record = self
            .module_manager
            .get_moditem_record(&self.crate_env, indspec)
            .ok_or("Inductive type is not a record type".to_string())?;

        let Some(exp) = record.field_projection(&self.crate_env, e, field_name, &parameters) else {
            return Err(format!("Field {} not found in record", field_name.as_str()));
        };

        Ok(exp)
    }

    fn infer(&mut self, local_ctx: &mut ExpContext, e: Exp) -> Result<Exp, String> {
        let mut ctx = self.module_manager.current_context(&self.crate_env);
        let module_context_len = ctx.len();
        ctx.append(local_ctx);
        let result = if self.metavariables.contains_unsolved(&self.crate_env, e) {
            self.metavariables.infer_pts(
                &self.crate_env,
                self.module_manager.current(),
                &mut ctx,
                e,
            )
        } else {
            self.logger
                .infer(&self.crate_env, self.module_manager.current(), &mut ctx, e)
                .ok_or("Failed to infer elaborated Set/Prop expression".to_string())
        };
        *local_ctx = ctx.split_off(module_context_len);
        result
    }

    fn elaborate_program_type(
        &mut self,
        expression: &SExp,
    ) -> Result<kernel::program::ProgramType, String> {
        let mut scope = program_term_elaborator::ProgramScope::from_environment(self);
        if let Ok(value_ty) = ValueTypeExp::try_from(expression.clone()) {
            return scope
                .elaborate_value_type(&value_ty, self)
                .map(kernel::program::ProgramType::Value);
        }
        let computation_ty = ComputationTypeExp::try_from(expression.clone())?;
        scope
            .elaborate_computation_type(&computation_ty, self)
            .map(kernel::program::ProgramType::Computation)
    }

    fn elaborate_program(
        &mut self,
        expression: &SExp,
        ty: kernel::program::ProgramType,
    ) -> Result<kernel::program::Program, String> {
        let mut scope = program_term_elaborator::ProgramScope::from_environment(self);
        match ty {
            kernel::program::ProgramType::Value(_) => {
                let value = ValueExp::try_from(expression.clone())?;
                scope
                    .elaborate_value(&value, self)
                    .map(kernel::program::Program::Value)
            }
            kernel::program::ProgramType::Computation(_) => {
                let computation = ComputationExp::try_from(expression.clone())?;
                scope
                    .elaborate_computation(&computation, self)
                    .map(kernel::program::Program::Computation)
            }
        }
    }
}

impl GlobalEnvironment {
    pub fn arena(&self) -> &Arena {
        self.crate_env.arena()
    }

    pub fn crate_env(&self) -> &CrateEnv {
        &self.crate_env
    }

    pub fn logger(&self) -> &Logger {
        &self.logger
    }

    fn finish_metavariables(&mut self) -> Result<(), ElaborationError> {
        match self.metavariables.finish(&self.crate_env) {
            Ok(()) => Ok(()),
            Err(error) => {
                let goals = match &error {
                    ElaborationError::AmbiguousImplicit(goals)
                    | ElaborationError::UnsolvedGoals(goals) => Some(goals.clone()),
                    _ => None,
                };
                if let Some(goals) = goals {
                    self.logger.record(
                        LogLevel::Error,
                        vec!["metavariable".into(), "goal".into()],
                        error.to_string(),
                        LogPayload::Goals(goals),
                    );
                }
                Err(error)
            }
        }
    }

    /// Infer a Set/Prop term whose surface syntax still contains metavariables.
    fn infer_term_with_metavariables(
        &mut self,
        ctx: &mut ExpContext,
        term: Exp,
    ) -> Result<Exp, String> {
        self.metavariables
            .infer_pts(&self.crate_env, self.module_manager.current(), ctx, term)
    }

    /// Check a term against an expected type containing metavariables without
    /// letting failed judgement-classification probes contaminate later ones.
    fn check_term_with_metavariables(
        &mut self,
        ctx: &mut ExpContext,
        term: Exp,
        expected: Exp,
    ) -> Result<(), String> {
        let expected = self.metavariables.zonk(&self.crate_env, expected);
        if matches!(self.crate_env.arena().get(expected), ExpNode::Meta { .. }) {
            let inferred = self.infer_term_with_metavariables(ctx, term)?;
            self.metavariables
                .unify(&self.crate_env, expected, inferred)?;
            return Ok(());
        }

        self.metavariables.check_pts(
            &self.crate_env,
            self.module_manager.current(),
            ctx,
            term,
            expected,
        )
    }

    fn solve_module_arguments(
        &mut self,
        context: &mut ExpContext,
        back_parent: Option<usize>,
        calls: &mut [(Identifier, Vec<(Identifier, Exp)>)],
    ) -> Result<(), ElaborationError> {
        if self.metavariables.is_empty() {
            return Ok(());
        }
        let mut source = if let Some(back_parent) = back_parent {
            let mut module = self.module_manager.current();
            for _ in 0..back_parent {
                module =
                    self.crate_env.module(module).parent().ok_or_else(|| {
                        ElaborationError::Message("already at root module".into())
                    })?;
            }
            module
        } else {
            self.crate_env.root_module()
        };
        let mut substitutions = Vec::new();
        for (child_name, arguments) in calls.iter_mut() {
            let child = self
                .crate_env
                .module(source)
                .children()
                .iter()
                .copied()
                .find(|child| self.crate_env.module(*child).name() == child_name.as_str())
                .ok_or_else(|| {
                    ElaborationError::Message(format!(
                        "child module '{}' was not found",
                        child_name.as_str()
                    ))
                })?;
            let parameters = self.crate_env.module(child).parameters().to_vec();
            if parameters.len() != arguments.len() {
                return Err(ElaborationError::Message(format!(
                    "module '{}' argument count mismatch",
                    child_name.as_str()
                )));
            }
            for (position, ((argument_name, argument), parameter)) in
                arguments.iter_mut().zip(parameters).enumerate()
            {
                if argument_name.as_str() != self.crate_env.symbol(parameter.name) {
                    return Err(ElaborationError::Message(format!(
                        "module '{}' argument name mismatch",
                        child_name.as_str()
                    )));
                }
                match parameter.kind {
                    ModuleParameterKind::Pts { ty } => {
                        let expected = exp_subst_map(self.crate_env.arena(), ty, &substitutions);
                        self.metavariables
                            .check_pts(
                                &self.crate_env,
                                self.module_manager.current(),
                                context,
                                *argument,
                                expected,
                            )
                            .map_err(|message| self.metavariables.constraint_error(message))?;
                    }
                    ModuleParameterKind::ProgramType | ModuleParameterKind::ProgramValue { .. } => {
                        return Err(ElaborationError::Message(
                            "Program module arguments must use their category-specific syntax"
                                .into(),
                        ));
                    }
                }
                substitutions.push((
                    ModuleParamId {
                        module: child,
                        position: position as u32,
                    },
                    *argument,
                ));
            }
            source = child;
        }
        self.finish_metavariables()?;
        for (_, arguments) in calls {
            for (_, argument) in arguments {
                *argument = self.metavariables.zonk(&self.crate_env, *argument);
            }
        }
        Ok(())
    }
}

#[cfg(any())]
fn reflect_program_type_for_mirror(
    env: &CrateEnv,
    ty: Exp,
    self_inductive: ProgramInductiveId,
    self_reflected: InductiveId,
    parameter_count: usize,
) -> Result<Exp, String> {
    let arena = env.arena();
    let reflect = |child| {
        reflect_program_type_for_mirror(env, child, self_inductive, self_reflected, parameter_count)
    };
    Ok(match arena.get(ty) {
        ExpNode::Bound(_) => ty,
        ExpNode::ThunkType { computation_ty } => reflect(computation_ty)?,
        ExpNode::ReturnType { value_ty } => reflect(value_ty)?,
        ExpNode::ComputationFunction { domain, codomain } => {
            let domain = reflect(domain)?;
            let codomain = kernel::calculus::shift_bound_indices(arena, reflect(codomain)?, 1, 0);
            arena.alloc(ExpNode::Prod {
                var: SymbolId::ANONYMOUS,
                ty: domain,
                body: codomain,
            })
        }
        ExpNode::ProgramIndType {
            indspec,
            parameters,
        } => {
            let reflected = if indspec == self_inductive {
                self_reflected
            } else {
                env.program_inductive(indspec).reflected()
            };
            let parameters = if indspec == self_inductive && parameters.is_empty() {
                (0..parameter_count)
                    .rev()
                    .map(|index| arena.exp_bound(index))
                    .collect()
            } else {
                parameters
                    .into_iter()
                    .map(reflect)
                    .collect::<Result<Vec<_>, _>>()?
            };
            arena.alloc(ExpNode::IndType {
                indspec: reflected,
                parameters,
            })
        }
        ExpNode::ModuleParam(parameter) => arena.alloc(ExpNode::ReflectedProgramParam(parameter)),
        ExpNode::RunStep {
            state_ty,
            result_ty,
        } => arena.alloc(ExpNode::RunStep {
            state_ty: reflect(state_ty)?,
            result_ty: reflect(result_ty)?,
        }),
        _ => {
            return Err("unsupported Program type in reflected datatype field".into());
        }
    })
}

impl GlobalEnvironment {
    pub fn add_new_module_to_root(&mut self, module: &Module) -> Result<(), ElaborationError> {
        log_msg!(
            self.logger,
            LogLevel::Info,
            ["elaborator", "module"],
            "Top level Elaborating module {}",
            module.name.as_str()
        );
        self.module_manager.moveto_root();
        self.module_add_rec(module)?;
        Ok(())
    }

    fn collect_definition_obligations(
        &self,
        context: &mut ExpContext,
        body: Exp,
        ty: Exp,
    ) -> Result<(DefinitionKind, Vec<ProofObligation>), String> {
        let obligations = RefCell::new(Vec::new());
        let mut session = CheckSession::collecting(
            &self.crate_env,
            self.module_manager.current(),
            context,
            &obligations,
        );
        session
            .check_pts(body, ty)
            .map_err(|error| format!("Set/Prop definition check failed: {error:?}"))?;
        Ok((DefinitionKind::Pts, obligations.into_inner()))
    }

    fn elaborate_proof_evidence(
        &mut self,
        proof: Option<&ProofBlock>,
        obligations: &[ProofObligation],
        module_context: &ExpContext,
    ) -> Result<Vec<ProofEvidence>, ElaborationError> {
        let Some(proof) = proof else {
            if obligations.is_empty() {
                return Ok(Vec::new());
            }
            let rules = obligations
                .iter()
                .map(|obligation| obligation.rule)
                .collect::<Vec<_>>()
                .join(", ");
            return Err(format!(
                "missing proof block: {} undischarged obligation(s) from {rules}",
                obligations.len()
            )
            .into());
        };

        let mut evidence = Vec::with_capacity(proof.entries.len());
        for entry in &proof.entries {
            self.metavariables.clear();
            let mut scope = LocalScope::default();
            scope.elab_telescope_bind_in_decl(&entry.binders, self)?;
            let proposition = scope.elab_exp(&entry.proposition, self)?;
            let witness = scope.elab_exp(&entry.witness, self)?;
            let mut evidence_context = module_context.clone();
            evidence_context.extend(scope.typing_context().iter().cloned());

            if !self.metavariables.is_empty() {
                self.check_term_with_metavariables(&mut evidence_context, witness, proposition)
                    .map_err(|message| self.metavariables.constraint_error(message))?;
                self.finish_metavariables()?;
            }
            let proposition = self.metavariables.zonk(&self.crate_env, proposition);
            let witness = self.metavariables.zonk(&self.crate_env, witness);
            for context_entry in &mut evidence_context {
                context_entry.ty = self.metavariables.zonk(&self.crate_env, context_entry.ty);
            }
            evidence.push(ProofEvidence {
                context: evidence_context,
                proposition,
                witness,
            });
        }

        for obligation in obligations {
            let matches = evidence
                .iter()
                .filter(|candidate| {
                    kernel::derivation::evidence_matches_obligation(
                        &self.crate_env,
                        candidate,
                        obligation,
                    )
                })
                .count();
            if matches != 1 {
                return Err(format!(
                    "proof obligation from {} has {matches} matching proof-block entries (expected exactly one)",
                    obligation.rule
                )
                .into());
            }
        }
        for candidate in &evidence {
            if !obligations.iter().any(|obligation| {
                kernel::derivation::evidence_matches_obligation(
                    &self.crate_env,
                    candidate,
                    obligation,
                )
            }) {
                return Err("proof block contains an unused goal".into());
            }
        }
        Ok(evidence)
    }

    fn validate_definition_with_evidence(
        &self,
        context: &mut ExpContext,
        kind: DefinitionKind,
        body: Exp,
        ty: Exp,
        evidence: &[ProofEvidence],
    ) -> Result<(), String> {
        let mut session = CheckSession::with_evidence(
            &self.crate_env,
            self.module_manager.current(),
            context,
            evidence,
        );
        let result = match kind {
            DefinitionKind::Pts => session.check_pts(body, ty),
            DefinitionKind::ProgramValue | DefinitionKind::ProgramComputation => {
                return Err("Program definitions use ProgramCheckSession".into());
            }
        };
        result.map_err(|error| format!("definition proof validation failed: {error:?}"))
    }

    fn collect_inference_obligations(
        &self,
        context: &mut ExpContext,
        exp: Exp,
    ) -> Result<(kernel::exp::ExpJudgement, Vec<ProofObligation>), String> {
        let obligations = RefCell::new(Vec::new());
        let judgement = CheckSession::collecting(
            &self.crate_env,
            self.module_manager.current(),
            context,
            &obligations,
        )
        .infer_exp_judgement(exp)
        .map_err(|error| format!("Set/Prop inference failed: {error:?}"))?;
        Ok((judgement, obligations.into_inner()))
    }

    fn validate_inference_with_evidence(
        &self,
        context: &mut ExpContext,
        exp: Exp,
        _judgement: kernel::exp::ExpJudgement,
        evidence: &[ProofEvidence],
    ) -> Result<(), String> {
        let mut session = CheckSession::with_evidence(
            &self.crate_env,
            self.module_manager.current(),
            context,
            evidence,
        );
        let result = session.infer_pts(exp).map(|_| ());
        result.map_err(|error| format!("proof validation failed: {error:?}"))
    }

    #[cfg(any())]
    fn add_program_inductive_decl(
        &mut self,
        ctx: &mut ExpContext,
        type_name: &Identifier,
        parameters: &[RightBind],
        constructors: &[(Identifier, Vec<RightBind>, SExp)],
        expose_constructors: bool,
    ) -> Result<(), ElaborationError> {
        let module = self.module_manager.current();
        let inductive = self.crate_env.reserve_program_inductive(module);
        let reflected = self.crate_env.reserve_inductive(module);
        let type_name_var = self.crate_env.intern(type_name.as_str());
        let type_name_exp = self.crate_env.arena().alloc(ExpNode::ProgramIndType {
            indspec: inductive,
            parameters: Vec::new(),
        });
        let mut scope = LocalScope::default();
        scope.push_decl_var_exp(type_name_var, type_name_exp);

        let mut parameter_names = Vec::new();
        for RightBind { vars, ty } in parameters {
            if !matches!(ty.as_ref(), SExp::ValueType) {
                return Err("Program datatype parameters must have type \\VType".into());
            }
            for var in vars {
                let symbol = self.crate_env.intern(var.as_str());
                parameter_names.push(symbol);
                scope.push_program_type_decl_var(symbol);
            }
        }

        let mut constructor_names = Vec::with_capacity(constructors.len());
        let mut constructor_specs = Vec::with_capacity(constructors.len());
        for (constructor_name, fields, result) in constructors {
            constructor_names.push(constructor_name.clone());
            let mut elaborated_fields = Vec::new();
            for RightBind { vars, ty } in fields {
                if matches!(ty.as_ref(), SExp::ValueType) {
                    return Err("Program constructor fields must be value types".into());
                }
                let mut field_ty = scope.elab_exp(ty, self)?;
                if self
                    .metavariables
                    .contains_unsolved(&self.crate_env, field_ty)
                {
                    let mut meta_context = self.module_manager.current_context(&self.crate_env);
                    self.metavariables
                        .check_value_type(
                            &self.crate_env,
                            self.module_manager.current(),
                            &mut meta_context,
                            field_ty,
                        )
                        .map_err(|message| self.metavariables.constraint_error(message))?;
                    self.finish_metavariables()?;
                    field_ty = self.metavariables.zonk(&self.crate_env, field_ty);
                }
                if vars.is_empty() {
                    elaborated_fields.push((SymbolId::ANONYMOUS, field_ty));
                    scope.push_program_value_decl_var(SymbolId::ANONYMOUS, field_ty);
                } else {
                    for var in vars {
                        let field_name = self.crate_env.intern(var.as_str());
                        elaborated_fields.push((field_name, field_ty));
                        scope.push_program_value_decl_var(field_name, field_ty);
                    }
                }
            }
            let result = scope.elab_exp(result, self)?;
            if !matches!(
                self.crate_env.arena().get(result),
                ExpNode::ProgramIndType { indspec, parameters } if indspec == inductive && parameters.is_empty()
            ) {
                return Err(format!(
                    "Program constructor {} must return {}",
                    constructor_name.as_str(),
                    type_name.as_str()
                )
                .into());
            }
            constructor_specs.push(ProgramConstructorSpec::new(elaborated_fields));
        }

        let reflected_parameters = parameter_names
            .iter()
            .map(|name| (*name, self.crate_env.arena().sort(Sort::Set(0))))
            .collect::<Vec<_>>();
        let reflected_constructors = constructor_specs
            .iter()
            .map(|constructor| {
                let telescope = constructor
                    .fields()
                    .iter()
                    .map(|(name, ty)| {
                        reflect_program_type_for_mirror(
                            &self.crate_env,
                            *ty,
                            inductive,
                            reflected,
                            parameter_names.len(),
                        )
                        .and_then(|ty| {
                            if !exp_contains_inductive(self.crate_env.arena(), ty, reflected) {
                                return Ok(CtorBinder::Simple((*name, ty)));
                            }
                            let (binders, tail) =
                                kernel::utils::decompose_prod(self.crate_env.arena(), ty);
                            let (head, self_indices) =
                                kernel::utils::decompose_app(self.crate_env.arena(), tail);
                            if !matches!(
                                self.crate_env.arena().get(head),
                                ExpNode::IndType { indspec, .. } if indspec == reflected
                            ) {
                                return Err(
                                    "reflected recursive field is not strictly positive".into()
                                );
                            }
                            Ok(CtorBinder::StrictPositive {
                                binders,
                                self_indices,
                            })
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(kernel::inductive::CtorType {
                    telescope,
                    indices: Vec::new(),
                })
            })
            .collect::<Result<Vec<_>, String>>()?;

        let program_spec =
            ProgramInductiveTypeSpecs::unchecked(parameter_names, constructor_specs, reflected);
        let reflected_spec = InductiveTypeSpecs::unchecked(
            reflected_parameters,
            Vec::new(),
            Sort::Set(0),
            reflected_constructors,
        );
        self.crate_env
            .define_program_inductive(inductive, program_spec);
        self.crate_env.define_inductive(reflected, reflected_spec);
        self.crate_env
            .program_inductive(inductive)
            .validate(
                &mut CheckSession::new(&self.crate_env, module, ctx),
                inductive,
            )
            .map_err(|error| format!("Ill-formed Program datatype: {error:?}"))?;
        let mut reflected_context = ctx
            .iter()
            .map(|entry| match entry {
                ExpContextEntry { var, ty } => Ok(ExpContextEntry { var: *var, ty: *ty }),
                ExpContextEntry::ProgramType { var } => Ok(ExpContextEntry {
                    var: *var,
                    ty: self.crate_env.arena().sort(Sort::Set(0)),
                }),
                ExpContextEntry::ProgramValue { var, ty } => {
                    kernel::reflection::reflect_type(&self.crate_env, *ty)
                        .map(|ty| ExpContextEntry { var: *var, ty })
                        .map_err(|error| {
                            format!("cannot reflect enclosing Program parameter: {error}")
                        })
                }
            })
            .collect::<Result<ExpContext, String>>()?;
        self.crate_env
            .inductive(reflected)
            .validate(
                &mut CheckSession::new(&self.crate_env, module, &mut reflected_context),
                reflected,
            )
            .map_err(|error| format!("Ill-formed reflected datatype: {error:?}"))?;
        self.module_manager.publish_reserved_program_inductive(
            &mut self.crate_env,
            type_name.clone(),
            if expose_constructors {
                constructor_names
            } else {
                Vec::new()
            },
            inductive,
            reflected,
        )?;
        Ok(())
    }

    fn add_typed_program_inductive_decl(
        &mut self,
        type_name: &Identifier,
        parameters: &[RightBind],
        constructors: &[(Identifier, Vec<RightBind>, SExp)],
        expose_constructors: bool,
    ) -> Result<(), ElaborationError> {
        let module = self.module_manager.current();
        let inductive = self.crate_env.reserve_program_inductive(module);
        let reflected = self.crate_env.reserve_inductive(module);
        let type_name_symbol = self.crate_env.intern(type_name.as_str());
        let self_ty = self
            .crate_env
            .arena()
            .alloc(kernel::program::ValueTypeNode::Inductive {
                indspec: inductive,
                parameters: Vec::new(),
            });
        let mut scope = program_term_elaborator::ProgramScope::from_environment(self);
        scope.bind_value_type_name(type_name_symbol, self_ty);

        let mut parameter_names = Vec::new();
        for RightBind { vars, ty } in parameters {
            if !matches!(ty.as_ref(), SExp::ValueType) {
                return Err("Program datatype parameters must have type \\VType".into());
            }
            for variable in vars {
                let variable = self.crate_env.intern(variable.as_str());
                parameter_names.push(variable);
                scope.push_type(variable);
            }
        }

        let mut constructor_names = Vec::new();
        let mut constructor_specs = Vec::new();
        for (constructor_name, fields, result) in constructors {
            constructor_names.push(constructor_name.clone());
            let field_mark = scope.context().len();
            let mut elaborated_fields = Vec::new();
            for RightBind { vars, ty } in fields {
                let surface_ty: ValueTypeExp = ty.as_ref().clone().try_into()?;
                let field_ty = scope.elaborate_value_type(&surface_ty, self)?;
                if vars.is_empty() {
                    elaborated_fields.push((SymbolId::ANONYMOUS, field_ty));
                    scope.push_value(SymbolId::ANONYMOUS, field_ty);
                } else {
                    for variable in vars {
                        let variable = self.crate_env.intern(variable.as_str());
                        elaborated_fields.push((variable, field_ty));
                        scope.push_value(variable, field_ty);
                    }
                }
            }
            let result: ValueTypeExp = result.clone().try_into()?;
            let result = scope.elaborate_value_type(&result, self)?;
            let kernel::program::ValueTypeNode::Inductive {
                indspec,
                parameters,
            } = self.crate_env.arena().get(result)
            else {
                return Err(format!(
                    "Program constructor {} must return {}",
                    constructor_name.as_str(),
                    type_name.as_str()
                )
                .into());
            };
            if indspec != inductive
                || (!parameters.is_empty() && parameters.len() != parameter_names.len())
            {
                return Err(format!(
                    "Program constructor {} must return {} with all datatype parameters",
                    constructor_name.as_str(),
                    type_name.as_str()
                )
                .into());
            }
            while scope.context().len() > field_mark {
                scope.truncate(field_mark);
            }
            constructor_specs.push(ProgramConstructorSpec::new(elaborated_fields));
        }

        let program_spec = ProgramInductiveTypeSpecs::unchecked(
            parameter_names.clone(),
            constructor_specs,
            reflected,
        );
        self.crate_env
            .define_program_inductive(inductive, program_spec);

        let reflected_parameters = parameter_names
            .iter()
            .map(|name| (*name, self.crate_env.arena().sort(Sort::Set(0))))
            .collect();
        let reflected_constructors = self.crate_env.program_inductive(inductive).constructors().iter().map(|constructor| {
            let telescope = constructor.fields().iter().map(|(name, ty)| {
                let ty = kernel::reflection::reflect_value_type(&self.crate_env, *ty)
                    .map_err(|error| format!("cannot reflect Program constructor field: {error}"))?;
                if !exp_contains_inductive(self.crate_env.arena(), ty, reflected) {
                    return Ok(CtorBinder::Simple((*name, ty)));
                }
                let (binders, tail) = kernel::utils::decompose_prod(self.crate_env.arena(), ty);
                let (head, self_indices) = kernel::utils::decompose_app(self.crate_env.arena(), tail);
                if !matches!(self.crate_env.arena().get(head), ExpNode::IndType { indspec, .. } if indspec == reflected) {
                    return Err("reflected recursive Program field is not strictly positive".to_string());
                }
                Ok(CtorBinder::StrictPositive { binders, self_indices })
            }).collect::<Result<Vec<_>, String>>()?;
            Ok(kernel::inductive::CtorType { telescope, indices: Vec::new() })
        }).collect::<Result<Vec<_>, String>>()?;
        self.crate_env.define_inductive(
            reflected,
            InductiveTypeSpecs::unchecked(
                reflected_parameters,
                Vec::new(),
                Sort::Set(0),
                reflected_constructors,
            ),
        );

        let mut program_context = self.module_manager.current_program_context(&self.crate_env);
        self.crate_env
            .program_inductive(inductive)
            .validate(
                &mut ProgramCheckSession::new(&self.crate_env, module, &mut program_context),
                inductive,
            )
            .map_err(|error| format!("Ill-formed Program datatype: {error:?}"))?;
        let mut reflected_context =
            kernel::reflection::reflect_context(&self.crate_env, &program_context)
                .map_err(|error| format!("cannot reflect Program context: {error}"))?;
        self.crate_env
            .inductive(reflected)
            .validate(
                &mut CheckSession::new(&self.crate_env, module, &mut reflected_context),
                reflected,
            )
            .map_err(|error| format!("Ill-formed reflected datatype: {error:?}"))?;
        self.module_manager.publish_reserved_program_inductive(
            &mut self.crate_env,
            type_name.clone(),
            if expose_constructors {
                constructor_names
            } else {
                Vec::new()
            },
            inductive,
            reflected,
        )?;
        Ok(())
    }

    fn module_add_rec(&mut self, module: &Module) -> Result<(), ElaborationError> {
        log_msg!(
            self.logger,
            LogLevel::Debug,
            ["elaborator", "module"],
            "Elaborating module {}",
            module.name.as_str()
        );

        let Module {
            name,
            parameters,
            body,
        } = module;

        let ModuleBody::Inline(declarations) = body else {
            return Err(format!(
                "External module '{}' was not resolved; use the file loader",
                name.as_str()
            )
            .into());
        };

        // 1. before adding child, check well-typedness ness of parameters
        {
            self.metavariables.clear();
            let reserved_module = self
                .module_manager
                .reserve_child_and_moveto(&mut self.crate_env, name.0.clone());
            let mut ctx = self.module_manager.current_context(&self.crate_env);

            let mut parameter_position = 0_u32;

            let mut local_scope = term_elaborator::LocalScope::default();
            let mut program_scope = program_term_elaborator::ProgramScope::from_environment(self);

            for RightBind { vars, ty } in parameters.iter() {
                let parameter_kind = if matches!(ty.as_ref(), SExp::ValueType) {
                    ModuleParameterKind::ProgramType
                } else if let Ok(mut pts_ty) = local_scope.elab_exp(ty, self) {
                    if !self.metavariables.is_empty() {
                        self.metavariables
                            .infer_sort(
                                &self.crate_env,
                                self.module_manager.current(),
                                &mut ctx,
                                pts_ty,
                            )
                            .map_err(|message| self.metavariables.constraint_error(message))?;
                        self.finish_metavariables()?;
                        pts_ty = self.metavariables.zonk(&self.crate_env, pts_ty);
                    }
                    CheckSession::new(&self.crate_env, self.module_manager.current(), &mut ctx)
                        .infer_sort(pts_ty)
                        .map_err(|error| {
                            format!("Module parameter type is not Set/Prop: {error:?}")
                        })?;
                    ModuleParameterKind::Pts { ty: pts_ty }
                } else {
                    let program_ty: ValueTypeExp = ty.as_ref().clone().try_into()?;
                    let program_ty = program_scope.elaborate_value_type(&program_ty, self)?;
                    let mut program_context = program_scope.context().clone();
                    ProgramCheckSession::new(
                        &self.crate_env,
                        self.module_manager.current(),
                        &mut program_context,
                    )
                    .check_value_type(program_ty)
                    .map_err(|error| {
                        format!("Program module parameter has an ill-formed value type: {error:?}")
                    })?;
                    ModuleParameterKind::ProgramValue { ty: program_ty }
                };

                for v in vars {
                    let symbol = self.crate_env.intern(v.as_str());
                    let position = parameter_position;
                    let parameter_id = ModuleParamId {
                        module: reserved_module,
                        position,
                    };
                    self.crate_env.add_module_parameter(
                        reserved_module,
                        ModuleParameter {
                            name: symbol,
                            kind: parameter_kind,
                        },
                    );
                    parameter_position += 1;
                    match parameter_kind {
                        ModuleParameterKind::Pts { ty } => {
                            ctx.push(ExpContextEntry { var: symbol, ty });
                            local_scope.push_typed_decl_var_exp(
                                symbol,
                                ty,
                                self.crate_env.arena().exp_module_param(parameter_id),
                            );
                        }
                        ModuleParameterKind::ProgramType => program_scope.push_type(symbol),
                        ModuleParameterKind::ProgramValue { ty } => {
                            program_scope.push_value(symbol, ty)
                        }
                    }
                }
            }
        }

        let mut ctx = self.module_manager.current_context(&self.crate_env);

        // 2. elaborate declarations
        for decl in declarations {
            self.metavariables.clear();
            let mut local_scope = LocalScope::default();
            match decl {
                ModuleItem::Definition {
                    owner,
                    name,
                    binders,
                    ty,
                    body,
                    proof,
                } => {
                    self.logger.record(
                        LogLevel::Debug,
                        vec!["elaborator".to_string(), "definition".to_string()],
                        format!("Elaborating definition {}", name.as_str()),
                        LogPayload::Message,
                    );
                    if let Some(owner) = owner {
                        let expected = self
                            .module_manager
                            .associated_parameter_count(&self.crate_env, &owner.type_name)
                            .ok_or_else(|| {
                                format!(
                                    "Associated item owner '{}' is not a type in this module",
                                    owner.type_name.as_str()
                                )
                            })?;
                        let found = owner
                            .parameters
                            .iter()
                            .map(|binder| binder.vars.len())
                            .sum::<usize>();
                        if expected != found {
                            return Err(format!(
                                "Associated definition {}::{} expects {} owner parameter(s), found {}",
                                owner.type_name.as_str(),
                                name.as_str(),
                                expected,
                                found,
                            )
                            .into());
                        }
                    }
                    let mut all_binders = owner
                        .as_ref()
                        .map(|owner| owner.parameters.clone())
                        .unwrap_or_default();
                    all_binders.extend(binders.clone());
                    let mut ty = ty.clone();
                    let mut body = body.clone();
                    for binder in all_binders.into_iter().rev() {
                        ty = SExp::Prod {
                            bind: Bind::Named(binder.clone()),
                            body: Box::new(ty),
                        };
                        body = SExp::Lam {
                            bind: Bind::Named(binder),
                            body: Box::new(body),
                        };
                    }
                    let ty_elab = local_scope.elab_exp(&ty, self)?;
                    let body_elab = local_scope.elab_exp(&body, self)?;
                    if !self.metavariables.is_empty() {
                        self.check_term_with_metavariables(&mut ctx, body_elab, ty_elab)
                            .map_err(|message| self.metavariables.constraint_error(message))?;
                        self.finish_metavariables()?;
                    }
                    let ty_elab = self.metavariables.zonk(&self.crate_env, ty_elab);
                    let body_elab = self.metavariables.zonk(&self.crate_env, body_elab);
                    let module_context = ctx.clone();
                    let (kind, obligations) = self
                        .collect_definition_obligations(&mut ctx, body_elab, ty_elab)
                        .map_err(|message| {
                            format!(
                                "Definition {} body does not check against declared type: {message}",
                                name.as_str()
                            )
                        })?;
                    let evidence = self.elaborate_proof_evidence(
                        proof.as_ref(),
                        &obligations,
                        &module_context,
                    )?;
                    ctx = module_context;
                    self.validate_definition_with_evidence(
                        &mut ctx, kind, body_elab, ty_elab, &evidence,
                    )?;
                    debug_assert_eq!(kind, DefinitionKind::Pts);
                    let defined_constant = DefinedConstant::Pts {
                        ty: ty_elab,
                        body: body_elab,
                    };
                    if let Some(owner) = owner {
                        self.module_manager.add_associated_def(
                            &mut self.crate_env,
                            &owner.type_name,
                            name.clone(),
                            defined_constant,
                        )?;
                    } else {
                        self.module_manager.add_def(
                            &mut self.crate_env,
                            name.clone(),
                            defined_constant,
                        )?;
                    }
                }
                ModuleItem::ValueDefinition {
                    name,
                    binders,
                    ty,
                    body,
                } => {
                    if !binders.is_empty() {
                        return Err("Program definitions do not use Set/Prop product binders; use module parameters or Program computation lambdas".into());
                    }
                    let mut scope = program_term_elaborator::ProgramScope::from_environment(self);
                    let ty = scope.elaborate_value_type(ty, self)?;
                    let body = scope.elaborate_value(body, self)?;
                    let mut program_context = scope.context().clone();
                    ProgramCheckSession::new(
                        &self.crate_env,
                        self.module_manager.current(),
                        &mut program_context,
                    )
                    .check_value(body, ty)
                    .map_err(|error| {
                        format!(
                            "Program value definition {} is ill-typed: {error:?}",
                            name.as_str()
                        )
                    })?;
                    self.module_manager.add_def(
                        &mut self.crate_env,
                        name.clone(),
                        DefinedConstant::ProgramValue { ty, body },
                    )?;
                    self.logger.record(
                        LogLevel::Debug,
                        vec!["elaborator".into(), "program definition".into()],
                        format!("Program value {} elaborated", name.as_str()),
                        LogPayload::ValueType(ty),
                    );
                }
                ModuleItem::ComputationDefinition {
                    name,
                    binders,
                    ty,
                    body,
                } => {
                    if !binders.is_empty() {
                        return Err("Program definitions do not use Set/Prop product binders; use module parameters or Program computation lambdas".into());
                    }
                    let mut scope = program_term_elaborator::ProgramScope::from_environment(self);
                    let ty = scope.elaborate_computation_type(ty, self)?;
                    let body = scope.elaborate_computation(body, self)?;
                    let mut program_context = scope.context().clone();
                    ProgramCheckSession::new(
                        &self.crate_env,
                        self.module_manager.current(),
                        &mut program_context,
                    )
                    .check_computation(body, ty)
                    .map_err(|error| {
                        format!(
                            "Program computation definition {} is ill-typed: {error:?}",
                            name.as_str()
                        )
                    })?;
                    self.module_manager.add_def(
                        &mut self.crate_env,
                        name.clone(),
                        DefinedConstant::ProgramComputation { ty, body },
                    )?;
                    self.logger.record(
                        LogLevel::Debug,
                        vec!["elaborator".into(), "program definition".into()],
                        format!("Program computation {} elaborated", name.as_str()),
                        LogPayload::ComputationType(ty),
                    );
                }
                ModuleItem::Inductive {
                    type_name,
                    parameters,
                    indices,
                    kind,
                    constructors,
                } => {
                    if matches!(kind, InductiveKind::Program) {
                        self.add_typed_program_inductive_decl(
                            type_name,
                            parameters,
                            constructors,
                            true,
                        )?;
                        continue;
                    }
                    let InductiveKind::Pts(sort) = kind else {
                        unreachable!();
                    };
                    let type_name_var = self.crate_env.intern(type_name.as_str());
                    let inductive = self
                        .crate_env
                        .reserve_inductive(self.module_manager.current());
                    let type_name_exp = self.crate_env.arena().alloc(ExpNode::IndType {
                        indspec: inductive,
                        parameters: vec![],
                    });
                    // register type name as binded var
                    local_scope.push_decl_var_exp(type_name_var, type_name_exp);

                    // elaborate parameters and indices
                    // binding is memorized in local scope
                    let mut parameter_elab =
                        local_scope.elab_telescope_bind_in_decl(parameters, self)?;
                    let mut indices_elab =
                        local_scope.elab_telescope_bind_in_decl(indices, self)?;
                    if !self.metavariables.is_empty() {
                        self.finish_metavariables()?;
                        for (_, ty) in &mut parameter_elab {
                            *ty = self.metavariables.zonk(&self.crate_env, *ty);
                        }
                        for (_, ty) in &mut indices_elab {
                            *ty = self.metavariables.zonk(&self.crate_env, *ty);
                        }
                    }

                    // elaborate constructors
                    let mut ctor_names = vec![];
                    let mut ctor_type_elabs = vec![];

                    for (ctor_name, rightbinds, ends) in constructors {
                        ctor_names.push(ctor_name.clone());

                        let (telescope, ends_elab) = {
                            let term = {
                                let mut term: SExp = ends.clone();
                                for bd in rightbinds.iter().rev() {
                                    term = SExp::Prod {
                                        bind: crate::syntax::Bind::Named(bd.clone()),
                                        body: Box::new(term),
                                    };
                                }
                                term
                            };
                            let mut term_elab = local_scope.elab_exp(&term, self)?;
                            if self
                                .metavariables
                                .contains_unsolved(&self.crate_env, term_elab)
                            {
                                local_scope.infer_elaborated(term_elab, self)?;
                                self.finish_metavariables()?;
                                term_elab = self.metavariables.zonk(&self.crate_env, term_elab);
                            }
                            kernel::utils::decompose_prod(self.crate_env.arena(), term_elab)
                        };

                        let mut ctor_binders = vec![];
                        for (v, e) in telescope {
                            if exp_contains_inductive(self.crate_env.arena(), e, inductive) {
                                // strict positive case
                                let (inner_binders, inner_tail) =
                                    kernel::utils::decompose_prod(self.crate_env.arena(), e);
                                for (_, it) in inner_binders.iter() {
                                    if exp_contains_inductive(
                                        self.crate_env.arena(),
                                        *it,
                                        inductive,
                                    ) {
                                        return Err("Ctor contains inductive type name  in non-strictly positive position".into());
                                    }
                                }
                                let (head, tail) = kernel::utils::decompose_app(
                                    self.crate_env.arena(),
                                    inner_tail,
                                );
                                if !matches!(self.crate_env.arena().get(head), ExpNode::IndType { indspec, .. } if indspec == inductive)
                                {
                                    return Err("Constructor binder type head does not match inductive type name {type_name_var}".into());
                                }

                                for tail_elm in tail.iter() {
                                    if exp_contains_inductive(
                                        self.crate_env.arena(),
                                        *tail_elm,
                                        inductive,
                                    ) {
                                        return Err("Constructor binder type tail contains inductive type name in non-strictly positive position".into());
                                    }
                                }
                                ctor_binders.push(CtorBinder::StrictPositive {
                                    binders: inner_binders,
                                    self_indices: tail,
                                });
                            } else {
                                // simple case
                                ctor_binders.push(CtorBinder::Simple((v, e)));
                            }
                        }

                        let (head, tail) =
                            kernel::utils::decompose_app(self.crate_env.arena(), ends_elab);
                        if !matches!(self.crate_env.arena().get(head), ExpNode::IndType { indspec, .. } if indspec == inductive)
                        {
                            return Err(
                                "Constructor type head does not match inductive type name".into()
                            );
                        }

                        for tail_elm in tail.iter() {
                            if exp_contains_inductive(self.crate_env.arena(), *tail_elm, inductive)
                            {
                                return Err("Constructor type tail contains inductive type name in non-strictly positive position".into());
                            }
                        }

                        ctor_type_elabs.push(kernel::inductive::CtorType {
                            telescope: ctor_binders,
                            indices: tail,
                        });
                    }

                    let indspec = InductiveTypeSpecs::unchecked(
                        parameter_elab,
                        indices_elab,
                        *sort,
                        ctor_type_elabs,
                    );
                    /* let indspec = InductiveTypeSpecs::new(
                        &mut CheckSession::new(
                            &self.crate_env,
                            self.module_manager.current(),
                            &mut ctx,
                        ),
                        parameter_elab,
                        indices_elab,
                        *sort,
                        ctor_type_elabs,
                    )
                    .map_err(|error| {
                        log_msg!(
                            self.logger,
                            LogLevel::Error,
                            ["inductive type construction"],
                            "inductive type construction failed: {:?}",
                            error,
                        );
                        "Ill-formed inductive type specification".to_string()
                    })?; */

                    self.crate_env.define_inductive(inductive, indspec);
                    let spec = self.crate_env.inductive(inductive).clone();
                    spec.validate(
                        &mut CheckSession::new(
                            &self.crate_env,
                            self.module_manager.current(),
                            &mut ctx,
                        ),
                        inductive,
                    )
                    .map_err(|error| {
                        format!("Ill-formed inductive type specification: {error:?}")
                    })?;
                    self.module_manager.publish_reserved_inductive(
                        &mut self.crate_env,
                        type_name.clone(),
                        ctor_names,
                        inductive,
                    )?;
                }
                ModuleItem::Record {
                    type_name,
                    parameters,
                    kind,
                    fields,
                } => {
                    if matches!(kind, StructureKind::Program) {
                        let fields = fields
                            .iter()
                            .map(|(name, ty)| RightBind {
                                vars: vec![name.clone()],
                                ty: Box::new(ty.clone()),
                            })
                            .collect::<Vec<_>>();
                        let result = SExp::AccessPath {
                            access: LocalAccess::Current {
                                access: type_name.clone(),
                            },
                            parameters: Vec::new(),
                        };
                        self.add_typed_program_inductive_decl(
                            type_name,
                            parameters,
                            &[(Identifier("$structure".into()), fields, result)],
                            false,
                        )?;
                        continue;
                    }
                    let StructureKind::Pts(sort) = kind else {
                        unreachable!();
                    };
                    // treat record as inductive type with one constructor without recursive definition
                    // no register of type name as binded var since no recursive definition

                    // elaborate parameters
                    // binding is memorized in local scope
                    let mut parameter_elab =
                        local_scope.elab_telescope_bind_in_decl(parameters, self)?;
                    if !self.metavariables.is_empty() {
                        self.finish_metavariables()?;
                        for (_, ty) in &mut parameter_elab {
                            *ty = self.metavariables.zonk(&self.crate_env, *ty);
                        }
                    }

                    // elaborate fields as constructors
                    let mut telescope = vec![];
                    let mut fields_get: Vec<(SymbolId, Exp)> = vec![];
                    for (field_name, field_ty) in fields {
                        let field_name_var = self.crate_env.intern(field_name.as_str());
                        let mut field_ty_elab = local_scope.elab_exp(field_ty, self)?;
                        if self
                            .metavariables
                            .contains_unsolved(&self.crate_env, field_ty_elab)
                        {
                            local_scope.infer_elaborated(field_ty_elab, self)?;
                            self.finish_metavariables()?;
                            field_ty_elab = self.metavariables.zonk(&self.crate_env, field_ty_elab);
                        }
                        fields_get.push((field_name_var, field_ty_elab));
                        // field may depend on previous fields
                        local_scope.push_typed_decl_var(field_name_var, field_ty_elab);
                        telescope.push(CtorBinder::Simple((field_name_var, field_ty_elab)));
                    }

                    let indspec = InductiveTypeSpecs::unchecked(
                        parameter_elab,
                        vec![],
                        *sort,
                        vec![kernel::inductive::CtorType {
                            telescope,
                            indices: vec![],
                        }],
                    );
                    /* let indspec = InductiveTypeSpecs::new(
                        &mut CheckSession::new(
                            &self.crate_env,
                            self.module_manager.current(),
                            &mut ctx,
                        ),
                        parameter_elab,
                        vec![],
                        *sort,
                        vec![kernel::inductive::CtorType {
                            telescope,
                            indices: vec![],
                        }],
                    )
                    .map_err(|error| {
                        log_msg!(
                            self.logger,
                            LogLevel::Error,
                            ["record type construction"],
                            "record type construction failed: {:?}",
                            error,
                        );
                        "Ill-formed record type specification".to_string()
                    })?; */

                    let inductive = self
                        .crate_env
                        .reserve_inductive(self.module_manager.current());
                    self.crate_env.define_inductive(inductive, indspec);
                    self.crate_env
                        .inductive(inductive)
                        .clone()
                        .validate(
                            &mut CheckSession::new(
                                &self.crate_env,
                                self.module_manager.current(),
                                &mut ctx,
                            ),
                            inductive,
                        )
                        .map_err(|error| format!("Ill-formed structure: {error:?}"))?;
                    self.module_manager.publish_reserved_record(
                        &mut self.crate_env,
                        type_name.clone(),
                        inductive,
                    )?;
                }
                ModuleItem::ChildModule { module } => {
                    self.module_add_rec(module)?;
                }
                ModuleItem::Import { path, import_name } => {
                    if self
                        .crate_env
                        .module(self.module_manager.current())
                        .import(import_name.as_str())
                        .is_some()
                    {
                        return Err(format!(
                            "Module import '{}' is already defined",
                            import_name.as_str()
                        )
                        .into());
                    }
                    let (from, calls) = match path {
                        ModuleInstantiatePath::FromCurrent { back_parent, calls } => {
                            (Some(*back_parent), calls)
                        }
                        ModuleInstantiatePath::FromRoot { calls } => (None, calls),
                    };

                    let mut args = calls
                        .iter()
                        .map(|call| {
                            let args_given_this = call
                                .1
                                .iter()
                                .map(|(id, sexp)| {
                                    let exp_elab = local_scope.elab_exp(sexp, self)?;
                                    Ok((id.clone(), exp_elab))
                                })
                                .collect::<Result<Vec<_>, String>>()?;
                            Ok((call.0.clone(), args_given_this))
                        })
                        .collect::<Result<Vec<_>, String>>()?;

                    self.solve_module_arguments(&mut ctx, from, &mut args)?;

                    let access_result = self
                        .module_manager
                        .instantiate_module(&mut self.crate_env, &mut ctx, from, args)
                        .map_err(|e| format!("Module instantiation failed: {}", e))?;

                    self.module_manager.add_import(
                        &mut self.crate_env,
                        import_name.clone(),
                        access_result,
                    )?;
                }
                ModuleItem::MathMacro {
                    name,
                    before,
                    after,
                } => self.module_manager.register_macro(
                    &self.crate_env,
                    name.clone(),
                    MacroKind::Math,
                    before.clone(),
                    after.clone(),
                )?,
                ModuleItem::UserMacro {
                    name,
                    before,
                    after,
                } => self.module_manager.register_macro(
                    &self.crate_env,
                    name.clone(),
                    MacroKind::Named,
                    before.clone(),
                    after.clone(),
                )?,
                ModuleItem::UseMacro {
                    import_name,
                    macro_name,
                } => self
                    .module_manager
                    .use_macro(&self.crate_env, import_name, macro_name)?,
                ModuleItem::Eval { exp, proof } => {
                    let exp_elab = local_scope.elab_exp(exp, self)?;
                    if !self.metavariables.is_empty() {
                        self.infer_term_with_metavariables(&mut ctx, exp_elab)
                            .map_err(|message| self.metavariables.constraint_error(message))?;
                        self.finish_metavariables()?;
                    }
                    let exp_elab = self.metavariables.zonk(&self.crate_env, exp_elab);
                    if proof.is_some() {
                        let module_context = ctx.clone();
                        let (judgement, obligations) =
                            self.collect_inference_obligations(&mut ctx, exp_elab)?;
                        let evidence = self.elaborate_proof_evidence(
                            proof.as_ref(),
                            &obligations,
                            &module_context,
                        )?;
                        ctx = module_context;
                        self.validate_inference_with_evidence(
                            &mut ctx, exp_elab, judgement, &evidence,
                        )?;
                    }
                    self.logger.reduce_one(
                        &self.crate_env,
                        self.module_manager.current(),
                        &mut ctx,
                        exp_elab,
                    );
                }
                ModuleItem::Normalize { exp, proof } => {
                    let exp_elab = local_scope.elab_exp(exp, self)?;
                    if !self.metavariables.is_empty() {
                        self.infer_term_with_metavariables(&mut ctx, exp_elab)
                            .map_err(|message| self.metavariables.constraint_error(message))?;
                        self.finish_metavariables()?;
                    }
                    let exp_elab = self.metavariables.zonk(&self.crate_env, exp_elab);
                    if proof.is_some() {
                        let module_context = ctx.clone();
                        let (judgement, obligations) =
                            self.collect_inference_obligations(&mut ctx, exp_elab)?;
                        let evidence = self.elaborate_proof_evidence(
                            proof.as_ref(),
                            &obligations,
                            &module_context,
                        )?;
                        ctx = module_context;
                        self.validate_inference_with_evidence(
                            &mut ctx, exp_elab, judgement, &evidence,
                        )?;
                    }
                    self.logger.normalize(
                        &self.crate_env,
                        self.module_manager.current(),
                        &mut ctx,
                        exp_elab,
                    );
                }
                ModuleItem::ValueEval { exp } | ModuleItem::ValueNormalize { exp } => {
                    let mut scope = program_term_elaborator::ProgramScope::from_environment(self);
                    let value = scope.elaborate_value(exp, self)?;
                    self.logger.record(
                        LogLevel::Debug,
                        vec!["program evaluation".into()],
                        "Program value is in normal form".into(),
                        LogPayload::Value(value),
                    );
                }
                ModuleItem::ComputationEval { exp } => {
                    let mut scope = program_term_elaborator::ProgramScope::from_environment(self);
                    let computation = scope.elaborate_computation(exp, self)?;
                    let reduced = kernel::program_calculus::reduce_computation_once(
                        &self.crate_env,
                        computation,
                    );
                    self.logger.record(
                        LogLevel::Debug,
                        vec!["program evaluation".into()],
                        if reduced.is_some() {
                            "Program computation reduced once".into()
                        } else {
                            "Program computation cannot reduce".into()
                        },
                        reduced.map_or(
                            LogPayload::Computation(computation),
                            LogPayload::Computation,
                        ),
                    );
                }
                ModuleItem::ComputationNormalize { exp } => {
                    let mut scope = program_term_elaborator::ProgramScope::from_environment(self);
                    let computation = scope.elaborate_computation(exp, self)?;
                    self.logger
                        .evaluate_computation(&self.crate_env, computation);
                }
                ModuleItem::Check { exp, ty, proof } => {
                    let exp_elab = local_scope.elab_exp(exp, self)?;
                    let ty_elab = local_scope.elab_exp(ty, self)?;
                    if !self.metavariables.is_empty() {
                        self.check_term_with_metavariables(&mut ctx, exp_elab, ty_elab)
                            .map_err(|message| self.metavariables.constraint_error(message))?;
                        self.finish_metavariables()?;
                    }
                    let exp_elab = self.metavariables.zonk(&self.crate_env, exp_elab);
                    let ty_elab = self.metavariables.zonk(&self.crate_env, ty_elab);
                    if proof.is_some() {
                        let module_context = ctx.clone();
                        let (kind, obligations) =
                            self.collect_definition_obligations(&mut ctx, exp_elab, ty_elab)?;
                        let evidence = self.elaborate_proof_evidence(
                            proof.as_ref(),
                            &obligations,
                            &module_context,
                        )?;
                        ctx = module_context;
                        self.validate_definition_with_evidence(
                            &mut ctx, kind, exp_elab, ty_elab, &evidence,
                        )?;
                        self.logger.record(
                            LogLevel::Debug,
                            vec!["check".to_string()],
                            "check success".to_string(),
                            LogPayload::Exp(ty_elab),
                        );
                    } else {
                        self.logger.check(
                            &self.crate_env,
                            self.module_manager.current(),
                            &mut ctx,
                            exp_elab,
                            ty_elab,
                        );
                    }
                }
                ModuleItem::Infer { exp, proof } => {
                    let exp_elab = local_scope.elab_exp(exp, self)?;
                    if !self.metavariables.is_empty() {
                        self.infer_term_with_metavariables(&mut ctx, exp_elab)
                            .map_err(|message| self.metavariables.constraint_error(message))?;
                        self.finish_metavariables()?;
                    }
                    let exp_elab = self.metavariables.zonk(&self.crate_env, exp_elab);
                    if proof.is_some() {
                        let module_context = ctx.clone();
                        let (judgement, obligations) =
                            self.collect_inference_obligations(&mut ctx, exp_elab)?;
                        let evidence = self.elaborate_proof_evidence(
                            proof.as_ref(),
                            &obligations,
                            &module_context,
                        )?;
                        ctx = module_context;
                        self.validate_inference_with_evidence(
                            &mut ctx, exp_elab, judgement, &evidence,
                        )?;
                        let payload = LogPayload::Exp(judgement.ty);
                        self.logger.record(
                            LogLevel::Debug,
                            vec!["infer".to_string()],
                            format!("infer success: {judgement:?}"),
                            payload,
                        );
                    } else {
                        self.logger.infer_any(
                            &self.crate_env,
                            self.module_manager.current(),
                            &mut ctx,
                            exp_elab,
                        );
                    }
                }
            }
        }

        // 3. move back to parent
        self.module_manager
            .publish_current_module(&mut self.crate_env)?;
        self.module_manager.moveto_parent(&self.crate_env);
        Ok(())
    }
}
