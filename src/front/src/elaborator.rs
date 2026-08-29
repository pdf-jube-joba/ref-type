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
    program_inductive::{ProgramConstructorSpec, ProgramInductiveTypeSpecs},
    sort::Sort,
};

pub mod module_manager;
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

    fn intern(&mut self, name: &str) -> SymbolId {
        self.crate_env.intern(name)
    }

    fn symbol(&self, symbol: SymbolId) -> &str {
        self.crate_env.symbol(symbol)
    }

    fn fresh_meta(&mut self, kind: SurfaceMeta, span: SourceSpan, local_context: &Context) -> Exp {
        let mut context = self.module_manager.current_context(&self.crate_env);
        context.extend(local_context.iter().cloned());
        self.metavariables
            .fresh(&self.crate_env, kind, span, &context, local_context.len())
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

        let Node::IndType {
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

    fn infer(&mut self, local_ctx: &mut Context, e: Exp) -> Result<Exp, String> {
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
                .ok_or("Failed to infer elaborated expression".to_string())
        };
        *local_ctx = ctx.split_off(module_context_len);
        result
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

    fn solve_module_arguments(
        &mut self,
        context: &mut Context,
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
                    ModuleParameterKind::ProgramType => {
                        self.metavariables
                            .check_value_type(
                                &self.crate_env,
                                self.module_manager.current(),
                                context,
                                *argument,
                            )
                            .map_err(|message| self.metavariables.constraint_error(message))?;
                    }
                    ModuleParameterKind::ProgramValue { ty } => {
                        let expected = exp_subst_map(self.crate_env.arena(), ty, &substitutions);
                        self.metavariables
                            .check_value(
                                &self.crate_env,
                                self.module_manager.current(),
                                context,
                                *argument,
                                expected,
                            )
                            .map_err(|message| self.metavariables.constraint_error(message))?;
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
        Node::Bound(_) => ty,
        Node::ThunkType { computation_ty } => reflect(computation_ty)?,
        Node::ReturnType { value_ty } => reflect(value_ty)?,
        Node::ComputationFunction { domain, codomain } => {
            let domain = reflect(domain)?;
            let codomain = kernel::calculus::shift_bound_indices(arena, reflect(codomain)?, 1, 0);
            arena.alloc(Node::Prod {
                var: SymbolId::ANONYMOUS,
                ty: domain,
                body: codomain,
            })
        }
        Node::ProgramIndType {
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
                    .map(|index| arena.bound(index))
                    .collect()
            } else {
                parameters
                    .into_iter()
                    .map(reflect)
                    .collect::<Result<Vec<_>, _>>()?
            };
            arena.alloc(Node::IndType {
                indspec: reflected,
                parameters,
            })
        }
        Node::ModuleParam(_) => arena.alloc(Node::RfType { compute_ty: ty }),
        Node::RunStep { .. } => {
            if kernel::calculus::exp_contains_bound(arena, ty, 0) {
                return Err(
                    "RunStep fields depending on Program datatype parameters cannot yet be mirrored"
                        .into(),
                );
            }
            arena.alloc(Node::RfType { compute_ty: ty })
        }
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

    fn add_program_inductive_decl(
        &mut self,
        ctx: &mut Context,
        type_name: &Identifier,
        parameters: &[RightBind],
        constructors: &[(Identifier, Vec<RightBind>, SExp)],
    ) -> Result<(), ElaborationError> {
        let module = self.module_manager.current();
        let inductive = self.crate_env.reserve_program_inductive(module);
        let reflected = self.crate_env.reserve_inductive(module);
        let type_name_var = self.crate_env.intern(type_name.as_str());
        let type_name_exp = self.crate_env.arena().alloc(Node::ProgramIndType {
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
                    let field_ty = kernel::calculus::shift_bound_indices(
                        self.crate_env.arena(),
                        field_ty,
                        elaborated_fields.len(),
                        0,
                    );
                    elaborated_fields.push((SymbolId::ANONYMOUS, field_ty));
                } else {
                    for var in vars {
                        let field_ty = kernel::calculus::shift_bound_indices(
                            self.crate_env.arena(),
                            field_ty,
                            elaborated_fields.len(),
                            0,
                        );
                        elaborated_fields.push((self.crate_env.intern(var.as_str()), field_ty));
                    }
                }
            }
            let result = scope.elab_exp(result, self)?;
            if !matches!(
                self.crate_env.arena().get(result),
                Node::ProgramIndType { indspec, parameters } if indspec == inductive && parameters.is_empty()
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
                                Node::IndType { indspec, .. } if indspec == reflected
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
        self.crate_env
            .inductive(reflected)
            .validate(
                &mut CheckSession::new(&self.crate_env, module, ctx),
                reflected,
            )
            .map_err(|error| format!("Ill-formed reflected datatype: {error:?}"))?;
        self.module_manager.publish_reserved_program_inductive(
            &mut self.crate_env,
            type_name.clone(),
            constructor_names,
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

            for RightBind { vars, ty } in parameters.iter() {
                let program_type_parameter = matches!(ty.as_ref(), SExp::ValueType);
                let mut ty_elab = if program_type_parameter {
                    None
                } else {
                    Some(local_scope.elab_exp(ty, self)?)
                };
                if let Some(elaborated) = ty_elab
                    && !self.metavariables.is_empty()
                {
                    if self
                        .metavariables
                        .infer_sort(
                            &self.crate_env,
                            self.module_manager.current(),
                            &mut ctx,
                            elaborated,
                        )
                        .is_err()
                    {
                        self.metavariables
                            .check_value_type(
                                &self.crate_env,
                                self.module_manager.current(),
                                &mut ctx,
                                elaborated,
                            )
                            .map_err(|message| self.metavariables.constraint_error(message))?;
                    }
                    self.finish_metavariables()?;
                    ty_elab = Some(self.metavariables.zonk(&self.crate_env, elaborated));
                }
                let parameter_kind = if program_type_parameter {
                    ModuleParameterKind::ProgramType
                } else {
                    let ty_elab = ty_elab.expect("non-marker type was elaborated");
                    let mut session =
                        CheckSession::new(&self.crate_env, self.module_manager.current(), &mut ctx);
                    if session.infer_sort(ty_elab).is_ok() {
                        ModuleParameterKind::Pts { ty: ty_elab }
                    } else {
                        session.check_value_type(ty_elab).map_err(|_| {
                            "Module parameter type is neither PTS nor vtype".to_string()
                        })?;
                        ModuleParameterKind::ProgramValue { ty: ty_elab }
                    }
                };

                for v in vars {
                    let symbol = self.crate_env.intern(v.as_str());
                    let position = parameter_position;
                    let parameter_exp = self.crate_env.arena().module_param(ModuleParamId {
                        module: reserved_module,
                        position,
                    });
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
                            ctx.push(ContextEntry::Pts { var: symbol, ty });
                            local_scope.push_typed_decl_var_exp(symbol, ty, parameter_exp);
                        }
                        ModuleParameterKind::ProgramType => {
                            ctx.push(ContextEntry::ProgramType { var: symbol });
                            local_scope.push_program_type_decl_var_exp(symbol, parameter_exp);
                        }
                        ModuleParameterKind::ProgramValue { ty } => {
                            ctx.push(ContextEntry::ProgramValue { var: symbol, ty });
                            local_scope.push_program_value_decl_var_exp(symbol, ty, parameter_exp);
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
                ModuleItem::Definition { name, ty, body } => {
                    self.logger.record(
                        LogLevel::Debug,
                        vec!["elaborator".to_string(), "definition".to_string()],
                        format!("Elaborating definition {}", name.as_str()),
                        LogPayload::Message,
                    );
                    let ty_elab = local_scope.elab_exp(ty, self)?;
                    let body_elab = local_scope.elab_exp(body, self)?;
                    if !self.metavariables.is_empty() {
                        if self
                            .metavariables
                            .infer_sort(
                                &self.crate_env,
                                self.module_manager.current(),
                                &mut ctx,
                                ty_elab,
                            )
                            .is_ok()
                        {
                            self.metavariables
                                .check_pts(
                                    &self.crate_env,
                                    self.module_manager.current(),
                                    &mut ctx,
                                    body_elab,
                                    ty_elab,
                                )
                                .map_err(|message| self.metavariables.constraint_error(message))?;
                        } else if self
                            .metavariables
                            .check_value_type(
                                &self.crate_env,
                                self.module_manager.current(),
                                &mut ctx,
                                ty_elab,
                            )
                            .is_ok()
                        {
                            self.metavariables
                                .check_value(
                                    &self.crate_env,
                                    self.module_manager.current(),
                                    &mut ctx,
                                    body_elab,
                                    ty_elab,
                                )
                                .map_err(|message| self.metavariables.constraint_error(message))?;
                        } else {
                            self.metavariables
                                .check_computation(
                                    &self.crate_env,
                                    self.module_manager.current(),
                                    &mut ctx,
                                    body_elab,
                                    ty_elab,
                                )
                                .map_err(|message| self.metavariables.constraint_error(message))?;
                        }
                        self.finish_metavariables()?;
                    }
                    let ty_elab = self.metavariables.zonk(&self.crate_env, ty_elab);
                    let body_elab = self.metavariables.zonk(&self.crate_env, body_elab);
                    let mut session =
                        CheckSession::new(&self.crate_env, self.module_manager.current(), &mut ctx);
                    let kind = if matches!(self.crate_env.arena().get(ty_elab), Node::Sort(_))
                        || session.infer_sort(ty_elab).is_ok()
                    {
                        session
                            .check_pts(body_elab, ty_elab)
                            .map(|()| DefinitionKind::Pts)
                    } else if session.check_value_type(ty_elab).is_ok() {
                        session
                            .check_value(body_elab, ty_elab)
                            .map(|()| DefinitionKind::ProgramValue)
                    } else if session.check_computation_type(ty_elab).is_ok() {
                        session
                            .check_computation(body_elab, ty_elab)
                            .map(|()| DefinitionKind::ProgramComputation)
                    } else {
                        Err(Box::new(kernel::derivation::JudgementError::caused(
                            "declared definition type has no judgement",
                        )))
                    };
                    let Ok(kind) = kind else {
                        return Err(format!(
                            "Definition {} body does not check against declared type",
                            name.as_str()
                        )
                        .into());
                    };
                    let defined_constant = DefinedConstant {
                        kind,
                        ty: ty_elab,
                        body: body_elab,
                    };
                    self.module_manager.add_def(
                        &mut self.crate_env,
                        name.clone(),
                        defined_constant,
                    )?;
                }
                ModuleItem::Inductive {
                    type_name,
                    parameters,
                    indices,
                    kind,
                    constructors,
                } => {
                    if matches!(kind, InductiveKind::Program) {
                        self.add_program_inductive_decl(
                            &mut ctx,
                            type_name,
                            parameters,
                            constructors,
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
                    let type_name_exp = self.crate_env.arena().alloc(Node::IndType {
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
                                if !matches!(self.crate_env.arena().get(head), Node::IndType { indspec, .. } if indspec == inductive)
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
                        if !matches!(self.crate_env.arena().get(head), Node::IndType { indspec, .. } if indspec == inductive)
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
                    sort,
                    fields,
                } => {
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

                    self.module_manager.add_record(
                        &mut self.crate_env,
                        type_name.clone(),
                        indspec,
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
                ModuleItem::MathMacro { .. } | ModuleItem::UserMacro { .. } => todo!(),
                ModuleItem::Eval { exp } => {
                    let exp_elab = local_scope.elab_exp(exp, self)?;
                    if !self.metavariables.is_empty() {
                        if self
                            .metavariables
                            .infer_pts(
                                &self.crate_env,
                                self.module_manager.current(),
                                &mut ctx,
                                exp_elab,
                            )
                            .is_err()
                            && self
                                .metavariables
                                .infer_value(
                                    &self.crate_env,
                                    self.module_manager.current(),
                                    &mut ctx,
                                    exp_elab,
                                )
                                .is_err()
                        {
                            self.metavariables
                                .infer_computation(
                                    &self.crate_env,
                                    self.module_manager.current(),
                                    &mut ctx,
                                    exp_elab,
                                )
                                .map_err(|message| self.metavariables.constraint_error(message))?;
                        }
                        self.finish_metavariables()?;
                    }
                    let exp_elab = self.metavariables.zonk(&self.crate_env, exp_elab);
                    self.logger.reduce_one(
                        &self.crate_env,
                        self.module_manager.current(),
                        &mut ctx,
                        exp_elab,
                    );
                }
                ModuleItem::Normalize { exp } => {
                    let exp_elab = local_scope.elab_exp(exp, self)?;
                    if !self.metavariables.is_empty() {
                        if self
                            .metavariables
                            .infer_pts(
                                &self.crate_env,
                                self.module_manager.current(),
                                &mut ctx,
                                exp_elab,
                            )
                            .is_err()
                            && self
                                .metavariables
                                .infer_value(
                                    &self.crate_env,
                                    self.module_manager.current(),
                                    &mut ctx,
                                    exp_elab,
                                )
                                .is_err()
                        {
                            self.metavariables
                                .infer_computation(
                                    &self.crate_env,
                                    self.module_manager.current(),
                                    &mut ctx,
                                    exp_elab,
                                )
                                .map_err(|message| self.metavariables.constraint_error(message))?;
                        }
                        self.finish_metavariables()?;
                    }
                    let exp_elab = self.metavariables.zonk(&self.crate_env, exp_elab);
                    self.logger.normalize(
                        &self.crate_env,
                        self.module_manager.current(),
                        &mut ctx,
                        exp_elab,
                    );
                }
                ModuleItem::Check { exp, ty } => {
                    let exp_elab = local_scope.elab_exp(exp, self)?;
                    let ty_elab = local_scope.elab_exp(ty, self)?;
                    if !self.metavariables.is_empty() {
                        if self
                            .metavariables
                            .infer_sort(
                                &self.crate_env,
                                self.module_manager.current(),
                                &mut ctx,
                                ty_elab,
                            )
                            .is_ok()
                        {
                            self.metavariables
                                .check_pts(
                                    &self.crate_env,
                                    self.module_manager.current(),
                                    &mut ctx,
                                    exp_elab,
                                    ty_elab,
                                )
                                .map_err(|message| self.metavariables.constraint_error(message))?;
                        } else if self
                            .metavariables
                            .check_value_type(
                                &self.crate_env,
                                self.module_manager.current(),
                                &mut ctx,
                                ty_elab,
                            )
                            .is_ok()
                        {
                            self.metavariables
                                .check_value(
                                    &self.crate_env,
                                    self.module_manager.current(),
                                    &mut ctx,
                                    exp_elab,
                                    ty_elab,
                                )
                                .map_err(|message| self.metavariables.constraint_error(message))?;
                        } else {
                            self.metavariables
                                .check_computation(
                                    &self.crate_env,
                                    self.module_manager.current(),
                                    &mut ctx,
                                    exp_elab,
                                    ty_elab,
                                )
                                .map_err(|message| self.metavariables.constraint_error(message))?;
                        }
                        self.finish_metavariables()?;
                    }
                    let exp_elab = self.metavariables.zonk(&self.crate_env, exp_elab);
                    let ty_elab = self.metavariables.zonk(&self.crate_env, ty_elab);
                    self.logger.check(
                        &self.crate_env,
                        self.module_manager.current(),
                        &mut ctx,
                        exp_elab,
                        ty_elab,
                    );
                }
                ModuleItem::Infer { exp } => {
                    let exp_elab = local_scope.elab_exp(exp, self)?;
                    if !self.metavariables.is_empty() {
                        if self
                            .metavariables
                            .infer_pts(
                                &self.crate_env,
                                self.module_manager.current(),
                                &mut ctx,
                                exp_elab,
                            )
                            .is_err()
                            && self
                                .metavariables
                                .infer_value(
                                    &self.crate_env,
                                    self.module_manager.current(),
                                    &mut ctx,
                                    exp_elab,
                                )
                                .is_err()
                        {
                            self.metavariables
                                .infer_computation(
                                    &self.crate_env,
                                    self.module_manager.current(),
                                    &mut ctx,
                                    exp_elab,
                                )
                                .map_err(|message| self.metavariables.constraint_error(message))?;
                        }
                        self.finish_metavariables()?;
                    }
                    let exp_elab = self.metavariables.zonk(&self.crate_env, exp_elab);
                    self.logger.infer_any(
                        &self.crate_env,
                        self.module_manager.current(),
                        &mut ctx,
                        exp_elab,
                    );
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
