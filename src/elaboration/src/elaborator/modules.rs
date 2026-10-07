//! Elaborate module parameters, imports, and declaration order.
use super::*;

fn declaration_profile_label(item: &ModuleItem) -> String {
    match item {
        ModuleItem::Definition { name, .. } => format!("definition {}", name.as_str()),
        ModuleItem::Inductive { type_name, .. } => {
            format!("inductive {}", type_name.as_str())
        }
        ModuleItem::Record { type_name, .. } => format!("record {}", type_name.as_str()),
        ModuleItem::ChildModule { module } => format!("module {}", module.name.as_str()),
        ModuleItem::Import { import_name, .. } => format!("import {}", import_name.as_str()),
        ModuleItem::MathMacro { name, .. } => format!("math macro {}", name.as_str()),
        ModuleItem::UserMacro { name, .. } => format!("macro {}", name.as_str()),
        ModuleItem::UseMacro { macro_name, .. } => {
            format!("use macro {}", macro_name.as_str())
        }
        _ => "query".to_string(),
    }
}

impl GlobalEnvironment {
    pub(super) fn instantiate_module_expression(
        &mut self,
        path: &ModuleInstantiatePath,
        local_scope: &mut LocalScope,
        program_scope: &mut program_term_elaborator::ProgramScope,
    ) -> Result<ModuleId, ElaborationError> {
        let mut ctx = local_scope.context().clone();
        let source_override = if let ModuleInstantiatePath::FromModule { module, .. } = path {
            Some(
                self.module_manager
                    .hir_module(*module)
                    .ok_or("unknown module expression scope")?,
            )
        } else {
            None
        };
        let (from, base, calls) = match path {
            ModuleInstantiatePath::FromModule { calls, .. } => (None, None, calls),
            ModuleInstantiatePath::FromCurrent { back_parent, calls } => {
                (Some(*back_parent), None, calls)
            }
            ModuleInstantiatePath::FromRoot { calls } => (None, None, calls),
            ModuleInstantiatePath::FromImport { import_name, calls } => {
                let binding = self
                    .module_manager
                    .hir_import(&self.crate_env, import_name)
                    .ok_or_else(|| {
                        format!("Module import '{}' was not found", import_name.as_str())
                    })?;
                (None, Some(binding), calls)
            }
        };

        let mut source = if let Some(source) = source_override {
            source
        } else if let Some(base) = base {
            self.crate_env.binding(base).source
        } else if let Some(back_parent) = from {
            let mut module = self.module_manager.current();
            for _ in 0..back_parent {
                module = self
                    .crate_env
                    .module(module)
                    .parent()
                    .ok_or("already at root module")?;
            }
            module
        } else {
            self.crate_env.root_module()
        };
        let initial_source = source;
        let mut program_substitutions = base
            .map(|base| self.crate_env.binding(base).arguments.clone())
            .unwrap_or_default();
        let mut args = Vec::with_capacity(calls.len());
        for (child_name, supplied) in calls.iter() {
            let child = self
                .module_manager
                .hir_child(&self.crate_env, source, child_name)
                .ok_or_else(|| format!("child module '{}' was not found", child_name.as_str()))?;
            let parameters = self.crate_env.module(child).parameters().to_vec();
            if supplied.len() != parameters.len() {
                return Err(
                    format!("module '{}' argument count mismatch", child_name.as_str()).into(),
                );
            }
            let mut elaborated = Vec::with_capacity(supplied.len());
            for (position, ((name, expression), parameter)) in
                supplied.iter().zip(parameters).enumerate()
            {
                if name.as_str() != self.crate_env.symbol(parameter.name) {
                    return Err(
                        format!("module '{}' argument name mismatch", child_name.as_str()).into(),
                    );
                }
                let argument = match parameter.kind {
                    ModuleParameterKind::Pts { .. } => {
                        ModuleArgument::Pts(local_scope.elab_exp(expression, self)?)
                    }
                    ModuleParameterKind::ProgramType => {
                        let syntax: ValueTypeExp = expression.clone().try_into()?;
                        let ty = program_scope.elaborate_value_type(&syntax, self)?;
                        ModuleArgument::ProgramType(ty)
                    }
                    ModuleParameterKind::ProgramValue { ty } => {
                        let syntax: ValueTermExp = expression.clone().try_into()?;
                        let value = program_scope.elaborate_value(&syntax, self)?;
                        let mut expected = crate::raw::remapping::subst_value_type_module_params(
                            self.crate_env.arena(),
                            ty,
                            &program_substitutions,
                        );
                        if let Some(base) = base {
                            let remapping = self
                                .crate_env
                                .remapping(self.crate_env.binding(base).remapping);
                            expected = crate::raw::remapping::remap_value_type_global_ids(
                                self.crate_env.arena(),
                                expected,
                                &remapping.definition_ids,
                                &remapping.program_inductive_ids,
                            );
                        }
                        let (value, _) =
                            program_scope.check_value_term_with_metas(self, value, expected)?;
                        ModuleArgument::ProgramValue(value)
                    }
                };
                program_substitutions.push((
                    ModuleParamId {
                        module: child,
                        position: position as u32,
                    },
                    argument,
                ));
                elaborated.push((name.clone(), argument));
            }
            args.push((child_name.clone(), elaborated));
            source = child;
        }
        program_scope.finish_metas(self)?;
        for (_, arguments) in &mut args {
            for (_, argument) in arguments {
                match argument {
                    ModuleArgument::ProgramType(ty) => {
                        *ty = program_scope.zonk_module_value_type(self, *ty);
                        ProgramCheckSession::new(
                            &self.crate_env,
                            &mut program_scope.context().clone(),
                        )
                        .check_value_type(*ty)
                        .map_err(|error| {
                            format!("Program type module argument is ill-formed: {error}")
                        })?;
                    }
                    ModuleArgument::ProgramValue(value) => {
                        *value = program_scope.zonk_module_value(self, *value);
                    }
                    ModuleArgument::Pts(_) => {}
                }
            }
        }

        self.solve_module_arguments(&mut ctx, initial_source, base, &mut args)?;
        for entry in &mut ctx {
            entry.ty = self.metavariables.zonk(&self.crate_env, entry.ty);
        }

        let access_result = self
            .module_manager
            .bind_namespace_in_context(
                &mut self.crate_env,
                &mut ctx,
                program_scope.context(),
                initial_source,
                base,
                args,
            )
            .map_err(|e| format!("Module instantiation failed: {}", e))?;

        Ok(access_result)
    }

    fn solve_module_arguments(
        &mut self,
        context: &mut ExpContext,
        mut source: ModuleId,
        base: Option<ModuleId>,
        calls: &mut [(Identifier, Vec<(Identifier, ModuleArgument)>)],
    ) -> Result<(), ElaborationError> {
        if self.metavariables.is_empty() {
            return Ok(());
        }
        let inherited_arguments = base
            .map(|base| self.crate_env.binding(base).arguments.clone())
            .unwrap_or_default();
        let base_remapping = base.map(|base| self.crate_env.binding(base).remapping);
        let mut substitutions = inherited_arguments
            .into_iter()
            .map(|(parameter, argument)| {
                let reflected = match argument {
                    ModuleArgument::Pts(exp) => exp,
                    ModuleArgument::ProgramType(ty) => {
                        crate::raw::reflection::reflect_value_type(&self.crate_env, ty).map_err(
                            |error| {
                                ElaborationError::Message(format!(
                                    "cannot reflect Program type module argument: {error}"
                                ))
                            },
                        )?
                    }
                    ModuleArgument::ProgramValue(value) => crate::raw::reflection::reflect_program(
                        &self.crate_env,
                        crate::raw::program::ProgramTerm::ValueTerm(value),
                    )
                    .map_err(|error| {
                        ElaborationError::Message(format!(
                            "cannot reflect Program value module argument: {error}"
                        ))
                    })?,
                };
                Ok((parameter, reflected))
            })
            .collect::<Result<Vec<_>, ElaborationError>>()?;
        for (child_name, arguments) in calls.iter_mut() {
            let child = self
                .module_manager
                .hir_child(&self.crate_env, source, child_name)
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
                match (parameter.kind, *argument) {
                    (ModuleParameterKind::Pts { ty }, ModuleArgument::Pts(exp)) => {
                        let mut expected = ty;
                        if let Some(remapping) = base_remapping {
                            let remapping = self.crate_env.remapping(remapping);
                            expected = remap_all_global_ids(
                                self.crate_env.arena(),
                                expected,
                                &remapping.definition_ids,
                                &remapping.inductive_ids,
                                &remapping.program_inductive_ids,
                            );
                        }
                        let expected =
                            exp_subst_map(self.crate_env.arena(), expected, &substitutions);
                        self.metavariables
                            .check_pts(
                                &self.crate_env,
                                self.module_manager.current(),
                                context,
                                exp,
                                expected,
                            )
                            .map_err(|message| {
                                self.metavariables
                                    .constraint_error(&self.crate_env, message)
                            })?;
                    }
                    (ModuleParameterKind::ProgramType, ModuleArgument::ProgramType(_))
                    | (ModuleParameterKind::ProgramValue { .. }, ModuleArgument::ProgramValue(_)) =>
                        {}
                    _ => {
                        return Err(ElaborationError::Message(
                            "module argument uses the wrong syntactic category".into(),
                        ));
                    }
                }
                let reflected = match *argument {
                    ModuleArgument::Pts(exp) => exp,
                    ModuleArgument::ProgramType(ty) => {
                        crate::raw::reflection::reflect_value_type(&self.crate_env, ty).map_err(
                            |error| {
                                ElaborationError::Message(format!(
                                    "cannot reflect Program type module argument: {error}"
                                ))
                            },
                        )?
                    }
                    ModuleArgument::ProgramValue(value) => crate::raw::reflection::reflect_program(
                        &self.crate_env,
                        crate::raw::program::ProgramTerm::ValueTerm(value),
                    )
                    .map_err(|error| {
                        ElaborationError::Message(format!(
                            "cannot reflect Program value module argument: {error}"
                        ))
                    })?,
                };
                substitutions.push((
                    ModuleParamId {
                        module: child,
                        position: position as u32,
                    },
                    reflected,
                ));
            }
            source = child;
        }
        self.finish_metavariables()?;
        for (_, arguments) in calls {
            for (_, argument) in arguments {
                if let ModuleArgument::Pts(exp) = argument {
                    *exp = self.metavariables.zonk(&self.crate_env, *exp);
                }
            }
        }
        Ok(())
    }
    pub(super) fn elaborate_module_parameters(
        &mut self,
        module: &Module,
    ) -> Result<(), ElaborationError> {
        let Module { parameters, .. } = module;
        self.diagnostic_location = module.header_source.as_ref().map(|source| SourceLocation {
            source: source.clone(),
            span: module.span,
        });
        self.module_manager.reference_location = self.diagnostic_location.clone();
        self.metavariables.clear();
        let reserved_module = self.module_manager.current();
        let mut ctx = self.module_manager.current_context(&self.crate_env);

        let mut parameter_position = 0_u32;

        let mut local_scope = term_elaborator::LocalScope::default();
        let mut program_scope = program_term_elaborator::ProgramScope::new();

        for RightBind { vars, ty } in parameters.iter() {
            // Structure-valued fields expand to parameters named `field.member`.
            let source = vars.first().and_then(|name| {
                module
                    .parameter_sources
                    .get(name.as_str().split('.').next().unwrap())
            });
            self.diagnostic_location = module.header_source.as_ref().map(|file| SourceLocation {
                source: file.clone(),
                span: source.map_or(module.span, |source| source.span),
            });
            self.module_manager.reference_location = self.diagnostic_location.clone();
            let subject = source.map_or("Module parameter", |source| source.description.as_str());
            let parameter_kind = if matches!(ty.as_ref(), SExp::ValueType) {
                ModuleParameterKind::ProgramType
            } else if !matches!(ty.as_ref(), SExp::Meta { .. })
                && let Ok(program_ty) = ValueTypeExp::try_from(ty.as_ref().clone())
                && let Ok(program_ty) = program_scope.elaborate_value_type(&program_ty, self)
            {
                // Classify Program value parameters before reflecting their
                // names into the logical language for proof parameters.
                let mut program_context = program_scope.context().clone();
                ProgramCheckSession::new(&self.crate_env, &mut program_context)
                    .check_value_type(program_ty)
                    .map_err(|error| {
                        format!("{subject} has an ill-formed Program value type: {error}")
                    })?;
                ModuleParameterKind::ProgramValue { ty: program_ty }
            } else if let Ok(mut pts_ty) = local_scope.elab_exp(ty, self) {
                if !self.metavariables.is_empty() {
                    self.metavariables
                        .infer_sort(
                            &self.crate_env,
                            self.module_manager.current(),
                            &mut ctx,
                            pts_ty,
                        )
                        .map_err(|message| {
                            self.metavariables
                                .constraint_error(&self.crate_env, message)
                        })?;
                    self.finish_metavariables()?;
                    pts_ty = self.metavariables.zonk(&self.crate_env, pts_ty);
                }
                CheckSession::new(&self.crate_env, &mut ctx)
                    .infer_sort(pts_ty)
                    .map_err(|error| {
                        format!("{subject} must have a type or proposition: {error}")
                    })?;
                ModuleParameterKind::Pts { ty: pts_ty }
            } else {
                let program_ty: ValueTypeExp = ty.as_ref().clone().try_into()?;
                let program_ty = program_scope.elaborate_value_type(&program_ty, self)?;
                program_scope.finish_metas(self)?;
                let mut program_context = program_scope.context().clone();
                ProgramCheckSession::new(&self.crate_env, &mut program_context)
                    .check_value_type(program_ty)
                    .map_err(|error| {
                        format!("{subject} has an ill-formed Program value type: {error}")
                    })?;
                ModuleParameterKind::ProgramValue { ty: program_ty }
            };

            for v in vars {
                let symbol = self.crate_env.intern_name(v);
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
                    ModuleParameterKind::ProgramType | ModuleParameterKind::ProgramValue { .. } => {
                        // The parameter was just published, so rebuild the
                        // scope and resolve it through its stable module ID.
                        program_scope = program_term_elaborator::ProgramScope::new();
                    }
                }
            }
        }

        self.diagnostic_location = module.header_source.as_ref().map(|source| SourceLocation {
            source: source.clone(),
            span: module.span,
        });
        self.module_manager.reference_location = self.diagnostic_location.clone();
        for (value, ty) in &module.parameter_checks {
            program_scope.check_member(value, ty, self)?;
        }
        program_scope.finish_metas(self)?;
        self.record_parameters();
        Ok(())
    }

    pub(super) fn elaborate_module_declaration(
        &mut self,
        module: &Module,
        index: usize,
    ) -> Result<(), ElaborationError> {
        let ModuleBody::Inline(declarations) = &module.body else {
            return Err("External module was not resolved".into());
        };
        let decl = declarations
            .get(index)
            .ok_or("unknown declaration in execution order")?;
        let location = module.source.as_ref().map(|source| SourceLocation {
            source: source.clone(),
            span: module
                .declaration_spans
                .get(index)
                .copied()
                .unwrap_or(module.span),
        });
        self.elaborate_declaration(decl, location)
    }

    pub(super) fn elaborate_declaration(
        &mut self,
        decl: &ModuleItem,
        location: Option<SourceLocation>,
    ) -> Result<(), ElaborationError> {
        let mut ctx = self.module_manager.current_context(&self.crate_env);
        let mut profile_timer =
            profiling::ProfileTimer::start("REF_TYPE_PROFILE_DECLARATIONS", || {
                format!(
                    "{}: {}",
                    self.active_module_path().join("."),
                    declaration_profile_label(decl)
                )
            });
        self.diagnostic_location = location;
        self.module_manager.reference_location = self.diagnostic_location.clone();
        let output_start = self.outputs.len();
        self.metavariables.clear();
        let mut local_scope = LocalScope::default();
        match decl {
            ModuleItem::SetStructure {
                name,
                parameters,
                sort,
                fields,
            } => {
                self.elaborate_set_structure(name, parameters, *sort, fields)?;
            }
            ModuleItem::Structure { .. } | ModuleItem::Scoped { .. } => {
                return Err("unresolved frontend declaration".into());
            }
            ModuleItem::Definition {
                owner,
                name,
                binders,
                ty,
                body,
            } => {
                let program_result =
                    self.elaborate_program_definition_decl(owner.as_ref(), name, binders, ty, body);
                if let Some(timer) = &mut profile_timer {
                    timer.checkpoint("Program elaboration attempt");
                }
                let program_errors = match program_result {
                    Ok((parameters, definition)) => {
                        self.publish_program_definition(
                            owner.as_ref(),
                            name.clone(),
                            parameters,
                            definition,
                        )?;
                        self.record_declaration(decl, output_start);
                        self.metavariables.clear();
                        return Ok(());
                    }
                    Err(errors) => errors,
                };
                let has_program_owner = owner.as_ref().is_some_and(|owner| {
                    matches!(
                        self.module_manager.get_item(
                            &self.crate_env,
                            &LocalAccess::Current {
                                span: Default::default(),
                                access: owner.type_name.clone(),
                            },
                        ),
                        Some(module_manager::ItemAccessResult::ProgramInductive(_))
                    )
                });
                if has_program_owner && !program_errors.is_empty() {
                    return Err(ElaborationError::alternatives(program_errors));
                }
                self.metavariables.clear();
                let pts_result = (|| -> Result<(), ElaborationError> {
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
                    self.elaborate_contextual_definition(
                        owner.as_ref(),
                        name,
                        &all_binders,
                        ty,
                        body,
                    )
                })();
                if let Err(error) = pts_result {
                    if program_errors.is_empty() {
                        return Err(error);
                    }
                    return Err(ElaborationError::alternatives(
                        std::iter::once(error).chain(program_errors).collect(),
                    ));
                }
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
                        None,
                    )?;
                    self.record_declaration(decl, output_start);
                    self.metavariables.clear();
                    return Ok(());
                }
                let InductiveKind::Pts(sort) = kind else {
                    unreachable!();
                };
                let type_name_var = self.crate_env.intern_name(type_name);
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
                let mut index_scope = local_scope.clone();
                let mut indices_elab = index_scope.elab_telescope_bind_in_decl(indices, self)?;
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
                                    bind: crate::hir::Bind::Named(bd.clone()),
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
                        crate::raw::utils::decompose_prod(self.crate_env.arena(), term_elab)
                    };

                    let mut ctor_binders = vec![];
                    for (v, e) in telescope {
                        if exp_contains_inductive(self.crate_env.arena(), e, inductive) {
                            // strict positive case
                            let (inner_binders, inner_tail) =
                                crate::raw::utils::decompose_prod(self.crate_env.arena(), e);
                            for (_, it) in inner_binders.iter() {
                                if exp_contains_inductive(self.crate_env.arena(), *it, inductive) {
                                    return Err("Ctor contains inductive type name  in non-strictly positive position".into());
                                }
                            }
                            let (head, tail) = crate::raw::utils::decompose_app(
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
                        crate::raw::utils::decompose_app(self.crate_env.arena(), ends_elab);
                    if !matches!(self.crate_env.arena().get(head), ExpNode::IndType { indspec, .. } if indspec == inductive)
                    {
                        return Err(
                            "Constructor type head does not match inductive type name".into()
                        );
                    }

                    for tail_elm in tail.iter() {
                        if exp_contains_inductive(self.crate_env.arena(), *tail_elm, inductive) {
                            return Err("Constructor type tail contains inductive type name in non-strictly positive position".into());
                        }
                    }

                    ctor_type_elabs.push(crate::raw::inductive::CtorType {
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

                self.crate_env.define_inductive(inductive, indspec);
                let spec = self.crate_env.inductive(inductive).clone();
                spec.validate(&mut CheckSession::new(&self.crate_env, &mut ctx), inductive)
                    .map_err(|error| format!("Ill-formed inductive type specification: {error}"))?;
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
                if matches!(kind, InductiveKind::Program) {
                    self.add_program_record_decl(type_name, parameters, fields)?;
                    self.record_declaration(decl, output_start);
                    self.metavariables.clear();
                    return Ok(());
                }
                let InductiveKind::Pts(sort) = kind else {
                    unreachable!()
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
                    let field_name_var = self.crate_env.intern_name(field_name);
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
                    vec![crate::raw::inductive::CtorType {
                        telescope,
                        indices: vec![],
                    }],
                );

                let inductive = self
                    .crate_env
                    .reserve_inductive(self.module_manager.current());
                self.crate_env.define_inductive(inductive, indspec);
                self.crate_env
                    .inductive(inductive)
                    .clone()
                    .validate(&mut CheckSession::new(&self.crate_env, &mut ctx), inductive)
                    .map_err(|error| format!("Ill-formed structure: {error}"))?;
                let projections = self.add_record_projection_definitions(inductive)?;
                self.module_manager.publish_reserved_record(
                    &mut self.crate_env,
                    type_name.clone(),
                    inductive,
                    projections,
                )?;
            }
            ModuleItem::ChildModule { .. } => {
                return Err("child module in declaration execution order".into());
            }
            ModuleItem::Import {
                path,
                import_name,
                checks,
            } => {
                let mut scope = program_term_elaborator::ProgramScope::new();
                for (value, ty) in checks {
                    scope.check_member(value, ty, self)?;
                }
                scope.finish_metas(self)?;
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
                let access_result =
                    self.instantiate_module_expression(path, &mut local_scope, &mut scope)?;

                self.module_manager.register_hir_import(
                    &self.crate_env,
                    import_name,
                    access_result,
                );
                self.module_manager.add_import(
                    &mut self.crate_env,
                    import_name.clone(),
                    access_result,
                )?;
            }
            ModuleItem::MathMacro { .. }
            | ModuleItem::UserMacro { .. }
            | ModuleItem::UseMacro { .. } => {}
            ModuleItem::Eval { exp } => self.eval_query(exp, &mut ctx)?,
            ModuleItem::Normalize { exp } => self.normalize_query(exp, &mut ctx)?,
            ModuleItem::MemberCheck { value, ty } => {
                let mut scope = program_term_elaborator::ProgramScope::new();
                scope.check_member(value, ty, self)?;
                scope.finish_metas(self)?;
            }
            ModuleItem::ValueTypeCheck { ty } => {
                let mut scope = program_term_elaborator::ProgramScope::new();
                let ty = scope.elaborate_value_type(ty, self)?;
                scope.finish_metas(self)?;
                ProgramCheckSession::new(&self.crate_env, &mut scope.context().clone())
                    .check_value_type(ty)
                    .map_err(|error| error.to_string())?;
            }
            ModuleItem::Check { exp, ty } => self.check_query(exp, ty, &mut ctx)?,
            ModuleItem::Infer { exp } => self.infer_query(exp, &mut ctx)?,
        }
        self.record_declaration(decl, output_start);
        self.metavariables.clear();

        Ok(())
    }
}
