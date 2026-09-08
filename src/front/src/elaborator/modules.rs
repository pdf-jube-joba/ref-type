//! Elaborate module parameters, imports, and declaration order.
use super::*;

impl GlobalEnvironment {
    fn solve_module_arguments(
        &mut self,
        context: &mut ExpContext,
        back_parent: Option<usize>,
        calls: &mut [(Identifier, Vec<(Identifier, ModuleArgument)>)],
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
                match (parameter.kind, *argument) {
                    (ModuleParameterKind::Pts { ty }, ModuleArgument::Pts(exp)) => {
                        let expected = exp_subst_map(self.crate_env.arena(), ty, &substitutions);
                        self.metavariables
                            .check_pts(
                                &self.crate_env,
                                self.module_manager.current(),
                                context,
                                exp,
                                expected,
                            )
                            .map_err(|message| self.metavariables.constraint_error(message))?;
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
    pub(super) fn module_add_rec(&mut self, module: &Module) -> Result<(), ElaborationError> {
        let Module {
            name,
            parameters,
            body,
            ..
        } = module;
        self.diagnostic_location = module.header_source.as_ref().map(|source| SourceLocation {
            source: source.clone(),
            span: module.span,
        });

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
            let mut program_scope = program_term_elaborator::ProgramScope::new();

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
                    ProgramCheckSession::new(&self.crate_env, &mut program_context)
                        .check_value_type(program_ty)
                        .map_err(|error| {
                            format!(
                                "Program module parameter has an ill-formed value type: {error:?}"
                            )
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
                        ModuleParameterKind::ProgramType
                        | ModuleParameterKind::ProgramValue { .. } => {
                            // The parameter was just published, so rebuild the
                            // scope and resolve it through its stable module ID.
                            program_scope = program_term_elaborator::ProgramScope::new();
                        }
                    }
                }
            }
        }

        let mut ctx = self.module_manager.current_context(&self.crate_env);

        // 2. elaborate declarations
        for (index, decl) in declarations.iter().enumerate() {
            self.diagnostic_location = module.source.as_ref().map(|source| SourceLocation {
                source: source.clone(),
                span: module
                    .declaration_spans
                    .get(index)
                    .copied()
                    .unwrap_or(module.span),
            });
            self.metavariables.clear();
            let mut local_scope = LocalScope::default();
            match decl {
                ModuleItem::Definition {
                    owner,
                    name,
                    binders,
                    ty,
                    body,
                } => {
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
                    self.validate_definition(&mut ctx, body_elab, ty_elab)
                        .map_err(|message| {
                            format!(
                                "Definition {} body does not check against declared type: {message}",
                                name.as_str()
                            )
                        })?;
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
                ModuleItem::ValueDefinition { name, ty, body } => {
                    let mut scope = program_term_elaborator::ProgramScope::new();
                    let ty = scope.elaborate_value_type(ty, self)?;
                    let body = scope.elaborate_value(body, self)?;
                    let (body, ty) = scope.check_value_term_with_metas(self, body, ty)?;
                    let certified_reflection = scope.certified_value(self, body);
                    let mut program_context = scope.context().clone();
                    ProgramCheckSession::new(&self.crate_env, &mut program_context)
                        .check_value_term(body, ty)
                        .map_err(|error| {
                            format!(
                                "Program value definition {} is ill-typed: {error:?}",
                                name.as_str()
                            )
                        })?;
                    if scope.has_certificates()
                        && let Some(certificate) = certified_reflection
                    {
                        let reflected_ty =
                            crate::raw::reflection::reflect_value_type(&self.crate_env, ty)
                                .map_err(|error| error.to_string())?;
                        let mut context = self.module_manager.current_context(&self.crate_env);
                        CheckSession::new(
                            &self.crate_env,
                            self.module_manager.current(),
                            &mut context,
                        )
                        .check_pts(certificate, reflected_ty)
                        .map_err(|error| {
                            format!(
                                "Program value definition {} has an invalid certificate: {error:?}",
                                name.as_str()
                            )
                        })?;
                    }
                    self.module_manager.add_def(
                        &mut self.crate_env,
                        name.clone(),
                        DefinedConstant::ProgramValue {
                            ty,
                            body,
                            certified_reflection,
                        },
                    )?;
                }
                ModuleItem::ComputationDefinition { name, ty, body } => {
                    let mut scope = program_term_elaborator::ProgramScope::new();
                    let ty = scope.elaborate_computation_type(ty, self)?;
                    let body = scope.elaborate_computation(body, self)?;
                    let (body, ty) = scope.check_computation_term_with_metas(self, body, ty)?;
                    let certified_reflection = scope.certified_computation(self, body);
                    let mut program_context = scope.context().clone();
                    ProgramCheckSession::new(&self.crate_env, &mut program_context)
                        .check_computation_term(body, ty)
                        .map_err(|error| {
                            format!(
                                "Program computation definition {} is ill-typed: {error:?}",
                                name.as_str()
                            )
                        })?;
                    if scope.has_certificates()
                        && let Some(certificate) = certified_reflection
                    {
                        let reflected_ty =
                            crate::raw::reflection::reflect_computation_type(&self.crate_env, ty)
                                .map_err(|error| error.to_string())?;
                        let mut context = self.module_manager.current_context(&self.crate_env);
                        CheckSession::new(
                            &self.crate_env,
                            self.module_manager.current(),
                            &mut context,
                        )
                        .check_pts(certificate, reflected_ty)
                        .map_err(|error| {
                            format!(
                                "Program computation definition {} has an invalid certificate: {error:?}",
                                name.as_str()
                            )
                        })?;
                    }
                    self.module_manager.add_def(
                        &mut self.crate_env,
                        name.clone(),
                        DefinedConstant::ProgramComputation {
                            ty,
                            body,
                            certified_reflection,
                        },
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
                        self.add_typed_program_inductive_decl(type_name, parameters, constructors)?;
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
                            crate::raw::utils::decompose_prod(self.crate_env.arena(), term_elab)
                        };

                        let mut ctor_binders = vec![];
                        for (v, e) in telescope {
                            if exp_contains_inductive(self.crate_env.arena(), e, inductive) {
                                // strict positive case
                                let (inner_binders, inner_tail) =
                                    crate::raw::utils::decompose_prod(self.crate_env.arena(), e);
                                for (_, it) in inner_binders.iter() {
                                    if exp_contains_inductive(
                                        self.crate_env.arena(),
                                        *it,
                                        inductive,
                                    ) {
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
                            if exp_contains_inductive(self.crate_env.arena(), *tail_elm, inductive)
                            {
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
                        .validate(
                            &mut CheckSession::new(
                                &self.crate_env,
                                self.module_manager.current(),
                                &mut ctx,
                            ),
                            inductive,
                        )
                        .map_err(|error| format!("Ill-formed structure: {error:?}"))?;
                    let projections = self.add_record_projection_definitions(inductive)?;
                    self.module_manager.publish_reserved_record(
                        &mut self.crate_env,
                        type_name.clone(),
                        inductive,
                        projections,
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

                    let mut source = if let Some(back_parent) = from {
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
                    let mut program_substitutions = Vec::new();
                    let mut program_scope = program_term_elaborator::ProgramScope::new();
                    let mut args = Vec::with_capacity(calls.len());
                    for (child_name, supplied) in calls.iter() {
                        let child = self
                            .crate_env
                            .module(source)
                            .children()
                            .iter()
                            .copied()
                            .find(|child| {
                                self.crate_env.module(*child).name() == child_name.as_str()
                            })
                            .ok_or_else(|| {
                                format!("child module '{}' was not found", child_name.as_str())
                            })?;
                        let parameters = self.crate_env.module(child).parameters().to_vec();
                        if supplied.len() != parameters.len() {
                            return Err(format!(
                                "module '{}' argument count mismatch",
                                child_name.as_str()
                            )
                            .into());
                        }
                        let mut elaborated = Vec::with_capacity(supplied.len());
                        for (position, ((name, expression), parameter)) in
                            supplied.iter().zip(parameters).enumerate()
                        {
                            if name.as_str() != self.crate_env.symbol(parameter.name) {
                                return Err(format!(
                                    "module '{}' argument name mismatch",
                                    child_name.as_str()
                                )
                                .into());
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
                                    let expected =
                                        crate::raw::program_calculus::subst_value_type_module_params(
                                            self.crate_env.arena(),
                                            ty,
                                            &program_substitutions,
                                        );
                                    let (value, _) = program_scope
                                        .check_value_term_with_metas(self, value, expected)?;
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
                    program_scope.finish_metas()?;
                    for (_, arguments) in &mut args {
                        for (_, argument) in arguments {
                            match argument {
                                ModuleArgument::ProgramType(ty) => {
                                    *ty = program_scope.zonk_module_value_type(self, *ty);
                                    ProgramCheckSession::new(
                                        &self.crate_env,
                                        &mut Vec::new(),
                                    )
                                    .check_value_type(*ty)
                                    .map_err(|error| {
                                        format!(
                                            "Program type module argument is ill-formed: {error:?}"
                                        )
                                    })?;
                                }
                                ModuleArgument::ProgramValue(value) => {
                                    *value = program_scope.zonk_module_value(self, *value);
                                }
                                ModuleArgument::Pts(_) => {}
                            }
                        }
                    }

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
                ModuleItem::Eval { exp } => self.eval_query(exp, &mut ctx)?,
                ModuleItem::Normalize { exp } => self.normalize_query(exp, &mut ctx)?,
                ModuleItem::ComputationEval { exp } => self.computation_eval_query(exp)?,
                ModuleItem::ComputationNormalize { exp } => {
                    self.computation_normalize_query(exp)?
                }
                ModuleItem::ValueCheck { exp, ty } => self.value_check_query(exp, ty)?,
                ModuleItem::ComputationCheck { exp, ty } => {
                    self.computation_check_query(exp, ty)?
                }
                ModuleItem::ValueInfer { exp } => self.value_infer_query(exp)?,
                ModuleItem::ComputationInfer { exp } => self.computation_infer_query(exp)?,
                ModuleItem::Check { exp, ty } => self.check_query(exp, ty, &mut ctx)?,
                ModuleItem::Infer { exp } => self.infer_query(exp, &mut ctx)?,
            }
        }

        // 3. move back to parent
        self.diagnostic_location = module.header_source.as_ref().map(|source| SourceLocation {
            source: source.clone(),
            span: module.span,
        });
        self.module_manager
            .publish_current_module(&mut self.crate_env)?;
        self.module_manager.moveto_parent(&self.crate_env);
        Ok(())
    }
}
