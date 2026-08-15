use crate::{
    elaborator::{module_manager::ItemAccessResult, term_elaborator::LocalScope},
    log_msg, log_record,
    logger::{LogLevel, LogPayload, Logger},
    syntax::*,
};
use kernel::{
    calculus::exp_contains_inductive,
    derivation::CheckSession,
    environment::{CrateEnv, ModuleParameter},
    exp::*,
    inductive::{CtorBinder, InductiveTypeSpecs},
};

pub mod module_manager;
pub mod term_elaborator;

// do type checking
#[derive(Default)]
pub struct GlobalEnvironment {
    crate_env: CrateEnv,
    logger: Logger, // to pass to elaborator
    module_manager: module_manager::ModuleManager,
}

impl term_elaborator::Handler for GlobalEnvironment {
    fn env(&self) -> &CrateEnv {
        &self.crate_env
    }

    fn arena(&self) -> &Arena {
        self.crate_env.arena()
    }

    fn intern(&mut self, name: &str) -> SymbolId {
        self.crate_env.intern(name)
    }

    fn symbol(&self, symbol: SymbolId) -> &str {
        self.crate_env.symbol(symbol)
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
        let result = self
            .logger
            .infer(&self.crate_env, self.module_manager.current(), &mut ctx, e)
            .ok_or("Failed to infer elaborated expression".to_string());
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
}

impl GlobalEnvironment {
    pub fn add_new_module_to_root(&mut self, module: &Module) -> Result<(), String> {
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
    fn module_add_rec(&mut self, module: &Module) -> Result<(), String> {
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
            ));
        };

        // 1. before adding child, check well-typedness ness of parameters
        {
            let reserved_module = self
                .module_manager
                .reserve_child_and_moveto(&mut self.crate_env, name.0.clone());
            let mut ctx = self.module_manager.current_context(&self.crate_env);

            let mut parameter_position = 0_u32;

            let mut local_scope = term_elaborator::LocalScope::default();

            for RightBind { vars, ty } in parameters.iter() {
                let ty_elab = local_scope.elab_exp(ty, self)?;
                // check sort of parameter type
                self.logger
                    .infer_sort(
                        &self.crate_env,
                        self.module_manager.current(),
                        &mut ctx,
                        ty_elab,
                    )
                    .ok_or("Failed to infer sort of parameter type".to_string())?;

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
                            ty: ty_elab,
                        },
                    );
                    parameter_position += 1;
                    ctx.push((symbol, ty_elab));
                    local_scope.push_typed_decl_var_exp(symbol, ty_elab, parameter_exp);
                }
            }
        }

        let mut ctx = self.module_manager.current_context(&self.crate_env);

        // 2. elaborate declarations
        for decl in declarations {
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
                    // check body : ty
                    if !self.logger.check(
                        &self.crate_env,
                        self.module_manager.current(),
                        &mut ctx,
                        body_elab,
                        ty_elab,
                    ) {
                        return Err(format!(
                            "Definition {} body does not check against declared type",
                            name.as_str()
                        ));
                    }
                    let defined_constant = DefinedConstant {
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
                    sort,
                    constructors,
                } => {
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
                    let parameter_elab =
                        local_scope.elab_telescope_bind_in_decl(parameters, self)?;
                    let indices_elab = local_scope.elab_telescope_bind_in_decl(indices, self)?;

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
                            let term_elab = local_scope.elab_exp(&term, self)?;
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
                                        return Err(
                                            "Ctor contains inductive type name  in non-strictly positive position".to_string(),
                                        );
                                    }
                                }
                                let (head, tail) = kernel::utils::decompose_app(
                                    self.crate_env.arena(),
                                    inner_tail,
                                );
                                if !matches!(self.crate_env.arena().get(head), Node::IndType { indspec, .. } if indspec == inductive)
                                {
                                    return Err(
                                        "Constructor binder type head does not match inductive type name {type_name_var}".to_string(),
                                    );
                                }

                                for tail_elm in tail.iter() {
                                    if exp_contains_inductive(
                                        self.crate_env.arena(),
                                        *tail_elm,
                                        inductive,
                                    ) {
                                        return Err(
                                            "Constructor binder type tail contains inductive type name in non-strictly positive position".to_string(),
                                        );
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
                            return Err("Constructor type head does not match inductive type name"
                                .to_string());
                        }

                        for tail_elm in tail.iter() {
                            if exp_contains_inductive(self.crate_env.arena(), *tail_elm, inductive)
                            {
                                return Err(
                                    "Constructor type tail contains inductive type name in non-strictly positive position".to_string(),
                                );
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
                    let parameter_elab =
                        local_scope.elab_telescope_bind_in_decl(parameters, self)?;

                    // elaborate fields as constructors
                    let mut telescope = vec![];
                    let mut fields_get: Vec<(SymbolId, Exp)> = vec![];
                    for (field_name, field_ty) in fields {
                        let field_name_var = self.crate_env.intern(field_name.as_str());
                        let field_ty_elab = local_scope.elab_exp(field_ty, self)?;
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
                        ));
                    }
                    let (from, calls) = match path {
                        ModuleInstantiatePath::FromCurrent { back_parent, calls } => {
                            (Some(*back_parent), calls)
                        }
                        ModuleInstantiatePath::FromRoot { calls } => (None, calls),
                    };

                    let args = calls
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
                    self.logger.reduce_one(&self.crate_env, exp_elab);
                }
                ModuleItem::Normalize { exp } => {
                    let exp_elab = local_scope.elab_exp(exp, self)?;
                    self.logger.normalize(&self.crate_env, exp_elab);
                }
                ModuleItem::Check { exp, ty } => {
                    let exp_elab = local_scope.elab_exp(exp, self)?;
                    let ty_elab = local_scope.elab_exp(ty, self)?;
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
                    self.logger.infer(
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
