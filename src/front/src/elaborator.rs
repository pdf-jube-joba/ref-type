use crate::{
    elaborator::{
        module_manager::{InstantiateResult, ItemAccessResult},
        term_elaborator::LocalScope,
    },
    logger::Logger,
    syntax::*,
};
use kernel::{
    calculus::exp_contains_as_freevar,
    exp::*,
    inductive::{self, CtorBinder, InductiveTypeSpecs},
};

pub mod module_manager;
pub mod term_elaborator;
use crate::logger::log_msg;

pub enum Query {
    Eval { exp: Exp },
    Normalize { exp: Exp },
    Checking { ctx: Context, exp: Exp, ty: Exp },
    Infer { ctx: Context, exp: Exp },
    InferSort { ctx: Context, exp: Exp },
}

// do type checking
pub struct GlobalEnvironment {
    logger: Logger, // to pass to elaborator
    module_manager: module_manager::ModuleManager,
}

impl Default for GlobalEnvironment {
    fn default() -> Self {
        GlobalEnvironment {
            logger: Logger::new(),
            module_manager: module_manager::ModuleManager::new(),
        }
    }
}

impl term_elaborator::Handler for GlobalEnvironment {
    fn get_item_from_access_path(
        &mut self,
        access_path: &LocalAccess,
    ) -> Result<ItemAccessResult, String> {
        self.module_manager
            .get_item(access_path)
            .ok_or(format!("Failed to access item at path",))
    }

    fn field_projection(&mut self, e: &Exp, field_name: &Identifier) -> Result<Exp, String> {
        self.logger.log

        let ctx = self
            .module_manager
            .current_context()
            .into_iter()
            .flat_map(|(_, v)| v)
            .collect::<Vec<_>>();

        let infer_type_e = self.logger.with_infer(&ctx, e).ok_or_else(|| {
            format!(
                "Failed to infer type of expression {} for field projection",
                e
            )
        })?;
        let Exp::IndType {
            indspec,
            parameters,
        } = infer_type_e
        else {
            return Err(ErrorKind::Msg(format!(
                "Expected inductive type for field projection, got {}",
                infer_type_e
            )));
        };

        let record = self
            .module_manager
            .get_moditem_record_from_rc(&indspec)
            .ok_or_else(|| ErrorKind::Msg("Inductive type is not a record type".to_string()))?;

        let Some(exp) = record.field_projection(e, field_name, &parameters) else {
            return Err(ErrorKind::Msg(format!(
                "Field {} not found in record",
                field_name.as_str()
            )));
        };

        Ok(exp)
    }
}

impl GlobalEnvironment {
    pub fn logs(&self) -> &Vec<LogEnum> {
        &self.logger.log
    }
}

impl GlobalEnvironment {
    pub fn add_new_module_to_root(&mut self, module: &Module) -> Result<(), ErrorKind> {
        self.logger.log(format!(
            "top level Elaborating module {}",
            module.name.as_str()
        ));
        self.module_manager.moveto_root();
        self.module_add_rec(module)?;
        Ok(())
    }
    fn module_add_rec(&mut self, module: &Module) -> Result<(), ErrorKind> {
        self.logger.log(format!("before: {}", self.module_manager));

        let Module {
            name,
            parameters,
            declarations,
        } = module;

        // 1. before adding child, check well-typedness ness of parameters
        {
            let ctx: Vec<(Var, Exp)> = self
                .module_manager
                .current_context()
                .into_iter()
                .flat_map(|(_, v)| v)
                .collect();

            let mut parameters_elab = vec![];

            let mut local_scope = term_elaborator::LocalScope::default();

            for RightBind { vars, ty } in parameters.iter() {
                let ty_elab = local_scope.elab_exp(ty, self)?;
                let ext_ctx = ctx
                    .iter()
                    .cloned()
                    .chain(parameters_elab.iter().cloned())
                    .collect::<Vec<_>>();
                // check sort of parameter type
                self.logger.infer_sort(&ext_ctx, &ty_elab)?;

                for v in vars {
                    let v = Var::new(v.as_str());
                    parameters_elab.push((v.clone(), ty_elab.clone()));
                    local_scope.push_decl_var(v);
                }
            }
            // ok => add child module and move to it
            self.module_manager
                .add_child_and_moveto(name.0.clone(), parameters_elab);
        }

        self.logger.log(format!(
            "Elaborating module {} with parameters {}",
            name.as_str(),
            parameters
                .iter()
                .map(|bd| format!("{}", bd))
                .collect::<String>()
        ));

        let ctx = self
            .module_manager
            .current_context()
            .into_iter()
            .flat_map(|(_, v)| v)
            .collect::<Vec<_>>();

        // 2. elaborate declarations
        for decl in declarations {
            self.logger
                .log(format!("Elaborating declaration: {}", decl));
            let mut local_scope = LocalScope::default();
            match decl {
                ModuleItem::Definition { name, ty, body } => {
                    let ty_elab = local_scope.elab_exp(ty, self)?;
                    let body_elab = local_scope.elab_exp(body, self)?;
                    let defined_constant = DefinedConstant {
                        ty: ty_elab,
                        body: body_elab,
                    };
                    self.module_manager.add_def(name.clone(), defined_constant);
                }
                ModuleItem::Inductive {
                    type_name,
                    parameters,
                    indices,
                    sort,
                    constructors,
                } => {
                    self.logger.log(format!(
                        "Elaborating inductive type {type_name} {parameters:?}: {indices:?} -> {sort}",
                    ));
                    self.logger.log(format!(
                        "With constructors: {}",
                        constructors
                            .iter()
                            .map(|(n, r, e)| format!("{} : {:?} {}", n.as_str(), r, e))
                            .collect::<String>()
                    ));

                    let type_name_var: Var = type_name.into();
                    // register type name as binded var
                    local_scope.push_decl_var(type_name_var.clone());

                    // elaborate parameters and indices
                    // binding is memorized in local scope
                    let parameter_elab =
                        local_scope.elab_telescope_bind_in_decl(parameters, self)?;
                    let indices_elab = local_scope.elab_telescope_bind_in_decl(indices, self)?;

                    // elaborate constructors
                    let mut ctor_names_var = vec![];
                    let mut ctor_names = vec![];
                    let mut ctor_type_elabs = vec![];

                    for (ctor_name, rightbinds, ends) in constructors {
                        self.logger.log(format!(
                            "Elaborating constructor {} with rightbinds {:?} and ends {}",
                            ctor_name.as_str(),
                            rightbinds,
                            ends
                        ));
                        let ctor_name_var: Var = ctor_name.into();
                        ctor_names_var.push(ctor_name_var.clone());
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
                            self.logger
                                .log(format!("----  (before elaboration): {}", term));
                            let term_elab = local_scope.elab_exp(&term, self)?;
                            self.logger
                                .log(format!("----> Elaborated constructor term: {}", term_elab));
                            kernel::utils::decompose_prod(term_elab)
                        };

                        let mut ctor_binders = vec![];
                        for (v, e) in telescope {
                            if exp_contains_as_freevar(&e, &type_name_var) {
                                // strict positive case
                                let (inner_binders, inner_tail) = kernel::utils::decompose_prod(e);
                                for (_, it) in inner_binders.iter() {
                                    if exp_contains_as_freevar(it, &type_name_var) {
                                        return Err(ErrorKind::Msg(format!(
                                            "Ctor {it} contains inductive type name {type_name_var} in non-strictly positive position"
                                        )));
                                    }
                                }
                                let (head, tail) = kernel::utils::decompose_app(inner_tail);
                                if !matches!(head, Exp::Var(head_var) if head_var.is_eq_ptr(&type_name_var))
                                {
                                    return Err(ErrorKind::Msg(format!(
                                        "Constructor binder type head does not match inductive type name {type_name_var}"
                                    )));
                                }

                                for tail_elm in tail.iter() {
                                    if exp_contains_as_freevar(tail_elm, &type_name_var) {
                                        return Err(ErrorKind::Msg(format!(
                                            "Constructor binder type tail {tail_elm} contains inductive type name {type_name_var} in non-strictly positive position"
                                        )));
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

                        let (head, tail) = kernel::utils::decompose_app(ends_elab);
                        if !matches!(head, Exp::Var(head_var) if head_var.is_eq_ptr(&type_name_var))
                        {
                            return Err(ErrorKind::Msg(format!(
                                "Constructor type head does not match inductive type name {type_name_var}"
                            )));
                        }

                        for tail_elm in tail.iter() {
                            if exp_contains_as_freevar(tail_elm, &type_name_var) {
                                return Err(ErrorKind::Msg(format!(
                                    "Constructor type tail {tail_elm} contains inductive type name {type_name_var} in non-strictly positive position"
                                )));
                            }
                        }

                        self.logger.log(format!(
                            "Elaborated constructor {} with telescope {:?} and indices {:?}",
                            ctor_name.as_str(),
                            ctor_binders,
                            tail
                        ));

                        ctor_type_elabs.push(kernel::inductive::CtorType {
                            telescope: ctor_binders,
                            indices: tail,
                        });
                    }

                    let indspec = InductiveTypeSpecs {
                        parameters: parameter_elab,
                        indices: indices_elab,
                        sort: *sort,
                        constructors: ctor_type_elabs,
                    };

                    self.logger.check_wellformed_indspec(&ctx, &indspec)?;

                    self.module_manager
                        .add_inductive(type_name.clone(), ctor_names, indspec);
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
                    let mut fields_get: Vec<(Var, Exp)> = vec![];
                    for (field_name, field_ty) in fields {
                        let field_name_var: Var = field_name.into();
                        let field_ty_elab = local_scope.elab_exp(field_ty, self)?;
                        fields_get.push((field_name_var.clone(), field_ty_elab.clone()));
                        // field may depend on previous fields
                        local_scope.push_decl_var(field_name_var.clone());
                        telescope.push(CtorBinder::Simple((field_name_var, field_ty_elab)));
                    }

                    let indspec = InductiveTypeSpecs {
                        parameters: parameter_elab,
                        indices: vec![],
                        sort: *sort,
                        constructors: vec![kernel::inductive::CtorType {
                            telescope,
                            indices: vec![],
                        }],
                    };

                    self.logger.check_wellformed_indspec(&ctx, &indspec)?;

                    self.module_manager.add_record(type_name.clone(), indspec);
                }
                ModuleItem::ChildModule { module } => {
                    self.module_add_rec(module)?;
                }
                ModuleItem::Import { path, import_name } => {
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
                                .collect::<Result<Vec<_>, ErrorKind>>()?;
                            Ok((call.0.clone(), args_given_this))
                        })
                        .collect::<Result<Vec<_>, ErrorKind>>()?;

                    let access_result = self
                        .module_manager
                        .instantiate_module(from, args)
                        .map_err(|e| {
                            ErrorKind::Msg(format!("Module instantiation failed: {}", e))
                        })?;

                    let InstantiateResult {
                        instantiated_module,
                        need_to_type_check,
                    } = access_result;

                    for (_, arg, ty) in need_to_type_check {
                        self.logger.check(&ctx, &arg, &ty)?;
                    }

                    self.module_manager
                        .add_import(import_name.clone(), instantiated_module);
                }
                ModuleItem::MathMacro { .. } | ModuleItem::UserMacro { .. } => todo!(),
                ModuleItem::Eval { exp } => {
                    let exp_elab = local_scope.elab_exp(exp, self)?;
                    self.logger.query(Query::Eval { exp: exp_elab })?;
                }
                ModuleItem::Normalize { exp } => {
                    let exp_elab = local_scope.elab_exp(exp, self)?;
                    self.logger.query(Query::Normalize { exp: exp_elab })?;
                }
                ModuleItem::Check { exp, ty } => {
                    let exp_elab = local_scope.elab_exp(exp, self)?;
                    let ty_elab = local_scope.elab_exp(ty, self)?;
                    self.logger.query(Query::Checking {
                        ctx: ctx.clone(),
                        exp: exp_elab,
                        ty: ty_elab,
                    })?;
                }
                ModuleItem::Infer { exp } => {
                    let exp_elab = local_scope.elab_exp(exp, self)?;
                    self.logger.query(Query::Infer {
                        ctx: ctx.clone(),
                        exp: exp_elab,
                    })?;
                }
            }
        }

        // 3. move back to parent
        self.module_manager.moveto_parent();
        self.logger.log(format!("after: {}", self.module_manager));
        Ok(())
    }
}
