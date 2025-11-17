use std::collections::HashMap;

use crate::{
    elaborator::{
        module_manager::{InstantiateResult, ItemAccessResult, ModItemRecord},
        term_elaborator::LocalScope,
    },
    syntax::*,
};
use kernel::{
    calculus::{exp_contains_as_freevar, exp_subst_map},
    exp::*,
    inductive::{self, CtorBinder, InductiveTypeSpecs},
};

mod module_manager;
mod term_elaborator;

pub enum Query {
    Eval { exp: Exp },
    Normalize { exp: Exp },
    Checking { ctx: Context, exp: Exp, ty: Exp },
    Infer { ctx: Context, exp: Exp },
    InferSort { ctx: Context, exp: Exp },
}

#[derive(Debug, Clone)]
pub enum ErrorKind {
    Msg(String),
    DerivationFail(DerivationFail),
}

impl From<String> for ErrorKind {
    fn from(msg: String) -> Self {
        ErrorKind::Msg(msg)
    }
}

impl From<DerivationFail> for ErrorKind {
    fn from(err: DerivationFail) -> Self {
        ErrorKind::DerivationFail(err)
    }
}

pub enum LogEnum {
    Derivation(DerivationSuccess),
    Message(String),
}

// log any derivation steps and messages
// any call of `kernel::derivation` should be call via this logger
// do not use kernel::derivation directly
pub struct Logger {
    log: Vec<LogEnum>,
}

impl Logger {
    pub fn log<T>(&mut self, msg: T)
    where
        T: Into<String>,
    {
        self.log.push(LogEnum::Message(msg.into()));
    }
    pub fn log_derivation(&mut self, der: DerivationSuccess) {
        self.log.push(LogEnum::Derivation(der));
    }
    pub fn query(&mut self, query: Query) -> Result<(), ErrorKind> {
        match query {
            Query::Eval { exp } => match kernel::calculus::reduce_one(&exp) {
                Some(reduced) => {
                    self.log(format!("One step reduction: {}", reduced));
                    Ok(())
                }
                None => {
                    self.log("Expression is in normal form".to_string());
                    Ok(())
                }
            },
            Query::Normalize { exp } => {
                let normalized = kernel::calculus::normalize(&exp);
                self.log(format!("Normalized expression: {}", normalized));
                Ok(())
            }
            Query::Checking { ctx, exp, ty } => {
                let res = kernel::derivation::check(&ctx, &exp, &ty);
                match res {
                    Ok(derivation) => {
                        self.log("Type checking succeeded");
                        self.log_derivation(derivation);
                        Ok(())
                    }
                    Err(err) => Err(ErrorKind::DerivationFail(err)),
                }
            }
            Query::Infer { ctx, exp } => {
                let res = kernel::derivation::infer(&ctx, &exp);
                match res {
                    Ok(derivation) => {
                        let ty = derivation.type_of().unwrap();
                        self.log(format!("Inferred type: {}", ty));
                        self.log_derivation(derivation);
                        Ok(())
                    }
                    Err(err) => Err(ErrorKind::DerivationFail(err)),
                }
            }
            Query::InferSort { ctx, exp } => {
                let res = kernel::derivation::infer_sort(&ctx, &exp);
                match res {
                    Ok(derivation) => {
                        self.log("Inferred sort");
                        self.log_derivation(derivation);
                        Ok(())
                    }
                    Err(err) => Err(ErrorKind::DerivationFail(err)),
                }
            }
        }
    }
    pub fn check(&mut self, ctx: &Context, exp: &Exp, ty: &Exp) -> Result<(), ErrorKind> {
        let der = kernel::derivation::check(ctx, exp, ty);
        match der {
            Ok(derivation) => {
                self.log("Type checking succeeded");
                self.log_derivation(derivation);
                Ok(())
            }
            Err(err) => Err(ErrorKind::DerivationFail(err)),
        }
    }
    pub fn infer(&mut self, ctx: &Context, exp: &Exp) -> Result<Exp, ErrorKind> {
        let der = kernel::derivation::infer(ctx, exp);
        match der {
            Ok(derivation) => {
                let ty = derivation.type_of().unwrap().clone();
                self.log(format!("Inferred type: {}", ty));
                self.log_derivation(derivation);
                Ok(ty)
            }
            Err(err) => Err(ErrorKind::DerivationFail(err)),
        }
    }
    pub fn infer_sort(&mut self, ctx: &Context, exp: &Exp) -> Result<(), ErrorKind> {
        let der = kernel::derivation::infer_sort(ctx, exp);
        match der {
            Ok(derivation) => {
                self.log("Inferred sort");
                self.log_derivation(derivation);
                Ok(())
            }
            Err(err) => Err(ErrorKind::DerivationFail(err)),
        }
    }
    pub fn check_wellformed_indspec(
        &mut self,
        ctx: &Context,
        indspec: &inductive::InductiveTypeSpecs,
    ) -> Result<(), ErrorKind> {
        let der = kernel::inductive::acceptable_typespecs(ctx, indspec);
        match der {
            Ok(derivation) => {
                self.log("Inductive type specs are well-formed");
                self.log_derivation(derivation);
                Ok(())
            }
            Err(err) => Err(ErrorKind::DerivationFail(err)),
        }
    }
}

// do type checking
pub struct GlobalEnvironment {
    logger: Logger, // to pass to elaborator
    module_manager: module_manager::ModuleManager,
    current_imported_modules: HashMap<Identifier, module_manager::InstantiatedModule>,
}

impl Default for GlobalEnvironment {
    fn default() -> Self {
        GlobalEnvironment {
            logger: Logger { log: vec![] },
            module_manager: module_manager::ModuleManager::new(),
            current_imported_modules: HashMap::new(),
        }
    }
}

impl term_elaborator::Handler for GlobalEnvironment {
    fn get_item_from_access_path(
        &mut self,
        access_path: &LocalAccess,
    ) -> Result<ItemAccessResult, ErrorKind> {
        match access_path {
            LocalAccess::Current { access } => {
                let current_module = self.module_manager.current_module_as_instantiated();
                self.logger.log(format!(
                    "\n\nAccessing {:?}: {:?}\n\n",
                    access, current_module,
                ));
                let item = current_module.get_item(access).ok_or_else(|| {
                    ErrorKind::Msg(format!(
                        "Item {} not found in current module",
                        access.as_str()
                    ))
                })?;
                self.logger
                    .log(format!("Found item {:?} in current module\n\n", item));
                Ok(item)
            }
            LocalAccess::Named { access, child } => {
                let imported_module =
                    self.current_imported_modules.get(access).ok_or_else(|| {
                        ErrorKind::Msg(format!("Imported module {} not found", access))
                    })?;
                let item = imported_module.get_item(child).ok_or_else(|| {
                    ErrorKind::Msg(format!(
                        "Item {} not found in imported module {}",
                        child.as_str(),
                        access.as_str()
                    ))
                })?;
                Ok(item)
            }
        }
    }

    fn field_projection(&mut self, e: &Exp, field_name: &Identifier) -> Result<Exp, ErrorKind> {
        let ctx = self
            .module_manager
            .current_context()
            .into_iter()
            .flat_map(|(_, v)| v)
            .collect::<Vec<_>>();

        let infer_type_e = self.logger.infer(&ctx, e)?;
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

        let ModItemRecord {
            type_name,
            fields: field_names,
            rc_spec_as_indtype,
        } = self
            .module_manager
            .get_moditem_record_from_rc(&indspec)
            .ok_or_else(|| ErrorKind::Msg(format!("Inductive type is not a record type",)))?;

        todo!()
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
            "Elaborating module {} with parameters {:?}",
            name.as_str(),
            parameters,
        ));

        let ctx = self
            .module_manager
            .current_context()
            .into_iter()
            .flat_map(|(_, v)| v)
            .collect::<Vec<_>>();

        self.logger.log(format!(
            "current module: {:?}",
            self.module_manager.current_module_as_instantiated()
        ));

        // 2. elaborate declarations
        for decl in declarations {
            self.logger
                .log(format!("Elaborating declaration: {:?}", decl));
            let mut local_scope = LocalScope::default();
            match decl {
                ModuleItem::Definition { name, ty, body } => {
                    let ty_elab = local_scope.elab_exp(ty, self)?;
                    let body_elab = local_scope.elab_exp(body, self)?;
                    let name =
                        self.module_manager.current_path().join(".").to_string() + "." + &name.0;
                    let defined_constant = DefinedConstant {
                        ty: ty_elab,
                        body: body_elab,
                    };
                    self.module_manager.add_def(name.into(), defined_constant);
                }
                ModuleItem::Inductive {
                    type_name,
                    parameters,
                    indices,
                    sort,
                    constructors,
                } => {
                    self.logger.log(format!(
                        "Elaborating inductive type {type_name} {parameters:?}: {indices:?} -> {sort:?}",
                    ));
                    self.logger.log(format!(
                        "With constructors: {:?}",
                        constructors
                            .iter()
                            .map(|(n, r, e)| format!("{} : {:?} {:?}", n.as_str(), r, e))
                            .collect::<Vec<_>>()
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
                            "Elaborating constructor {} with rightbinds {:?} and ends {:?}",
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
                                .log(format!("----  (before elaboration): {:?}", term));
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

                    self.module_manager
                        .add_record(type_name.clone(), fields_get, indspec);
                }
                ModuleItem::ChildModule { module } => {
                    self.module_add_rec(module)?;
                }
                ModuleItem::Import { path, import_name } => {
                    let access_result = match path {
                        ModuleInstantiatePath::FromCurrent { back_parent, calls } => {
                            let mut args = vec![];
                            for call in calls {
                                let args_given_this = call
                                    .1
                                    .iter()
                                    .map(|(id, sexp)| {
                                        let exp_elab = local_scope.elab_exp(sexp, self)?;
                                        Ok((id.clone(), exp_elab))
                                    })
                                    .collect::<Result<Vec<_>, ErrorKind>>()?;
                                args.push((call.0.clone(), args_given_this));
                            }
                            self.module_manager
                                .access_from_current(*back_parent, args)?
                        }
                        ModuleInstantiatePath::FromRoot { calls } => {
                            let mut args = vec![];
                            for call in calls {
                                let args_given_this = call
                                    .1
                                    .iter()
                                    .map(|(id, sexp)| {
                                        let exp_elab = local_scope.elab_exp(sexp, self)?;
                                        Ok((id.clone(), exp_elab))
                                    })
                                    .collect::<Result<Vec<_>, ErrorKind>>()?;
                                args.push((call.0.clone(), args_given_this));
                            }
                            self.module_manager.access_from_root(args)?
                        }
                    };
                    let InstantiateResult {
                        instantiated_module,
                        need_to_type_check,
                    } = access_result;

                    for (_, arg, ty) in need_to_type_check {
                        self.logger.check(&ctx, &arg, &ty)?;
                    }

                    self.current_imported_modules
                        .insert(import_name.clone(), instantiated_module);
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
        Ok(())
    }
}
