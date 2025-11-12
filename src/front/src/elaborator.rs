// NOTE for GitHub Copilot:
// In this compiler, variable handling differs between surface expression and kernel expression levels.
// surface ... `Identifier(String)` for names,
// kernel ... `Var(std::rc::Rc<String>)` as a global ID mechanism
//   each Rc pointer is unique,allowing fresh variables and true binding equality by pointer identity.
// This design makes substitution easier (`subst`), but elaboration must carefully
// align variables between the two levels to preserve correct correspondence.

use std::{collections::HashMap, rc::Rc};

use crate::{
    elaborator::module_manager::{InstantiateResult, ItemAccessResult},
    syntax::*,
};
use kernel::{
    calculus::{exp_contains_as_freevar, exp_subst_map},
    exp::*,
    inductive::{self, CtorBinder, InductiveTypeSpecs},
};

mod module_manager;

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
    pub fn log(&mut self, msg: String) {
        self.log.push(LogEnum::Message(msg));
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
                        self.log(format!("Type checking succeeded"));
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
                        self.log(format!("Inferred sort"));
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
                self.log(format!("Type checking succeeded"));
                self.log_derivation(derivation);
                Ok(())
            }
            Err(err) => Err(ErrorKind::DerivationFail(err)),
        }
    }
    pub fn infer(&mut self, ctx: &Context, exp: &Exp) -> Result<Exp, ErrorKind> {
        let der = kernel::derivation::infer(&ctx, exp);
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
                self.log(format!("Inferred sort"));
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
                self.log(format!("Inductive type specs are well-formed"));
                self.log_derivation(derivation);
                Ok(())
            }
            Err(err) => Err(ErrorKind::DerivationFail(err)),
        }
    }
}

// local scope during elaboration
#[derive(Debug, Clone)]
pub struct LocalScope {
    // for find binded variables inside term
    // lambda abstraction variables, product, subset,
    // after any call of elab_exp outside the elab_exp, this should be cleared
    binded_vars: Vec<Var>,
    // for find decl levels
    decl_binds: Vec<Var>,
    imported_modules: HashMap<Identifier, module_manager::ModuleInstantiated>,
}

impl LocalScope {
    fn get_var(&self, name: &Identifier) -> Option<Var> {
        for v in self.binded_vars.iter().rev() {
            if v.as_str() == name.0.as_str() {
                return Some(v.clone());
            }
        }
        for v in self.decl_binds.iter().rev() {
            if v.as_str() == name.0.as_str() {
                return Some(v.clone());
            }
        }
        None
    }
    fn get_imported_module(
        &self,
        name: &Identifier,
    ) -> Option<&module_manager::ModuleInstantiated> {
        self.imported_modules.get(name)
    }
}

// do type checking
pub struct GlobalEnvironment {
    logger: Logger, // to pass to elaborator
    local_scope: LocalScope,
    module_manager: module_manager::ModuleManager,
}

impl Default for GlobalEnvironment {
    fn default() -> Self {
        GlobalEnvironment {
            logger: Logger { log: vec![] },
            local_scope: LocalScope {
                binded_vars: vec![],
                decl_binds: vec![],
                imported_modules: HashMap::new(),
            },
            module_manager: module_manager::ModuleManager::new(),
        }
    }
}

impl GlobalEnvironment {
    pub fn logs(&self) -> &Vec<LogEnum> {
        &self.logger.log
    }
}

impl GlobalEnvironment {
    fn add_decl_var(&mut self, var: Var) {
        self.local_scope.decl_binds.push(var);
    }
    fn clear_decl_vars(&mut self) {
        self.local_scope.decl_binds.clear();
    }
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
        let ctx: Vec<(Var, Exp)> = self
            .module_manager
            .current_context()
            .into_iter()
            .flat_map(|(_, v)| v)
            .collect();

        let mut subst_mapping = vec![];
        let mut parameters_elab = vec![];
        for RightBind { vars, ty } in parameters.iter() {
            let ty_elab = self.elab_exp(ty)?;
            let ty_substed = exp_subst_map(&ty_elab, &subst_mapping);
            // check sort of parameter type
            self.logger.infer_sort(&ctx, &ty_substed)?;

            for v in vars {
                let v = Var::new(v.as_str());
                subst_mapping.push((v.clone(), ty_substed.clone()));
                parameters_elab.push((v.clone(), ty_substed.clone()));
            }
        }
        // ok => add child module and move to it
        self.module_manager
            .add_child_and_moveto(name.0.clone(), parameters_elab);

        // 2. elaborate declarations
        for decl in declarations {
            self.clear_decl_vars();
            match decl {
                ModuleItem::Definition { name, ty, body } => {
                    let ty_elab = self.elab_exp(ty)?;
                    let body_elab = self.elab_exp(body)?;
                    let name =
                        format!("{}", self.module_manager.current_path().join(".")) + "." + &name.0;
                    let defined_constant = DefinedConstant {
                        name,
                        ty: ty_elab,
                        body: body_elab,
                    };
                    self.module_manager.add_def(defined_constant);
                }
                ModuleItem::Inductive {
                    type_name,
                    parameters,
                    indices,
                    sort,
                    constructors,
                } => {
                    let type_name: Var = type_name.into();
                    // register type name as binded var
                    self.add_decl_var(type_name.clone());

                    // elaborate parameters and indices
                    // binding is memorized in local scope
                    let parameter_elab = self.elab_telescope_bind_in_decl(parameters)?;
                    let indices_elab = self.elab_telescope_bind_in_decl(indices)?;

                    // elaborate constructors
                    let mut ctor_names = vec![];
                    let mut ctor_type_elabs = vec![];

                    for (ctor_name, rightbinds, ends) in constructors {
                        let ctor_name_var: Var = ctor_name.into();
                        ctor_names.push(ctor_name_var.clone());

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
                            let term_elab = self.elab_exp(&term)?;
                            kernel::utils::decompose_prod(term_elab)
                        };

                        let mut ctor_binders = vec![];
                        for (v, e) in telescope {
                            if exp_contains_as_freevar(&e, &type_name) {
                                // strict positive case
                                let (inner_binders, inner_tail) = kernel::utils::decompose_prod(e);
                                for (_, it) in inner_binders.iter() {
                                    if exp_contains_as_freevar(it, &type_name) {
                                        return Err(ErrorKind::Msg(format!(
                                            "Ctor {it} contains inductive type name {type_name} in non-strictly positive position"
                                        )));
                                    }
                                }
                                let (head, tail) = kernel::utils::decompose_app(inner_tail);
                                if !matches!(head, Exp::Var(head_var) if head_var.is_eq_ptr(&type_name))
                                {
                                    return Err(ErrorKind::Msg(format!(
                                        "Constructor binder type head does not match inductive type name {type_name}"
                                    )));
                                }

                                for tail_elm in tail.iter() {
                                    if exp_contains_as_freevar(tail_elm, &type_name) {
                                        return Err(ErrorKind::Msg(format!(
                                            "Constructor binder type tail {tail_elm} contains inductive type name {type_name} in non-strictly positive position"
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
                        if !matches!(head, Exp::Var(head_var) if head_var.is_eq_ptr(&type_name)) {
                            return Err(ErrorKind::Msg(format!(
                                "Constructor type head does not match inductive type name {type_name}"
                            )));
                        }

                        for tail_elm in tail.iter() {
                            if exp_contains_as_freevar(tail_elm, &type_name) {
                                return Err(ErrorKind::Msg(format!(
                                    "Constructor type tail {tail_elm} contains inductive type name {type_name} in non-strictly positive position"
                                )));
                            }
                        }

                        ctor_type_elabs.push(kernel::inductive::CtorType {
                            telescope: ctor_binders,
                            indices: tail,
                        });
                    }
                    // clear decl vars
                    self.clear_decl_vars();

                    let indspec = InductiveTypeSpecs {
                        names: (
                            type_name.as_str().to_string(),
                            ctor_names.iter().map(|v| v.as_str().to_string()).collect(),
                        ),
                        parameters: parameter_elab,
                        indices: indices_elab,
                        sort: *sort,
                        constructors: ctor_type_elabs,
                    };

                    self.logger.check_wellformed_indspec(&ctx, &indspec)?;

                    self.module_manager.add_inductive(indspec);
                }
                ModuleItem::ChildModule { module } => {
                    let save_localscope = self.local_scope.clone();
                    self.module_add_rec(module)?;
                    self.local_scope = save_localscope;
                }
                ModuleItem::Import { path, import_name } => {
                    let access_result = match path {
                        ModuleAccessPath::FromCurrent { back_parent, calls } => {
                            let mut args = vec![];
                            for call in calls {
                                let args_given_this = call
                                    .1
                                    .iter()
                                    .map(|(id, sexp)| {
                                        let exp_elab = self.elab_exp(sexp)?;
                                        Ok((id.clone(), exp_elab))
                                    })
                                    .collect::<Result<Vec<_>, ErrorKind>>()?;
                                args.push((call.0.clone(), args_given_this));
                            }
                            self.module_manager
                                .access_from_current_parent(*back_parent, args)?
                        }
                        ModuleAccessPath::FromRoot { calls } => {
                            let mut args = vec![];
                            for call in calls {
                                let args_given_this = call
                                    .1
                                    .iter()
                                    .map(|(id, sexp)| {
                                        let exp_elab = self.elab_exp(sexp)?;
                                        Ok((id.clone(), exp_elab))
                                    })
                                    .collect::<Result<Vec<_>, ErrorKind>>()?;
                                args.push((call.0.clone(), args_given_this));
                            }
                            self.module_manager.access_from_root(args)?
                        }
                    };
                    let InstantiateResult {
                        module_index: _,
                        instantiated_module,
                        need_to_type_check,
                    } = access_result;

                    for (_, arg, ty) in need_to_type_check {
                        self.logger.check(&ctx, &arg, &ty)?;
                    }

                    self.local_scope
                        .imported_modules
                        .insert(import_name.clone(), instantiated_module);
                }
                ModuleItem::MathMacro { .. } | ModuleItem::UserMacro { .. } => todo!(),
                ModuleItem::Eval { exp } => {
                    let exp_elab = self.elab_exp(exp)?;
                    self.logger.query(Query::Eval { exp: exp_elab })?;
                }
                ModuleItem::Normalize { exp } => {
                    let exp_elab = self.elab_exp(exp)?;
                    self.logger.query(Query::Normalize { exp: exp_elab })?;
                }
                ModuleItem::Check { exp, ty } => {
                    let exp_elab = self.elab_exp(exp)?;
                    let ty_elab = self.elab_exp(ty)?;
                    self.logger.query(Query::Checking {
                        ctx: ctx.clone(),
                        exp: exp_elab,
                        ty: ty_elab,
                    })?;
                }
                ModuleItem::Infer { exp } => {
                    let exp_elab = self.elab_exp(exp)?;
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
    fn elab_telescope_bind_in_decl(
        &mut self,
        v: &Vec<RightBind>,
    ) -> Result<Vec<(Var, Exp)>, ErrorKind> {
        let mut result = vec![];
        for RightBind { vars, ty } in v.iter() {
            let ty_elab = self.elab_exp(ty)?;
            for var in vars {
                let var = Var::new(var.as_str());
                result.push((var.clone(), ty_elab.clone()));
                self.local_scope.decl_binds.push(var);
            }
        }
        Ok(result)
    }

    fn convert_access_path_to_items(
        &self,
        path: &LocalAccess,
    ) -> Result<ItemAccessResult, ErrorKind> {
        let (find_from, item_name) = match path {
            LocalAccess::Current {
                access,
                parameters: _,
            } => {
                let module = self.module_manager.current_module_as_instantiated();
                (module, access.clone())
            }
            LocalAccess::Named {
                access,
                child,
                parameters: _,
            } => {
                let module = match self.local_scope.get_imported_module(access) {
                    Some(m) => m.clone(),
                    None => {
                        return Err(ErrorKind::Msg(format!(
                            "Imported module {} not found",
                            access.as_str()
                        )));
                    }
                };
                (module, child.clone())
            }
        };

        let item = find_from.get_item(&item_name).ok_or_else(|| {
            ErrorKind::Msg(format!(
                "Item {} not found in access path {:?}",
                item_name.as_str(),
                path
            ))
        })?;

        Ok(item)
    }
}

// elaborations
impl GlobalEnvironment {
    fn elab_exp(&mut self, sexp: &SExp) -> Result<Exp, ErrorKind> {
        assert!(self.local_scope.binded_vars.is_empty());
        let e = self.elab_exp_rec(sexp);
        assert!(self.local_scope.binded_vars.is_empty());
        e
    }

    fn push_binded_var(&mut self, var: Var) {
        self.local_scope.binded_vars.push(var);
    }
    fn pop_binded_var(&mut self) {
        self.local_scope.binded_vars.pop();
    }
    // this modifies bind_vars (length += number of vars)
    // after call, caller should pop the binded vars
    fn elab_telescope_rec(&mut self, v: &[RightBind]) -> Result<Vec<(Var, Exp)>, ErrorKind> {
        let mut result = vec![];
        for RightBind { vars, ty } in v.iter() {
            let ty_elab = self.elab_exp(ty)?;
            for var in vars {
                let var = Var::new(var.as_str());
                result.push((var.clone(), ty_elab.clone()));
                self.push_binded_var(var);
            }
        }
        Ok(result)
    }

    fn elab_exp_rec(&mut self, sexp: &SExp) -> Result<Exp, ErrorKind> {
        match sexp {
            SExp::AccessPath(local_access) => {
                // 1. find from local_scope ... if LocalAccess::Current and has Some() get_var

                if let LocalAccess::Current { access, parameters } = local_access {
                    // 1. binded in local scope
                    if let Some(v) = self.local_scope.get_var(access) {
                        if parameters.is_empty() {
                            return Ok(Exp::Var(v));
                        } else {
                            return Err(ErrorKind::Msg(format!(
                                "Variable {} cannot be applied with parameters",
                                access.as_str()
                            )));
                        }
                    }
                }

                // 2. find from modules
                let item = self.convert_access_path_to_items(local_access)?;

                match item {
                    ItemAccessResult::Definition { rc } => {
                        if local_access.parameters().is_empty() {
                            return Ok(Exp::DefinedConstant(rc.clone()));
                        } else {
                            return Err(ErrorKind::Msg(format!(
                                "Defined constant {} cannot be applied with parameters",
                                rc.name.as_str()
                            )));
                        }
                    }
                    ItemAccessResult::Inductive { ind_defs } => {
                        let parameters: Vec<Exp> = local_access
                            .parameters()
                            .iter()
                            .map(|e| self.elab_exp_rec(e))
                            .collect::<Result<_, _>>()?;
                        return Ok(Exp::IndType {
                            indspec: ind_defs.clone(),
                            parameters,
                        });
                    }
                    ItemAccessResult::Parameter { exp } => {
                        if local_access.parameters().is_empty() {
                            return Ok(exp.clone());
                        } else {
                            return Err(ErrorKind::Msg(format!(
                                "Module parameter {} cannot be applied with parameters",
                                exp
                            )));
                        }
                    }
                }
            }
            SExp::MathMacro { .. } | SExp::NamedMacro { .. } => todo!(),
            SExp::Where { exp, clauses } => {
                // elaborate clauses, register name
                // then subst var to defconst in exp

                let mut where_def_rcs_substmap: Vec<(Var, Exp)> = vec![];
                for (name, ty, body) in clauses {
                    let ty = self.elab_exp_rec(ty)?;
                    let body = self.elab_exp_rec(body)?;
                    let def_cst = DefinedConstant {
                        name: format!("<where {}>", name.as_str()),
                        ty,
                        body,
                    };
                    let def_rc = Rc::new(def_cst);
                    let name: Var = Var::new(name.as_str());
                    where_def_rcs_substmap.push((name, Exp::DefinedConstant(def_rc)));
                }

                let exp_elab = self.elab_exp_rec(exp)?;

                Ok(exp_subst_map(&exp_elab, &where_def_rcs_substmap))
            }
            SExp::WithProofs { exp, proofs } => {
                let exp_elab = self.elab_exp_rec(exp)?;
                let mut proof_goals: Vec<ProveGoal> = vec![];
                for proof in proofs {
                    let GoalProof {
                        extended_ctx,
                        goal,
                        proofby: proof_term,
                    } = proof;
                    let extended_ctx_elab = self.elab_telescope_rec(extended_ctx)?;
                    //
                    let goal_elab = self.elab_exp_rec(goal)?;
                    let proof_term_elab = self.elab_proof_by_rec(proof_term)?;

                    for _ in 0..extended_ctx_elab.len() {
                        self.pop_binded_var();
                    }

                    proof_goals.push(ProveGoal {
                        extended_ctx: extended_ctx_elab,
                        goal_prop: goal_elab,
                        command: proof_term_elab,
                    });
                }
                Ok(Exp::ProveHere {
                    exp: exp_elab.into(),
                    goals: proof_goals,
                })
            }
            SExp::Sort(sort) => Ok(Exp::Sort(*sort)),
            SExp::Prod { bind, body } | SExp::Lam { bind, body } => {
                let is_prod = matches!(sexp, SExp::Prod { .. });
                match bind {
                    Bind::Anonymous { ty } => {
                        let ty_elab = self.elab_exp_rec(ty)?;
                        let body_elab = self.elab_exp_rec(body)?;
                        Ok(if is_prod {
                            Exp::Prod {
                                var: Var::dummy(),
                                ty: Box::new(ty_elab),
                                body: Box::new(body_elab),
                            }
                        } else {
                            Exp::Lam {
                                var: Var::dummy(),
                                ty: Box::new(ty_elab),
                                body: Box::new(body_elab),
                            }
                        })
                    }
                    Bind::Named(right_bind) => {
                        let ty_elab = self.elab_exp_rec(&right_bind.ty)?;

                        let mut telescope: Vec<(Var, Exp)> = vec![];
                        for var in &right_bind.vars {
                            let var: Var = Var::new(var.as_str());
                            telescope.push((var.clone(), ty_elab.clone()));
                            self.push_binded_var(var);
                        }

                        let body_elab = self.elab_exp_rec(body)?;

                        for _ in &right_bind.vars {
                            self.pop_binded_var();
                        }

                        Ok(if is_prod {
                            kernel::utils::assoc_prod(telescope, body_elab)
                        } else {
                            kernel::utils::assoc_lam(telescope, body_elab)
                        })
                    }
                    Bind::Subset { var, ty, predicate } => {
                        let ty_elab = self.elab_exp_rec(ty)?;
                        let var: Var = Var::new(var.as_str());
                        self.push_binded_var(var.clone());
                        let predicate_elab = self.elab_exp_rec(predicate)?;
                        let body_elab = self.elab_exp_rec(body)?;
                        self.pop_binded_var();

                        let subset = Exp::SubSet {
                            var: var.clone(),
                            set: Box::new(ty_elab.clone()),
                            predicate: Box::new(predicate_elab.clone()),
                        };

                        let ty_elab = Box::new(Exp::TypeLift {
                            superset: Box::new(ty_elab.clone()),
                            subset: Box::new(subset),
                        });

                        Ok(if is_prod {
                            Exp::Prod {
                                var: var.clone(),
                                ty: ty_elab,
                                body: Box::new(body_elab),
                            }
                        } else {
                            Exp::Lam {
                                var: var.clone(),
                                ty: ty_elab,
                                body: Box::new(body_elab),
                            }
                        })
                    }
                    Bind::SubsetWithProof {
                        var,
                        ty,
                        predicate,
                        proof_var,
                    } => {
                        let ty_elab = self.elab_exp_rec(ty)?;
                        let var: Var = Var::new(var.as_str());
                        self.push_binded_var(var.clone());
                        let predicate_elab = self.elab_exp_rec(predicate)?;
                        let proof: Var = Var::new(proof_var.as_str());
                        self.push_binded_var(proof.clone());
                        let body_elab = self.elab_exp_rec(body)?;
                        self.pop_binded_var();
                        self.pop_binded_var();

                        let subset = Exp::SubSet {
                            var: var.clone(),
                            set: Box::new(ty_elab.clone()),
                            predicate: Box::new(predicate_elab.clone()),
                        };

                        let ty_elab = Box::new(Exp::TypeLift {
                            superset: Box::new(ty_elab.clone()),
                            subset: Box::new(subset),
                        });
                        let body_elab = Box::new(Exp::Prod {
                            var: proof,
                            ty: Box::new(predicate_elab),
                            body: Box::new(body_elab),
                        });

                        Ok(if is_prod {
                            Exp::Prod {
                                var: var.clone(),
                                ty: ty_elab,
                                body: body_elab,
                            }
                        } else {
                            Exp::Lam {
                                var: var.clone(),
                                ty: ty_elab,
                                body: body_elab,
                            }
                        })
                    }
                }
            }
            SExp::App {
                func,
                arg,
                piped: _,
            } => {
                let func_elab = self.elab_exp_rec(func)?;
                let arg_elab = self.elab_exp_rec(arg)?;
                Ok(Exp::App {
                    func: Box::new(func_elab),
                    arg: Box::new(arg_elab),
                })
            }
            SExp::Cast { exp, to } => {
                let exp_elab = self.elab_exp_rec(exp)?;
                let to_elab = self.elab_exp_rec(to)?;
                Ok(Exp::Cast {
                    exp: Box::new(exp_elab),
                    to: Box::new(to_elab),
                })
            }
            SExp::IndCtor { path, ctor_name } => {
                let item = self.convert_access_path_to_items(path)?;

                let ItemAccessResult::Inductive { ind_defs: indspec } = item else {
                    return Err(ErrorKind::Msg(format!(
                        "Expected inductive type in path {:?}",
                        path
                    )));
                };

                let parameters: Vec<Exp> = path
                    .parameters()
                    .iter()
                    .map(|e| self.elab_exp_rec(e))
                    .collect::<Result<_, _>>()?;

                let idx = indspec
                    .ctor_idx_from_name(ctor_name.as_str())
                    .ok_or_else(|| {
                        ErrorKind::Msg(format!(
                            "Constructor {} not found in inductive type {}",
                            ctor_name.as_str(),
                            indspec.names.0
                        ))
                    })?;

                Ok(Exp::IndCtor {
                    indspec,
                    parameters,
                    idx,
                })
            }
            SExp::IndElim {
                path,
                elim,
                return_type,
                cases,
            } => {
                let item = self.convert_access_path_to_items(path)?;
                let ItemAccessResult::Inductive { ind_defs: indspec } = item else {
                    return Err(ErrorKind::Msg(format!(
                        "Expected inductive type in path {:?}",
                        path
                    )));
                };
                let elim_elab = self.elab_exp_rec(elim)?;
                let return_type_elab = self.elab_exp_rec(return_type)?;
                let mut cases_elab: Vec<Exp> = vec![];
                for (ctor_name, case) in cases {
                    let case_elab = self.elab_exp_rec(case)?;
                    let ctor_idx =
                        indspec
                            .ctor_idx_from_name(ctor_name.as_str())
                            .ok_or_else(|| {
                                ErrorKind::Msg(format!(
                                    "Constructor {} not found in inductive type {}",
                                    ctor_name.as_str(),
                                    indspec.names.0
                                ))
                            })?;
                    if ctor_idx != cases_elab.len() {
                        return Err(ErrorKind::Msg(format!(
                            "Constructor cases are not in order in ind elim for inductive type {}",
                            indspec.names.0
                        )));
                    }
                    cases_elab.push(case_elab);
                }
                Ok(Exp::IndElim {
                    indspec,
                    elim: Box::new(elim_elab),
                    return_type: Box::new(return_type_elab),
                    cases: cases_elab,
                })
            }
            SExp::IndElimPrim { path, sort } => {
                let item = self.convert_access_path_to_items(path)?;
                let ItemAccessResult::Inductive { ind_defs: indspec } = item else {
                    return Err(ErrorKind::Msg(format!(
                        "Expected inductive type in path {:?}",
                        path
                    )));
                };
                let parameters: Vec<Exp> = path
                    .parameters()
                    .iter()
                    .map(|e| self.elab_exp_rec(e))
                    .collect::<Result<_, _>>()?;
                Ok(InductiveTypeSpecs::primitive_recursion(
                    &indspec, parameters, *sort,
                ))
            }
            SExp::ProveLater { prop: term } => {
                let term_elab = self.elab_exp_rec(term)?;
                Ok(Exp::ProveLater {
                    prop: Box::new(term_elab),
                })
            }
            SExp::PowerSet { set } => {
                let set_elab = self.elab_exp_rec(set)?;
                Ok(Exp::PowerSet {
                    set: Box::new(set_elab),
                })
            }
            SExp::SubSet {
                var,
                set,
                predicate,
            } => {
                let set_elab = self.elab_exp_rec(set)?;
                let var: Var = Var::new(var.as_str());
                self.push_binded_var(var.clone());
                let predicate_elab = self.elab_exp_rec(predicate)?;
                self.pop_binded_var();
                Ok(Exp::SubSet {
                    var: var.clone(),
                    set: Box::new(set_elab),
                    predicate: Box::new(predicate_elab),
                })
            }
            SExp::Pred {
                superset,
                subset,
                element,
            } => {
                let superset_elab = self.elab_exp_rec(superset)?;
                let subset_elab = self.elab_exp_rec(subset)?;
                let element_elab = self.elab_exp_rec(element)?;
                Ok(Exp::Pred {
                    superset: Box::new(superset_elab),
                    subset: Box::new(subset_elab),
                    element: Box::new(element_elab),
                })
            }
            SExp::TypeLift { superset, subset } => {
                let superset_elab = self.elab_exp_rec(superset)?;
                let subset_elab = self.elab_exp_rec(subset)?;
                Ok(Exp::TypeLift {
                    superset: Box::new(superset_elab),
                    subset: Box::new(subset_elab),
                })
            }
            SExp::Equal { left, right } => {
                let left_elab = self.elab_exp_rec(left)?;
                let right_elab = self.elab_exp_rec(right)?;
                Ok(Exp::Equal {
                    left: Box::new(left_elab),
                    right: Box::new(right_elab),
                })
            }
            // this is non emptyness of type ... Exp::Exists { set: Box<Exp> }
            SExp::Exists { bind } => match bind {
                Bind::Named(_) | Bind::SubsetWithProof { .. } => Err(ErrorKind::Msg(
                    "Elaboration of named bind or subset with proof in Exists is not implemented"
                        .to_string(),
                )),
                Bind::Anonymous { ty } => {
                    let ty_elab = self.elab_exp_rec(ty)?;
                    Ok(Exp::Exists {
                        set: Box::new(ty_elab),
                    })
                }
                Bind::Subset { var, ty, predicate } => {
                    let subset_as_exp = {
                        let ty_elab = self.elab_exp_rec(ty)?;
                        let var: Var = Var::new(var.as_str());
                        self.push_binded_var(var.clone());
                        let predicate_elab = self.elab_exp_rec(predicate)?;
                        self.pop_binded_var();

                        Exp::SubSet {
                            var: var.clone(),
                            set: Box::new(ty_elab.clone()),
                            predicate: Box::new(predicate_elab.clone()),
                        }
                    };
                    Ok(Exp::Exists {
                        set: Box::new(subset_as_exp),
                    })
                }
            },
            SExp::Take { bind, body } => {
                // elab as SExp::Lam {bind, body}
                let map = SExp::Lam {
                    bind: bind.clone(),
                    body: body.clone(),
                };
                let map_elab = self.elab_exp_rec(&map)?;
                Ok(Exp::Take {
                    map: Box::new(map_elab),
                })
            }
            SExp::ProofTermRaw(proof_by) => {
                let proof_by_elab = self.elab_proof_by_rec(proof_by)?;
                Ok(Exp::ProofTermRaw {
                    command: Box::new(proof_by_elab),
                })
            }
            SExp::Block(block) => {
                let Block {
                    statements: declarations,
                    result: term,
                } = block;
                let mut term = term.as_ref().clone();
                for decl in declarations.iter().rev() {
                    match decl {
                        Statement::Fix(items) => {
                            for bind in items.iter().rev() {
                                term = SExp::Lam {
                                    bind: Bind::Named(bind.clone()),
                                    body: Box::new(term),
                                };
                            }
                        }
                        Statement::Let { var, ty, body } => {
                            term = SExp::App {
                                func: Box::new(SExp::Lam {
                                    bind: Bind::Named(RightBind {
                                        vars: vec![var.clone()],
                                        ty: Box::new(ty.clone()),
                                    }),
                                    body: Box::new(term),
                                }),
                                arg: Box::new(body.clone()),
                                piped: false,
                            };
                        }
                        Statement::Take { bind } => {
                            term = SExp::Take {
                                bind: bind.clone(),
                                body: Box::new(term),
                            };
                        }
                        Statement::Sufficient { map, map_ty } => {
                            term = SExp::App {
                                func: Box::new(SExp::Cast {
                                    exp: Box::new(map.clone()),
                                    to: Box::new(map_ty.clone()),
                                }),
                                arg: Box::new(term),
                                piped: false,
                            };
                        }
                    }
                }
                self.elab_exp_rec(&term)
            }
        }
    }
    fn elab_proof_by_rec(
        &mut self,
        proof_by: &SProveCommandBy,
    ) -> Result<ProveCommandBy, ErrorKind> {
        let elab = match proof_by {
            SProveCommandBy::Construct { term } => {
                let term_elab = self.elab_exp_rec(term)?;
                ProveCommandBy::Construct(term_elab)
            }
            SProveCommandBy::Exact { term, set } => {
                let term_elab = self.elab_exp_rec(term)?;
                let set_elab = self.elab_exp_rec(set)?;
                ProveCommandBy::ExactElem {
                    elem: term_elab,
                    ty: set_elab,
                }
            }
            SProveCommandBy::SubsetElim {
                superset,
                subset,
                elem,
            } => {
                let superset_elab = self.elab_exp_rec(superset)?;
                let subset_elab = self.elab_exp_rec(subset)?;
                let elem_elab = self.elab_exp_rec(elem)?;
                ProveCommandBy::SubsetElim {
                    superset: superset_elab,
                    subset: subset_elab,
                    elem: elem_elab,
                }
            }
            SProveCommandBy::IdRefl { term } => {
                let term_elab = self.elab_exp_rec(term)?;
                ProveCommandBy::IdRefl { elem: term_elab }
            }
            SProveCommandBy::IdElim {
                left,
                right,
                var,
                ty,
                predicate,
            } => {
                let left_elab = self.elab_exp_rec(left)?;
                let right_elab = self.elab_exp_rec(right)?;
                let var: Var = var.into();
                let mut bind_var = vec![];
                bind_var.push(var.clone());
                let ty_elab = self.elab_exp_rec(ty)?;
                let predicate_elab = self.elab_exp_rec(predicate)?;
                ProveCommandBy::IdElim {
                    left: left_elab,
                    right: right_elab,
                    var,
                    ty: ty_elab,
                    predicate: predicate_elab,
                }
            }
            SProveCommandBy::TakeEq {
                func,
                elem,
                domain,
                codomain,
            } => {
                let func_elab = self.elab_exp_rec(func)?;
                let domain_elab = self.elab_exp_rec(domain)?;
                let codomain_elab = self.elab_exp_rec(codomain)?;
                let elem_elab = self.elab_exp_rec(elem)?;
                ProveCommandBy::TakeEq {
                    func: func_elab,
                    domain: domain_elab,
                    codomain: codomain_elab,
                    elem: elem_elab,
                }
            }
            SProveCommandBy::Axiom(_) => {
                todo!("not yet implemented axiom")
            }
        };
        Ok(elab)
    }
}
