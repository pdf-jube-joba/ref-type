// NOTE for GitHub Copilot:
// In this compiler, variable handling differs between surface expression and kernel expression levels.
// surface ... `Identifier(String)` for names,
// kernel ... `Var(std::rc::Rc<String>)` as a global ID mechanism
//   each Rc pointer is unique,allowing fresh variables and true binding equality by pointer identity.
// This design makes substitution easier (`subst`), but elaboration must carefully
// align variables between the two levels to preserve correct correspondence.

use std::collections::HashMap;

use crate::syntax::*;
use either::Either;
use kernel::{
    calculus::{exp_contains_as_freevar, exp_subst_map},
    exp::*,
    inductive::{CtorBinder, InductiveTypeSpecs},
};

#[derive(Debug, Clone)]
pub enum Item {
    Definition {
        name: Var,
        ty: Exp,
        body: Exp,
    },
    Inductive {
        name: Var,
        ctor_names: Vec<Var>,
        ind_defs: std::rc::Rc<kernel::inductive::InductiveTypeSpecs>,
    },
    Import {
        module_name: Var,
        import_name: Var,
        args: Vec<(Var, Exp)>,
    },
}

impl Item {
    fn subst(&self, subst_mapping: &[(Var, Exp)]) -> Item {
        match self {
            Item::Definition { name, ty, body } => Item::Definition {
                name: name.clone(),
                ty: exp_subst_map(ty, subst_mapping),
                body: exp_subst_map(body, subst_mapping),
            },
            Item::Inductive {
                name,
                ctor_names,
                ind_defs,
            } => Item::Inductive {
                name: name.clone(),
                ctor_names: ctor_names.clone(),
                ind_defs: std::rc::Rc::new(ind_defs.subst(subst_mapping)),
            },
            Item::Import {
                module_name,
                import_name,
                args,
            } => Item::Import {
                module_name: module_name.clone(),
                import_name: import_name.clone(),
                args: args
                    .iter()
                    .map(|(v, e)| (v.clone(), exp_subst_map(e, subst_mapping)))
                    .collect(),
            },
        }
    }
}

pub enum Query {
    Eval { exp: Exp },
    Normalize { exp: Exp },
    Checking { exp: Exp, ty: Exp },
    Infer { exp: Exp },
}

// do type checking
pub struct GlobalEnvironment {
    module_templates: Vec<ModuleResolved>,
    elaborator: Elaborator,
    logger: Logger, // to pass to elaborator
}

impl GlobalEnvironment {
    pub fn logs(&self) -> &Vec<Either<DerivationSuccess, String>> {
        &self.logger.log
    }
}

pub struct Logger {
    log: Vec<Either<DerivationSuccess, String>>,
}

impl Logger {
    pub fn log_derivation(&mut self, der: DerivationSuccess) {
        self.log.push(Either::Left(der));
    }
    pub fn log(&mut self, msg: String) {
        self.log.push(Either::Right(format!("{msg}\n")));
    }
}

impl Default for GlobalEnvironment {
    fn default() -> Self {
        GlobalEnvironment {
            module_templates: vec![],
            elaborator: Elaborator {
                parameters: vec![],
                realized: HashMap::new(),
                items: vec![],
            },
            logger: Logger { log: vec![] },
        }
    }
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
    fn from(der_fail: DerivationFail) -> Self {
        ErrorKind::DerivationFail(der_fail)
    }
}

impl GlobalEnvironment {
    // add derivation log to global log
    // return Some(true) if derivation is successful without goal
    // return Some(false) if derivation is successful with unproved goals
    // return None if derivation is failed
    pub fn add_derivation(&mut self, der: DerivationSuccess) {
        self.logger.log_derivation(der);
    }
    pub fn new_module(&mut self, module: &Module) -> Result<(), ErrorKind> {
        let Module {
            name,
            parameters,
            declarations,
        } = module;

        self.logger
            .log(format!("Elaborating module {}", name.0.as_str()));

        // elaborator setup
        {
            // reset
            self.elaborator = Elaborator {
                parameters: vec![],
                realized: HashMap::new(),
                items: vec![],
            };

            // get elaborated parameters
            let parameters_elab = self
                .elaborator
                .elab_telescope(&mut self.logger, parameters)?;

            // sort check parameter's ty
            for (v, ty) in parameters_elab.iter() {
                self.logger
                    .log(format!("Checking parameter {} : {}", v.as_str(), ty));
                let der = kernel::derivation::infer_sort(&self.elaborator.parameters, ty)?;
                self.add_derivation(der);

                // a parameter may depends on previous parameters
                self.elaborator.parameters.push((v.clone(), ty.clone()));
            }
        }

        // chek well-formedness of items
        {
            for item in declarations {
                self.logger.log(format!("Checking item {:?}", item));
                let item_elab = self.elaborator.elab_item(&mut self.logger, item)?;

                let item_elab = match item_elab {
                    Either::Left(left) => left,
                    Either::Right(right) => {
                        match right {
                            Query::Eval { exp } => {
                                let after = kernel::calculus::normalize(&exp);
                                self.logger.log(format!("Eval result: {}", after));
                            }
                            Query::Normalize { exp } => {
                                let after = kernel::calculus::normalize(&exp);
                                self.logger.log(format!("Normalize result: {}", after));
                            }
                            Query::Checking { exp, ty } => {
                                let der = kernel::derivation::check(
                                    &self.elaborator.parameters,
                                    &exp,
                                    &ty,
                                )?;
                                self.add_derivation(der);
                            }
                            Query::Infer { exp } => {
                                let der =
                                    kernel::derivation::infer(&self.elaborator.parameters, &exp)?;
                                let ty = der.type_of().unwrap().clone();
                                self.logger.log(format!("Inferred type: {}", ty));
                                self.add_derivation(der);
                            }
                        }
                        continue;
                    }
                };

                match &item_elab {
                    Item::Definition { name: _, ty, body } => {
                        let der = kernel::derivation::check(&self.elaborator.parameters, body, ty)?;
                        self.add_derivation(der);
                    }
                    Item::Inductive {
                        name: _,
                        ctor_names: _,
                        ind_defs,
                    } => {
                        let der = kernel::inductive::acceptable_typespecs(
                            &self.elaborator.parameters,
                            ind_defs,
                        )?;
                        self.add_derivation(der);
                    }
                    Item::Import {
                        module_name,
                        import_name,
                        args,
                    } => {
                        let module_template = match self
                            .module_templates
                            .iter()
                            .rev()
                            .find(|m| m.name.as_str() == module_name.as_str())
                        {
                            Some(m) => m.clone(),
                            None => {
                                return Err(format!(
                                    "Imported module template {} not found",
                                    module_name.as_str()
                                )
                                .into());
                            }
                        };

                        if module_template.parameters.len() != args.len() {
                            return Err(format!(
                                "Imported module expects {} arguments, but {} were provided",
                                module_template.parameters.len(),
                                args.len()
                            )
                            .into());
                        }

                        // type check
                        {
                            let mut subst_maps = vec![];
                            for ((v0, arg), (v1, ty)) in
                                args.iter().zip(module_template.parameters.iter())
                            {
                                // we need to check name string match and subst with it
                                if v0.as_str() != v1.as_str() {
                                    return Err(format!(
                                        "Imported module argument name {} does not match parameter name {}",
                                        v0.as_str(),
                                        v1.as_str()
                                    ).into());
                                }

                                let ty_substed = exp_subst_map(ty, &subst_maps);
                                let der = kernel::derivation::check(
                                    &self.elaborator.parameters,
                                    arg,
                                    &ty_substed,
                                )?;
                                self.add_derivation(der);
                                subst_maps.push((v1.clone(), arg.clone()));
                            }
                        }
                        let realized = module_template
                            .realize(args.iter().map(|(_, e)| e.clone()).collect::<Vec<_>>());
                        self.elaborator
                            .realized
                            .insert(import_name.as_str().into(), realized);
                    }
                }
                self.elaborator.items.push(item_elab);
            }
        }

        self.module_templates.push(ModuleResolved {
            name: Var::new(name.0.as_str()),
            parameters: self.elaborator.parameters.clone(),
            items: self.elaborator.items.clone(),
        });

        Ok(())
    }
}

// elaborator does not type check
pub struct Elaborator {
    parameters: Vec<(Var, Exp)>,
    realized: HashMap<Identifier, ModuleRealized>,
    items: Vec<Item>, // previously elaborated items
}

// resolve path
// len == 1 => locally binded variable | current module defined item (definition, inductive type name) | module parameter
// len == 2 => current module's inductive type constructor access | named module's item access
// len == 3 => named module's inductive type constructor access
// in the case of inductive type of constructors, we need to uncurry with tails
// the other cases, elaborate with tails
impl Elaborator {
    // return Either::Left(exp) for Definition
    // return Either::Right((specs, None)) for IndType
    // return Either::Right((specs, Some(idx))) for IndCtor
    #[allow(clippy::type_complexity)]
    fn get_item_from_path(
        &self,
        path: &[Identifier],
    ) -> Option<Either<Exp, (std::rc::Rc<InductiveTypeSpecs>, Option<usize>)>> {
        match path {
            // current module's inductive type or definition
            [ident] => {
                // check from module item
                for item in self.items.iter().rev() {
                    match item {
                        Item::Definition { name, ty: _, body }
                            if name.as_str() == ident.0.as_str() =>
                        {
                            return Some(Either::Left(body.clone()));
                        }
                        Item::Inductive {
                            name,
                            ctor_names,
                            ind_defs,
                        } if name.as_str() == ident.0.as_str() => {
                            // check ctor names
                            for (idx, _) in ctor_names.iter().enumerate() {
                                if ident.0.as_str() == ctor_names[idx].as_str() {
                                    return Some(Either::Right((ind_defs.clone(), Some(idx))));
                                }
                            }
                            return Some(Either::Right((ind_defs.clone(), None)));
                        }
                        _ => {
                            continue;
                        }
                    }
                }

                None
            }
            // current module's inductive constructor or named module's item
            [path0, path1] => {
                // check current module's inductive constructor
                for item in self.items.iter().rev() {
                    if let Item::Inductive {
                        name: ind_name,
                        ctor_names,
                        ind_defs,
                    } = item
                        && ind_name.as_str() == path0.0.as_str()
                    {
                        for (idx, ctor_name_item) in ctor_names.iter().enumerate() {
                            if ctor_name_item.as_str() == path1.0.as_str() {
                                return Some(Either::Right((ind_defs.clone(), Some(idx))));
                            }
                        }
                    }
                }
                // check named module's definition or inductive type
                let module_realized = self.realized.get(path0)?;
                for item in module_realized.items.iter().rev() {
                    match item {
                        Item::Definition {
                            name: def_name,
                            ty: _,
                            body,
                        } if def_name.as_str() == path1.0.as_str() => {
                            return Some(Either::Left(body.clone()));
                        }
                        Item::Inductive {
                            name: ind_name,
                            ctor_names: _,
                            ind_defs,
                        } if ind_name.as_str() == path1.0.as_str() => {
                            return Some(Either::Right((ind_defs.clone(), None)));
                        }
                        _ => {
                            continue;
                        }
                    }
                }

                None
            }
            // named module's inductive constructor
            [path0, path1, path2] => {
                let module_realized = self.realized.get(path0)?;

                for item in module_realized.items.iter().rev() {
                    if let Item::Inductive {
                        name: ind_name,
                        ctor_names,
                        ind_defs,
                    } = item
                        && ind_name.as_str() == path1.0.as_str()
                    {
                        for (idx, ctor_name_item) in ctor_names.iter().enumerate() {
                            if ctor_name_item.as_str() == path2.0.as_str() {
                                return Some(Either::Right((ind_defs.clone(), Some(idx))));
                            }
                        }
                    }
                }

                None
            }
            _ => None,
        }
    }
}

impl Elaborator {
    fn elab_item(
        &mut self,
        logger: &mut Logger,
        item: &crate::syntax::ModuleItem,
    ) -> Result<Either<Item, Query>, String> {
        match item {
            ModuleItem::Definition {
                name: var,
                ty,
                body,
            } => {
                let var: Var = var.into();
                let ty_elab = self.elab_exp(logger, ty, &[])?;
                let body_elab = self.elab_exp(logger, body, &[])?;
                Ok(Either::Left(Item::Definition {
                    name: var,
                    ty: ty_elab,
                    body: body_elab,
                }))
            }
            ModuleItem::Inductive {
                type_name,
                parameters,
                arity,
                constructors,
            } => {
                let type_name: Var = type_name.into();

                // elaborate parameters
                let parameter_elab = self.elab_telescope(logger, parameters)?;

                // elaborate arity and decompose to (x[0]: A[0]) -> ... -> (x[n]: A[n]) -> Sort
                let arity_elab = self.elab_exp(logger, arity, &[])?;
                let (indices_elab, sort) = kernel::utils::decompose_prod(arity_elab);
                let Exp::Sort(sort) = sort else {
                    return Err(format!(
                        "Inductive type arity {arity:?} does not end with a Sort"
                    ));
                };

                // elaborate constructors
                let mut ctor_names = vec![];
                let mut ctor_type_elabs = vec![];

                for (ctor_name, ctor_args) in constructors {
                    let ctor_name_var: Var = ctor_name.into();
                    ctor_names.push(ctor_name_var.clone());

                    // elaborate constructor type and decompose to telescope and tails
                    let ctor_type_elab =
                        self.elab_exp(logger, ctor_args, std::slice::from_ref(&type_name))?;
                    let (telescope, tails) = kernel::utils::decompose_prod(ctor_type_elab);

                    let mut ctor_binders = vec![];
                    for (v, e) in telescope {
                        if exp_contains_as_freevar(&e, &type_name) {
                            // strict positive case
                            let (inner_binders, inner_tail) = kernel::utils::decompose_prod(e);
                            for (_, it) in inner_binders.iter() {
                                if exp_contains_as_freevar(it, &type_name) {
                                    return Err(format!(
                                        "Constructor binder type {it} contains inductive type name {type_name} in non-strictly positive position"
                                    ));
                                }
                            }
                            let (head, tail) = kernel::utils::decompose_app(inner_tail);
                            if !matches!(head, Exp::Var(head_var) if head_var.is_eq_ptr(&type_name))
                            {
                                return Err(format!(
                                    "Constructor binder type head does not match inductive type name {type_name}"
                                ));
                            }

                            for tail_elm in tail.iter() {
                                if exp_contains_as_freevar(tail_elm, &type_name) {
                                    return Err(format!(
                                        "Constructor binder type tail {tail_elm} contains inductive type name {type_name} in non-strictly positive position"
                                    ));
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

                    let (head, tail) = kernel::utils::decompose_app(tails);
                    if !matches!(head, Exp::Var(head_var) if head_var.is_eq_ptr(&type_name)) {
                        return Err(format!(
                            "Constructor type head does not match inductive type name {type_name}"
                        ));
                    }

                    for tail_elm in tail.iter() {
                        if exp_contains_as_freevar(tail_elm, &type_name) {
                            return Err(format!(
                                "Constructor type tail {tail_elm} contains inductive type name {type_name} in non-strictly positive position"
                            ));
                        }
                    }

                    ctor_type_elabs.push(kernel::inductive::CtorType {
                        telescope: ctor_binders,
                        indices: tail,
                    });
                }

                let indtype_specs = InductiveTypeSpecs {
                    names: (
                        type_name.as_str().to_string(),
                        ctor_names.iter().map(|v| v.as_str().to_string()).collect(),
                    ),
                    parameters: parameter_elab,
                    indices: indices_elab,
                    sort,
                    constructors: ctor_type_elabs,
                };

                Ok(Either::Left(Item::Inductive {
                    name: type_name,
                    ctor_names,
                    ind_defs: std::rc::Rc::new(indtype_specs),
                }))
            }
            ModuleItem::Import {
                path:
                    ModuleInstantiated {
                        module_name, // will be not yet realized ... deligate every thing to global
                        arguments,
                    },
                import_name,
            } => {
                let args_elab = arguments
                    .iter()
                    .map(|(v, e)| {
                        let v: Var = v.into();
                        let e_elab = self.elab_exp(logger, e, &[])?;
                        Ok((v, e_elab))
                    })
                    .collect::<Result<Vec<_>, String>>()?;

                Ok(Either::Left(Item::Import {
                    module_name: Var::new(module_name.0.as_str()),
                    import_name: Var::new(import_name.0.as_str()),
                    args: args_elab,
                }))
            }
            ModuleItem::MathMacro { .. } | ModuleItem::UserMacro { .. } => todo!(),
            ModuleItem::Eval { exp } => {
                let exp_elab = self.elab_exp(logger, exp, &[])?;
                Ok(Either::Right(Query::Eval { exp: exp_elab }))
            }
            ModuleItem::Normalize { exp } => {
                let exp_elab = self.elab_exp(logger, exp, &[])?;
                Ok(Either::Right(Query::Normalize { exp: exp_elab }))
            }
            ModuleItem::Check { exp, ty } => {
                let exp_elab = self.elab_exp(logger, exp, &[])?;
                let ty_elab = self.elab_exp(logger, ty, &[])?;
                Ok(Either::Right(Query::Checking {
                    exp: exp_elab,
                    ty: ty_elab,
                }))
            }
            ModuleItem::Infer { exp } => {
                let exp_elab = self.elab_exp(logger, exp, &[])?;
                Ok(Either::Right(Query::Infer { exp: exp_elab }))
            }
        }
    }
    fn elab_exp(
        &mut self,
        logger: &mut Logger,
        sexp: &crate::syntax::SExp,
        reference_var: &[Var],
    ) -> Result<Exp, String> {
        self.elab_exp_rec(logger, sexp, reference_var, vec![])
    }
    fn elab_telescope(
        &mut self,
        logger: &mut Logger,
        telescope: &Vec<RightBind>,
    ) -> Result<Vec<(Var, Exp)>, String> {
        let mut result = vec![];
        let mut reference_var = vec![];
        for RightBind { vars, ty } in telescope {
            let ty_elab = self.elab_exp_rec(logger, ty, &reference_var, vec![])?;
            for var in vars {
                let var: Var = var.into();
                result.push((var.clone(), ty_elab.clone()));
                reference_var.push(var);
            }
        }
        Ok(result)
    }
    fn elab_exp_rec(
        &mut self,
        logger: &mut Logger,
        sexp: &crate::syntax::SExp,
        reference_var: &[Var],
        bind_var: Vec<Var>,
    ) -> Result<Exp, String> {
        match sexp {
            SExp::AccessPath(path) => {
                // parameters.len() > 0 <=> AccessPath::WithParams
                let (idents, parameters) = match path {
                    AccessPath::Plain { segments } => (segments, vec![]),
                    AccessPath::WithParams {
                        segments,
                        parameters,
                    } => (segments, parameters.clone()),
                };

                let parameters_elab = parameters
                    .iter()
                    .map(|p| self.elab_exp_rec(logger, p, reference_var, bind_var.clone()))
                    .collect::<Result<Vec<_>, String>>()?;

                // case: len == 1 && parameters.is_empty() && in bind_var or reference_var or module's parameter => Var
                if let [ident] = &idents[..]
                    && parameters.is_empty()
                {
                    // case: binded in expression
                    for v in bind_var.iter().rev() {
                        if v.as_str() == ident.0.as_str() {
                            return Ok(Exp::Var(v.clone()));
                        }
                    }
                    // case: binded in reference_var
                    for v in reference_var.iter().rev() {
                        if v.as_str() == ident.0.as_str() {
                            return Ok(Exp::Var(v.clone()));
                        }
                    }
                    // case: module parameter
                    for (v, _) in self.parameters.iter().rev() {
                        if v.as_str() == ident.0.as_str() {
                            return Ok(Exp::Var(v.clone()));
                        }
                    }
                }

                // otherwise ... get item from path
                let Some(item) = self.get_item_from_path(idents) else {
                    return Err(format!(
                        "Unbound identifier for item: {}",
                        idents
                            .iter()
                            .map(|id| id.0.as_str())
                            .collect::<Vec<_>>()
                            .join(".")
                    ));
                };

                match item {
                    Either::Left(body) => {
                        // definition case ... if parameters exists => Error
                        if !parameters.is_empty() {
                            return Err(format!(
                                "Definition {} does not take parameters",
                                idents
                                    .iter()
                                    .map(|id| id.0.as_str())
                                    .collect::<Vec<_>>()
                                    .join(".")
                            ));
                        }
                        Ok(body)
                    }
                    Either::Right((indspec, None)) => Ok(Exp::IndType {
                        indspec,
                        parameters: parameters_elab,
                    }),
                    Either::Right((indspec, Some(idx))) => Ok(Exp::IndCtor {
                        indspec,
                        idx,
                        parameters: parameters_elab,
                    }),
                }
            }
            SExp::MathMacro { .. } | SExp::NamedMacro { .. } => {
                todo!("macro elaboration not implemented")
            }
            SExp::Where { exp, clauses } => {
                let mut bind_var = bind_var.clone();
                let mut clauses_elab = vec![];
                for (v, ty, body) in clauses {
                    let v: Var = v.into();
                    bind_var.push(v.clone());
                    let ty_elab = self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                    let body_elab =
                        self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;
                    clauses_elab.push((v, ty_elab, body_elab));
                }
                let mut exp_elab =
                    self.elab_exp_rec(logger, exp, reference_var, bind_var.clone())?;
                for (v, ty, body) in clauses_elab {
                    exp_elab = Exp::App {
                        func: Box::new(Exp::Lam {
                            var: v,
                            ty: Box::new(ty),
                            body: Box::new(exp_elab),
                        }),
                        arg: Box::new(body),
                    }
                }
                Ok(exp_elab)
            }
            SExp::WithProofs { exp, proofs } => {
                let exp_elab = self.elab_exp_rec(logger, exp, reference_var, bind_var.clone())?;
                let mut proof_goals: Vec<ProveGoal> = vec![];
                for proof in proofs {
                    let GoalProof {
                        extended_ctx,
                        goal,
                        proofby: proof_term,
                    } = proof;
                    let mut bind_var = bind_var.clone();
                    let extended_ctx_elab = self.elab_telescope(logger, extended_ctx)?;
                    for (v, _) in extended_ctx_elab.iter() {
                        bind_var.push(v.clone());
                    }
                    let goal_elab =
                        self.elab_exp_rec(logger, goal, reference_var, bind_var.clone())?;
                    let proof_term_elab =
                        self.elab_proof_by(logger, proof_term, reference_var, bind_var.clone())?;
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
                    // A -> B ... (_: A) -> B
                    // A => B ... (_: A) => B
                    Bind::Anonymous { ty } => {
                        let ty_elab =
                            self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                        let body_elab =
                            self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;
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
                    // (x[0], ..., x[n]: A) -> B ... (x[0]: A) -> ... -> (x[n]: A) -> B
                    // (x[0], ..., x[n]: A) => B ... (x[0]: A) => ... => (x[n]: A) => B
                    Bind::Named(RightBind { vars, ty }) => {
                        let ty_elab =
                            self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;

                        let mut telescope: Vec<(Var, Exp)> = vec![];
                        let mut bind_var = bind_var.clone();

                        for var in vars {
                            let var: Var = var.into();
                            telescope.push((var.clone(), ty_elab.clone()));
                            bind_var.push(var);
                        }

                        let body_elab =
                            self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;

                        Ok(if is_prod {
                            kernel::utils::assoc_prod(telescope, body_elab)
                        } else {
                            kernel::utils::assoc_lam(telescope, body_elab)
                        })
                    }
                    // (x: A | P) -> B ... (x: Lift(A, {x: A | P})) -> B
                    // (x: A | P) => B ... (x: Lift(A, {x: A | P})) => B
                    Bind::Subset { var, ty, predicate } => {
                        let ty_elab =
                            self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                        let var: Var = var.into();
                        let mut bind_var = bind_var.clone();
                        bind_var.push(var.clone());
                        let predicate_elab =
                            self.elab_exp_rec(logger, predicate, reference_var, bind_var.clone())?;
                        let body_elab =
                            self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;

                        let subset = Exp::SubSet {
                            var: var.clone(),
                            set: Box::new(ty_elab.clone()),
                            predicate: Box::new(predicate_elab.clone()),
                        };

                        Ok(if is_prod {
                            Exp::Prod {
                                var: var.clone(),
                                ty: Box::new(Exp::TypeLift {
                                    superset: Box::new(ty_elab.clone()),
                                    subset: Box::new(subset),
                                }),
                                body: Box::new(body_elab),
                            }
                        } else {
                            Exp::Lam {
                                var: var.clone(),
                                ty: Box::new(Exp::TypeLift {
                                    superset: Box::new(ty_elab.clone()),
                                    subset: Box::new(subset),
                                }),
                                body: Box::new(body_elab),
                            }
                        })
                    }
                    // (x: A | h: P) -> B ... (x: Lift(A, {x: A | P})) -> (h: P) -> B
                    // (x: A | h: P) => B ... (x: Lift(A, {x: A | P})) => (h: P) => B
                    Bind::SubsetWithProof {
                        var,
                        ty,
                        predicate,
                        proof_var: proof,
                    } => {
                        let ty_elab =
                            self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                        let var: Var = var.into();
                        let mut bind_var = bind_var.clone();
                        bind_var.push(var.clone());
                        let predicate_elab =
                            self.elab_exp_rec(logger, predicate, reference_var, bind_var.clone())?;
                        let proof: Var = proof.into();
                        bind_var.push(proof.clone());
                        let body_elab =
                            self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;
                        let subset = Exp::SubSet {
                            var: var.clone(),
                            set: Box::new(ty_elab.clone()),
                            predicate: Box::new(predicate_elab.clone()),
                        };

                        Ok(if is_prod {
                            Exp::Prod {
                                var: var.clone(),
                                ty: Box::new(Exp::TypeLift {
                                    superset: Box::new(ty_elab.clone()),
                                    subset: Box::new(subset),
                                }),
                                body: Box::new(Exp::Prod {
                                    var: proof,
                                    ty: Box::new(predicate_elab),
                                    body: Box::new(body_elab),
                                }),
                            }
                        } else {
                            Exp::Lam {
                                var: var.clone(),
                                ty: Box::new(Exp::TypeLift {
                                    superset: Box::new(ty_elab.clone()),
                                    subset: Box::new(subset),
                                }),
                                body: Box::new(Exp::Lam {
                                    var: proof,
                                    ty: Box::new(predicate_elab),
                                    body: Box::new(body_elab),
                                }),
                            }
                        })
                    }
                }
            }
            SExp::Cast { exp, to } => {
                let exp_elab = self.elab_exp_rec(logger, exp, reference_var, bind_var.clone())?;
                let to_elab = self.elab_exp_rec(logger, to, reference_var, bind_var.clone())?;
                Ok(Exp::Cast {
                    exp: Box::new(exp_elab),
                    to: Box::new(to_elab),
                })
            }
            SExp::App {
                func,
                arg,
                piped: _,
            } => {
                let func_elab = self.elab_exp_rec(logger, func, reference_var, bind_var.clone())?;
                let arg_elab = self.elab_exp_rec(logger, arg, reference_var, bind_var.clone())?;
                Ok(Exp::App {
                    func: Box::new(func_elab),
                    arg: Box::new(arg_elab),
                })
            }
            SExp::IndElim {
                path,
                elim,
                return_type,
                cases,
            } => {
                let (idents, parameters) = match path {
                    AccessPath::Plain { segments } => (segments, vec![]),
                    AccessPath::WithParams {
                        segments,
                        parameters,
                    } => (segments, parameters.clone()),
                };

                if !parameters.is_empty() {
                    return Err(format!(
                        "Inductive type {:?} elimination does not take parameters",
                        path
                    ));
                }

                let item = self.get_item_from_path(idents).ok_or(format!(
                    "Inductive type {:?} not found for elimination",
                    path
                ))?;

                let Either::Right((ind_defs, None)) = item else {
                    return Err(format!(
                        "Item {:?} is not an inductive type for elimination",
                        path
                    ));
                };

                let eliminated_exp_elab =
                    self.elab_exp_rec(logger, elim, reference_var, bind_var.clone())?;
                let return_type_elab =
                    self.elab_exp_rec(logger, return_type, reference_var, bind_var.clone())?;
                let mut cases_elab = vec![];
                for (ctor_name, case_exp) in cases {
                    let ctor_idx =
                        ind_defs
                            .ctor_idx_from_name(ctor_name.as_str())
                            .ok_or(format!(
                                "Constructor name {} not found in inductive type {}",
                                ctor_name.as_str(),
                                ind_defs.names.0
                            ))?;
                    let case_exp_elab =
                        self.elab_exp_rec(logger, case_exp, reference_var, bind_var.clone())?;
                    cases_elab.push((ctor_idx, case_exp_elab));
                }

                cases_elab.sort_by_key(|(idx, _)| *idx);

                let cases_elab = cases_elab
                    .into_iter()
                    .map(|(_, case_exp)| case_exp)
                    .collect::<Vec<Exp>>();

                Ok(Exp::IndElim {
                    indspec: ind_defs,
                    elim: Box::new(eliminated_exp_elab),
                    return_type: Box::new(return_type_elab),
                    cases: cases_elab,
                })
            }
            SExp::IndElimPrim { path, sort } => {
                let (idents, parameters) = match path {
                    AccessPath::Plain { segments } => (segments, vec![]),
                    AccessPath::WithParams {
                        segments,
                        parameters,
                    } => (segments, parameters.clone()),
                };

                let item = self.get_item_from_path(idents).ok_or(format!(
                    "Inductive type {:?} not found for primitive elimination",
                    idents
                ))?;
                let Either::Right((indspec, None)) = item else {
                    return Err(format!(
                        "Item {:?} is not an inductive type for primitive elimination",
                        idents
                    ));
                };

                let parameters_elab = parameters
                    .iter()
                    .map(|p| self.elab_exp_rec(logger, p, reference_var, bind_var.clone()))
                    .collect::<Result<Vec<_>, String>>()?;
                Ok(kernel::inductive::InductiveTypeSpecs::primitive_recursion(
                    &indspec,
                    parameters_elab,
                    *sort,
                ))
            }
            SExp::ProveLater { term } => {
                let term_elab = self.elab_exp_rec(logger, term, reference_var, bind_var.clone())?;
                Ok(Exp::ProveLater {
                    prop: Box::new(term_elab),
                })
            }
            SExp::PowerSet { set } => {
                let power_elab = self.elab_exp_rec(logger, set, reference_var, bind_var.clone())?;
                Ok(Exp::PowerSet {
                    set: Box::new(power_elab),
                })
            }
            SExp::SubSet {
                var,
                set,
                predicate,
            } => {
                let set_elab = self.elab_exp_rec(logger, set, reference_var, bind_var.clone())?;
                let var: Var = var.into();
                let mut bind_var = bind_var.clone();
                bind_var.push(var.clone());
                let predicate_elab =
                    self.elab_exp_rec(logger, predicate, reference_var, bind_var.clone())?;
                Ok(Exp::SubSet {
                    var,
                    set: Box::new(set_elab),
                    predicate: Box::new(predicate_elab),
                })
            }
            SExp::Pred {
                superset,
                subset,
                element,
            } => {
                let superset_elab =
                    self.elab_exp_rec(logger, superset, reference_var, bind_var.clone())?;
                let subset_elab =
                    self.elab_exp_rec(logger, subset, reference_var, bind_var.clone())?;
                let elem_elab =
                    self.elab_exp_rec(logger, element, reference_var, bind_var.clone())?;
                Ok(Exp::Pred {
                    superset: Box::new(superset_elab),
                    subset: Box::new(subset_elab),
                    element: Box::new(elem_elab),
                })
            }
            SExp::TypeLift { superset, subset } => {
                let superset_elab =
                    self.elab_exp_rec(logger, superset, reference_var, bind_var.clone())?;
                let subset_elab =
                    self.elab_exp_rec(logger, subset, reference_var, bind_var.clone())?;
                Ok(Exp::TypeLift {
                    superset: Box::new(superset_elab),
                    subset: Box::new(subset_elab),
                })
            }
            SExp::Equal { left, right } => {
                let left_elab = self.elab_exp_rec(logger, left, reference_var, bind_var.clone())?;
                let right_elab =
                    self.elab_exp_rec(logger, right, reference_var, bind_var.clone())?;
                Ok(Exp::Equal {
                    left: Box::new(left_elab),
                    right: Box::new(right_elab),
                })
            }
            // this is non emptyness of type
            SExp::Exists { bind } => {
                let result = match bind {
                    // \exists A ... \exists A
                    Bind::Anonymous { ty } => {
                        let ty_elab =
                            self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                        Exp::Exists {
                            set: Box::new(ty_elab),
                        }
                    }
                    // \exists x: A ... same as Anonymous
                    Bind::Named(RightBind { vars: _, ty }) => {
                        // may be we should warning?
                        let ty_elab =
                            self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                        Exp::Exists {
                            set: Box::new(ty_elab),
                        }
                    }
                    // \exists (x: A | P) ... \exists Lift(A, {x: A | P})
                    Bind::Subset { var, ty, predicate } => {
                        let ty_elab =
                            self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                        let var: Var = var.into();
                        let mut bind_var = bind_var.clone();
                        bind_var.push(var.clone());
                        let predicate_elab =
                            self.elab_exp_rec(logger, predicate, reference_var, bind_var.clone())?;

                        let subset = Exp::SubSet {
                            var: var.clone(),
                            set: Box::new(ty_elab.clone()),
                            predicate: Box::new(predicate_elab.clone()),
                        };

                        Exp::Exists {
                            set: Box::new(Exp::TypeLift {
                                superset: Box::new(ty_elab.clone()),
                                subset: Box::new(subset),
                            }),
                        }
                    }
                    // \exists (x: A | h: P) ... invalid
                    Bind::SubsetWithProof { .. } => {
                        return Err(
                            "Invalid binding in Exists: only Anonymous and Named are allowed"
                                .to_string(),
                        );
                    }
                };
                Ok(result)
            }
            SExp::Take { bind, body } => {
                let map = match bind {
                    Bind::Anonymous { ty } => {
                        let ty_elab =
                            self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                        let body_elab =
                            self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;
                        Exp::Prod {
                            var: Var::dummy(),
                            ty: Box::new(ty_elab),
                            body: Box::new(body_elab),
                        }
                    }
                    // \take (x[0], ..., x[n]: A) => body ... \take x[0]: A => ... => \take (x[n]: A) => body
                    Bind::Named(RightBind { vars, ty }) => {
                        let ty_elab =
                            self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                        let mut telescope: Vec<(Var, Exp)> = vec![];
                        let mut bind_var = bind_var.clone();
                        for var in vars {
                            let var: Var = var.into();
                            telescope.push((var.clone(), ty_elab.clone()));
                            bind_var.push(var);
                        }
                        let mut body_elab =
                            self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;

                        while let Some((var, ty)) = telescope.pop() {
                            let map = Exp::Prod {
                                var: var.clone(),
                                ty: Box::new(ty),
                                body: Box::new(body_elab),
                            };
                            body_elab = Exp::Take { map: Box::new(map) };
                        }

                        // EARLY RETURN
                        return Ok(body_elab);
                    }
                    Bind::Subset { var, ty, predicate } => {
                        let ty_elab =
                            self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                        let var: Var = var.into();
                        let mut bind_var = bind_var.clone();
                        bind_var.push(var.clone());
                        let predicate_elab =
                            self.elab_exp_rec(logger, predicate, reference_var, bind_var.clone())?;
                        let body_elab =
                            self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;

                        let subset = Exp::SubSet {
                            var: var.clone(),
                            set: Box::new(ty_elab.clone()),
                            predicate: Box::new(predicate_elab.clone()),
                        };

                        Exp::Prod {
                            var: var.clone(),
                            ty: Box::new(Exp::TypeLift {
                                superset: Box::new(ty_elab.clone()),
                                subset: Box::new(subset),
                            }),
                            body: Box::new(body_elab),
                        }
                    }
                    Bind::SubsetWithProof {
                        var,
                        ty,
                        predicate,
                        proof_var: proof,
                    } => {
                        let ty_elab =
                            self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                        let var: Var = var.into();
                        let mut bind_var = bind_var.clone();
                        bind_var.push(var.clone());
                        let predicate_elab =
                            self.elab_exp_rec(logger, predicate, reference_var, bind_var.clone())?;
                        let proof: Var = proof.into();
                        bind_var.push(proof.clone());
                        let body_elab =
                            self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;
                        let subset = Exp::SubSet {
                            var: var.clone(),
                            set: Box::new(ty_elab.clone()),
                            predicate: Box::new(predicate_elab.clone()),
                        };

                        Exp::Prod {
                            var: var.clone(),
                            ty: Box::new(Exp::TypeLift {
                                superset: Box::new(ty_elab.clone()),
                                subset: Box::new(subset),
                            }),
                            body: Box::new(Exp::Prod {
                                var: proof,
                                ty: Box::new(predicate_elab),
                                body: Box::new(body_elab),
                            }),
                        }
                    }
                };
                Ok(Exp::Take { map: Box::new(map) })
            }
            SExp::ProofBy(proof_by) => {
                use ProveCommandBy;
                let command: ProveCommandBy =
                    self.elab_proof_by(logger, proof_by, reference_var, bind_var.clone())?;

                Ok(Exp::ProofTermRaw {
                    command: Box::new(command),
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
                self.elab_exp_rec(logger, &term, reference_var, bind_var.clone())
            }
        }
    }

    fn elab_proof_by(
        &mut self,
        logger: &mut Logger,
        proof_by: &crate::syntax::ProofBy,
        reference_var: &[Var],
        bind_var: Vec<Var>,
    ) -> Result<ProveCommandBy, String> {
        use ProveCommandBy;
        let elab = match proof_by {
            ProofBy::Construct { term } => {
                let term_elab = self.elab_exp_rec(logger, term, reference_var, bind_var.clone())?;
                ProveCommandBy::Construct(term_elab)
            }
            ProofBy::Exact { term, set } => {
                let term_elab = self.elab_exp_rec(logger, term, reference_var, bind_var.clone())?;
                let set_elab = self.elab_exp_rec(logger, set, reference_var, bind_var.clone())?;
                ProveCommandBy::ExactElem {
                    elem: term_elab,
                    ty: set_elab,
                }
            }
            ProofBy::SubsetElim {
                superset,
                subset,
                elem,
            } => {
                let superset_elab =
                    self.elab_exp_rec(logger, superset, reference_var, bind_var.clone())?;
                let subset_elab =
                    self.elab_exp_rec(logger, subset, reference_var, bind_var.clone())?;
                let elem_elab = self.elab_exp_rec(logger, elem, reference_var, bind_var.clone())?;
                ProveCommandBy::SubsetElim {
                    superset: superset_elab,
                    subset: subset_elab,
                    elem: elem_elab,
                }
            }
            ProofBy::IdRefl { term } => {
                let term_elab = self.elab_exp_rec(logger, term, reference_var, bind_var.clone())?;
                ProveCommandBy::IdRefl { elem: term_elab }
            }
            ProofBy::IdElim {
                left,
                right,
                var,
                ty,
                predicate,
            } => {
                let left_elab = self.elab_exp_rec(logger, left, reference_var, bind_var.clone())?;
                let right_elab =
                    self.elab_exp_rec(logger, right, reference_var, bind_var.clone())?;
                let var: Var = var.into();
                let mut bind_var = bind_var.clone();
                bind_var.push(var.clone());
                let ty_elab = self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                let predicate_elab =
                    self.elab_exp_rec(logger, predicate, reference_var, bind_var.clone())?;
                ProveCommandBy::IdElim {
                    left: left_elab,
                    right: right_elab,
                    var,
                    ty: ty_elab,
                    predicate: predicate_elab,
                }
            }
            ProofBy::TakeEq {
                func,
                domain,
                codomain,
                elem,
            } => {
                let func_elab = self.elab_exp_rec(logger, func, reference_var, bind_var.clone())?;
                let domain_elab =
                    self.elab_exp_rec(logger, domain, reference_var, bind_var.clone())?;
                let codomain_elab =
                    self.elab_exp_rec(logger, codomain, reference_var, bind_var.clone())?;
                let elem_elab = self.elab_exp_rec(logger, elem, reference_var, bind_var.clone())?;
                ProveCommandBy::TakeEq {
                    func: func_elab,
                    domain: domain_elab,
                    codomain: codomain_elab,
                    elem: elem_elab,
                }
            }
            ProofBy::Axiom(_) => {
                todo!()
            }
        };
        Ok(elab)
    }
}

// for templates
#[derive(Debug, Clone)]
pub struct ModuleResolved {
    pub name: Var,
    pub parameters: Vec<(Var, Exp)>, // v: ty
    pub items: Vec<Item>,
}

impl ModuleResolved {
    fn realize(&self, args: Vec<Exp>) -> ModuleRealized {
        // we need to subst variables in items
        let subst_map: Vec<(Var, Exp)> = self
            .parameters
            .iter()
            .map(|(v, _)| v.clone())
            .zip(args)
            .collect();
        let mut realized_items = vec![];
        for item in self.items.iter() {
            realized_items.push(item.subst(&subst_map));
        }
        ModuleRealized {
            name: self.name.clone(),
            arguments: subst_map.into_iter().map(|(_, e)| e).collect(),
            items: realized_items,
        }
    }
}

pub struct ModuleRealized {
    pub name: Var,
    pub arguments: Vec<Exp>, // v := arg
    pub items: Vec<Item>,
}
